`timescale 1ns / 1ps

module mixed_radix_240_1d (
    input  wire               clk,
    input  wire               rst_n,
    input  wire               start,
    input  wire               inv_en,
    input  wire               in_valid,
    input  wire signed [31:0] in_re,
    input  wire signed [31:0] in_im,
    output reg                out_valid,
    output reg         [7:0]  out_idx,
    output reg  signed [31:0] out_re,
    output reg  signed [31:0] out_im,
    output reg                done
);

    // FSM 状態定義
    localparam S_IDLE      = 3'd0;
    localparam S_LOAD      = 3'd1;
    localparam S_S1_LOAD   = 3'd2;
    localparam S_S1_BF     = 3'd3;
    localparam S_S1_TW     = 3'd4;
    localparam S_S2_DFT3   = 3'd5;
    localparam S_S2_TW15   = 3'd6;
    localparam S_S3_DFT5   = 3'd7;

    reg [2:0] state;
    reg       done_wait_mode;
    reg [3:0] wait_cnt;
    reg       inv_reg;

    // 各種ループカウンタ
    reg [7:0] in_cnt;
    reg [3:0] n1;        // 0..15
    reg [3:0] n2;        // 0..14
    reg [1:0] s_stage;   // 0..3 (16点FFTステージ)
    reg [2:0] bf_idx;    // 0..7 (バタフライ番号)
    reg [3:0] k1;        // 0..15
    reg [1:0] l1;        // 0..2
    reg [2:0] l2;        // 0..4
    reg [1:0] m1;        // 0..2
    reg [2:0] m2;        // 0..4
    reg [1:0] sub_step;  // 0..3 (各演算のサイクル制御)

    // 16点小バッファ (レジスタ配列)
    reg signed [23:0] tmp16_re [0:15];
    reg signed [23:0] tmp16_im [0:15];

    // 累算レジスタ (3点DFT / 5点DFT用)
    reg signed [23:0] acc_re, acc_im;

    // -------------------------------------------------------------------------
    // インデックス・アドレス計算用ヘルパー
    // -------------------------------------------------------------------------
    function [3:0] rev4;
        input [3:0] v;
        begin
            rev4 = {v[0], v[1], v[2], v[3]};
        end
    endfunction

    // 16点FFTのバタフライ対象インデックスと回転因子インデックス
    reg [3:0] bf_idx_e, bf_idx_o;
    reg [7:0] bf_w_idx;
    always @(*) begin
        case (s_stage)
            2'd0: begin
                bf_idx_e = {bf_idx, 1'b0};
                bf_idx_o = {bf_idx, 1'b1};
                bf_w_idx = 8'd0;
            end
            2'd1: begin
                bf_idx_e = {bf_idx[2:1], 1'b0, bf_idx[0]};
                bf_idx_o = {bf_idx[2:1], 1'b1, bf_idx[0]};
                bf_w_idx = bf_idx[0] ? 8'd60 : 8'd0; // k*4*15
            end
            2'd2: begin
                bf_idx_e = {bf_idx[2], 1'b0, bf_idx[1:0]};
                bf_idx_o = {bf_idx[2], 1'b1, bf_idx[1:0]};
                bf_w_idx = {4'd0, bf_idx[1:0], 2'd0} * 8'd7 + {5'd0, bf_idx[1:0], 1'b0}; // k*30
            end
            default: begin // 2'd3
                bf_idx_e = {1'b0, bf_idx};
                bf_idx_o = {1'b1, bf_idx};
                bf_w_idx = ({4'd0, bf_idx} << 4) - {5'd0, bf_idx}; // k*15
            end
        endcase
    end

    // 3点DFT用 W3 インデックス: ((m1 * l1) % 3) * 80
    reg [7:0] w3_idx;
    always @(*) begin
        if (m1 == 2'd0 || l1 == 2'd0)
            w3_idx = 8'd0;
        else if (m1 == l1)
            w3_idx = 8'd80;
        else
            w3_idx = 8'd160;
    end

    // 5点DFT用 W5 インデックス: ((m2 * l2) % 5) * 48
    wire [4:0] m2_x_l2 = m2 * l2;
    wire [2:0] m2l2_mod5 = (m2_x_l2 >= 5'd15) ? (m2_x_l2 - 5'd15) :
                           (m2_x_l2 >= 5'd10) ? (m2_x_l2 - 5'd10) :
                           (m2_x_l2 >= 5'd5)  ? (m2_x_l2 - 5'd5)  : m2_x_l2[2:0];
    wire [7:0] w5_idx = ({5'd0, m2l2_mod5} << 5) + ({5'd0, m2l2_mod5} << 4); // * 48

    // RAM アドレス計算 (乗算器不使用)
    wire [7:0] addr_15n1_n2    = ({4'd0, n1} << 4) - {4'd0, n1} + {4'd0, n2};
    wire [7:0] addr_15k1_n2    = ({4'd0, k1} << 4) - {4'd0, k1} + {4'd0, n2};
    wire [7:0] addr_15k1_5m1m2 = ({4'd0, k1} << 4) - {4'd0, k1} + ({6'd0, m1} << 2) + {6'd0, m1} + {5'd0, m2};
    wire [7:0] addr_15k1_5l1m2 = ({4'd0, k1} << 4) - {4'd0, k1} + ({6'd0, l1} << 2) + {6'd0, l1} + {5'd0, m2};
    wire [7:0] addr_out_k      = {4'd0, k1} + ({6'd0, l1} << 4) + ({5'd0, l2} << 5) + ({5'd0, l2} << 4);

    // -------------------------------------------------------------------------
    // 単一ROM (W_240) & ピンポンRAM (ram_a / ram_b)
    // -------------------------------------------------------------------------
    reg [7:0] rom_addr;
    always @(*) begin
        case (state)
            S_S1_BF:   rom_addr = bf_w_idx;
            S_S1_TW:   rom_addr = n2 * k1;
            S_S2_DFT3: rom_addr = w3_idx;
            S_S2_TW15: rom_addr = ({4'd0, m2} * {6'd0, l1}) << 4; // m2 * l1 * 16
            S_S3_DFT5: rom_addr = w5_idx;
            default:   rom_addr = 8'd0;
        endcase
    end

    wire signed [15:0] rom_re_raw, rom_im_raw;
    rom_W240 u_rom_w240 (
        .clk  (clk),
        .addr (rom_addr),
        .re   (rom_re_raw),
        .im   (rom_im_raw)
    );
    wire signed [15:0] rom_re = rom_re_raw;
    wire signed [15:0] rom_im = inv_reg ? -rom_im_raw : rom_im_raw;

    reg                ram_a_we;
    reg         [7:0]  ram_a_addr;
    reg  signed [23:0] ram_a_din_re, ram_a_din_im;
    wire signed [23:0] ram_a_dout_re, ram_a_dout_im;

    work_ram_240 u_ram_a (
        .clk     (clk),
        .we      (ram_a_we),
        .addr    (ram_a_addr),
        .din_re  (ram_a_din_re),
        .din_im  (ram_a_din_im),
        .dout_re (ram_a_dout_re),
        .dout_im (ram_a_dout_im)
    );

    reg                ram_b_we;
    reg         [7:0]  ram_b_addr;
    reg  signed [23:0] ram_b_din_re, ram_b_din_im;
    wire signed [23:0] ram_b_dout_re, ram_b_dout_im;

    work_ram_240 u_ram_b (
        .clk     (clk),
        .we      (ram_b_we),
        .addr    (ram_b_addr),
        .din_re  (ram_b_din_re),
        .din_im  (ram_b_din_im),
        .dout_re (ram_b_dout_re),
        .dout_im (ram_b_dout_im)
    );

    // -------------------------------------------------------------------------
    // 共有 2段パイプライン複素乗算器 (24bit x 16bit -> DSP48E1 x 4個)
    // -------------------------------------------------------------------------
    reg  signed [23:0] cmul_a_re, cmul_a_im;
    reg  signed [15:0] cmul_b_re, cmul_b_im;
    reg  signed [39:0] m_rr, m_ii, m_ri, m_ir;
    reg  signed [23:0] cmul_re, cmul_im;

    wire signed [40:0] cmul_sum_re = (m_rr - m_ii + 41'sd8192) >>> 14;
    wire signed [40:0] cmul_sum_im = (m_ri + m_ir + 41'sd8192) >>> 14;

    always @(*) begin
        case (state)
            S_S1_BF: begin
                cmul_a_re = tmp16_re[bf_idx_o];
                cmul_a_im = tmp16_im[bf_idx_o];
            end
            S_S1_TW: begin
                cmul_a_re = tmp16_re[k1];
                cmul_a_im = tmp16_im[k1];
            end
            S_S2_DFT3: begin
                cmul_a_re = ram_b_dout_re;
                cmul_a_im = ram_b_dout_im;
            end
            S_S2_TW15: begin
                cmul_a_re = acc_re;
                cmul_a_im = acc_im;
            end
            S_S3_DFT5: begin
                cmul_a_re = ram_a_dout_re;
                cmul_a_im = ram_a_dout_im;
            end
            default: begin
                cmul_a_re = 24'sd0;
                cmul_a_im = 24'sd0;
            end
        endcase
        cmul_b_re = rom_re;
        cmul_b_im = rom_im;
    end

    always @(posedge clk) begin
        // Stage 1: 乗算
        m_rr <= cmul_a_re * cmul_b_re;
        m_ii <= cmul_a_im * cmul_b_im;
        m_ri <= cmul_a_re * cmul_b_im;
        m_ir <= cmul_a_im * cmul_b_re;
        // Stage 2: 加減算 + 四捨五入右シフト(14bit)
        cmul_re <= cmul_sum_re[23:0];
        cmul_im <= cmul_sum_im[23:0];
    end

    // バタフライ加減算 & 1bit右シフト (四捨五入)
    wire signed [24:0] bf_sum_re  = ({tmp16_re[bf_idx_e][23], tmp16_re[bf_idx_e]} + {cmul_re[23], cmul_re} + 25'sd1) >>> 1;
    wire signed [24:0] bf_sum_im  = ({tmp16_im[bf_idx_e][23], tmp16_im[bf_idx_e]} + {cmul_im[23], cmul_im} + 25'sd1) >>> 1;
    wire signed [24:0] bf_diff_re = ({tmp16_re[bf_idx_e][23], tmp16_re[bf_idx_e]} - {cmul_re[23], cmul_re} + 25'sd1) >>> 1;
    wire signed [24:0] bf_diff_im = ({tmp16_im[bf_idx_e][23], tmp16_im[bf_idx_e]} - {cmul_im[23], cmul_im} + 25'sd1) >>> 1;

    // 5点DFT最終和
    wire signed [23:0] dft5_final_re = acc_re + cmul_re;
    wire signed [23:0] dft5_final_im = acc_im + cmul_im;

    // -------------------------------------------------------------------------
    // RAM 制御信号のマルチプレクサ
    // -------------------------------------------------------------------------
    always @(*) begin
        ram_a_we     = 1'b0;
        ram_a_addr   = 8'd0;
        ram_a_din_re = 24'sd0;
        ram_a_din_im = 24'sd0;

        ram_b_we     = 1'b0;
        ram_b_addr   = 8'd0;
        ram_b_din_re = 24'sd0;
        ram_b_din_im = 24'sd0;

        case (state)
            S_LOAD: begin
                ram_a_we     = in_valid;
                ram_a_addr   = in_cnt;
                ram_a_din_re = in_re[23:0];
                ram_a_din_im = in_im[23:0];
            end
            S_S1_LOAD: begin
                ram_a_addr   = addr_15n1_n2;
            end
            S_S1_TW: begin
                ram_b_we     = (sub_step == 2'd3);
                ram_b_addr   = addr_15k1_n2;
                ram_b_din_re = cmul_re;
                ram_b_din_im = cmul_im;
            end
            S_S2_DFT3: begin
                ram_b_addr   = addr_15k1_5m1m2;
            end
            S_S2_TW15: begin
                ram_a_we     = (sub_step == 2'd3);
                ram_a_addr   = addr_15k1_5l1m2;
                ram_a_din_re = cmul_re;
                ram_a_din_im = cmul_im;
            end
            S_S3_DFT5: begin
                ram_a_addr   = addr_15k1_5l1m2;
            end
            default: ;
        endcase
    end

    // -------------------------------------------------------------------------
    // メイン FSM
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (!rst_n) begin
            state          <= S_IDLE;
            done_wait_mode <= 1'b0;
            wait_cnt       <= 4'd0;
            inv_reg        <= 1'b0;
            in_cnt         <= 8'd0;
            n1             <= 4'd0;
            n2             <= 4'd0;
            s_stage        <= 2'd0;
            bf_idx         <= 3'd0;
            k1             <= 4'd0;
            l1             <= 2'd0;
            l2             <= 3'd0;
            m1             <= 2'd0;
            m2             <= 3'd0;
            sub_step       <= 2'd0;
            acc_re         <= 24'sd0;
            acc_im         <= 24'sd0;
            out_valid      <= 1'b0;
            out_idx        <= 8'd0;
            out_re         <= 32'sd0;
            out_im         <= 32'sd0;
            done           <= 1'b0;
        end else begin
            out_valid <= 1'b0;
            done      <= 1'b0;

            if (done_wait_mode) begin
                // Pass 2の5段パイプライン完了を待つため8サイクル遅延後にdoneを出力
                if (wait_cnt == 4'd7) begin
                    done           <= 1'b1;
                    done_wait_mode <= 1'b0;
                    state          <= S_IDLE;
                end else begin
                    wait_cnt <= wait_cnt + 4'd1;
                end
            end else begin
                case (state)
                    S_IDLE: begin
                        if (start) begin
                            inv_reg <= inv_en;
                            in_cnt  <= 8'd0;
                            state   <= S_LOAD;
                        end
                    end

                    S_LOAD: begin
                        if (in_valid) begin
                            if (in_cnt == 8'd239) begin
                                n1       <= 4'd0;
                                n2       <= 4'd0;
                                sub_step <= 2'd0;
                                state    <= S_S1_LOAD;
                            end else begin
                                in_cnt <= in_cnt + 8'd1;
                            end
                        end
                    end

                    // Stage 1a: ram_a から16点をビットリバーサル順で tmp16 へロード
                    S_S1_LOAD: begin
                        if (sub_step == 2'd0) begin
                            sub_step <= 2'd1;
                        end else begin
                            tmp16_re[rev4(n1)] <= ram_a_dout_re;
                            tmp16_im[rev4(n1)] <= ram_a_dout_im;
                            sub_step <= 2'd0;
                            if (n1 == 4'd15) begin
                                s_stage <= 2'd0;
                                bf_idx  <= 3'd0;
                                state   <= S_S1_BF;
                            end else begin
                                n1 <= n1 + 4'd1;
                            end
                        end
                    end

                    // Stage 1b: 16点 Radix-2 FFT (4ステージ x 8バタフライ)
                    S_S1_BF: begin
                        if (sub_step < 2'd3) begin
                            sub_step <= sub_step + 2'd1;
                        end else begin
                            tmp16_re[bf_idx_e] <= bf_sum_re[23:0];
                            tmp16_im[bf_idx_e] <= bf_sum_im[23:0];
                            tmp16_re[bf_idx_o] <= bf_diff_re[23:0];
                            tmp16_im[bf_idx_o] <= bf_diff_im[23:0];
                            sub_step <= 2'd0;

                            if (bf_idx == 3'd7) begin
                                bf_idx <= 3'd0;
                                if (s_stage == 2'd3) begin
                                    k1    <= 4'd0;
                                    state <= S_S1_TW;
                                end else begin
                                    s_stage <= s_stage + 2'd1;
                                end
                            end else begin
                                bf_idx <= bf_idx + 3'd1;
                            end
                        end
                    end

                    // Stage 1c: Twiddle W_240 乗算 -> ram_b 書き込み
                    S_S1_TW: begin
                        if (sub_step < 2'd3) begin
                            sub_step <= sub_step + 2'd1;
                        end else begin
                            sub_step <= 2'd0;
                            if (k1 == 4'd15) begin
                                k1 <= 4'd0;
                                if (n2 == 4'd14) begin
                                    k1    <= 4'd0;
                                    m2    <= 3'd0;
                                    l1    <= 2'd0;
                                    m1    <= 2'd0;
                                    state <= S_S2_DFT3;
                                end else begin
                                    n2    <= n2 + 4'd1;
                                    n1    <= 4'd0;
                                    state <= S_S1_LOAD;
                                end
                            end else begin
                                k1 <= k1 + 4'd1;
                            end
                        end
                    end

                    // Stage 2a: 3点 DFT (m1 = 0..2 積和)
                    S_S2_DFT3: begin
                        if (sub_step < 2'd3) begin
                            sub_step <= sub_step + 2'd1;
                        end else begin
                            if (m1 == 2'd0) begin
                                acc_re <= cmul_re;
                                acc_im <= cmul_im;
                            end else begin
                                acc_re <= acc_re + cmul_re;
                                acc_im <= acc_im + cmul_im;
                            end
                            sub_step <= 2'd0;
                            if (m1 == 2'd2) begin
                                m1    <= 2'd0;
                                state <= S_S2_TW15;
                            end else begin
                                m1 <= m1 + 2'd1;
                            end
                        end
                    end

                    // Stage 2b: Twiddle W_15 乗算 -> ram_a 書き込み
                    S_S2_TW15: begin
                        if (sub_step < 2'd3) begin
                            sub_step <= sub_step + 2'd1;
                        end else begin
                            sub_step <= 2'd0;
                            if (l1 == 2'd2) begin
                                l1 <= 2'd0;
                                if (m2 == 3'd4) begin
                                    m2 <= 3'd0;
                                    if (k1 == 4'd15) begin
                                        k1    <= 4'd0;
                                        l1    <= 2'd0;
                                        l2    <= 3'd0;
                                        m2    <= 3'd0;
                                        state <= S_S3_DFT5;
                                    end else begin
                                        k1    <= k1 + 4'd1;
                                        state <= S_S2_DFT3;
                                    end
                                end else begin
                                    m2    <= m2 + 3'd1;
                                    state <= S_S2_DFT3;
                                end
                            end else begin
                                l1    <= l1 + 2'd1;
                                state <= S_S2_DFT3;
                            end
                        end
                    end

                    // Stage 3: 5点 DFT (m2 = 0..4 積和) -> 出力
                    S_S3_DFT5: begin
                        if (sub_step < 2'd3) begin
                            sub_step <= sub_step + 2'd1;
                        end else begin
                            sub_step <= 2'd0;
                            if (m2 < 3'd4) begin
                                if (m2 == 3'd0) begin
                                    acc_re <= cmul_re;
                                    acc_im <= cmul_im;
                                end else begin
                                    acc_re <= acc_re + cmul_re;
                                    acc_im <= acc_im + cmul_im;
                                end
                                m2 <= m2 + 3'd1;
                            end else begin
                                out_valid <= 1'b1;
                                out_idx   <= addr_out_k;
                                out_re    <= {{8{dft5_final_re[23]}}, dft5_final_re};
                                out_im    <= {{8{dft5_final_im[23]}}, dft5_final_im};
                                m2        <= 3'd0;

                                if (l2 == 3'd4) begin
                                    l2 <= 3'd0;
                                    if (l1 == 2'd2) begin
                                        l1 <= 2'd0;
                                        if (k1 == 4'd15) begin
                                            done_wait_mode <= 1'b1;
                                            wait_cnt       <= 4'd0;
                                        end else begin
                                            k1 <= k1 + 4'd1;
                                        end
                                    end else begin
                                        l1 <= l1 + 2'd1;
                                    end
                                end else begin
                                    l2 <= l2 + 3'd1;
                                end
                            end
                        end
                    end

                    default: state <= S_IDLE;
                endcase
            end
        end
    end

endmodule