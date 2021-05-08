`timescale 1ns / 1ps


//module DFlipFlop (input clk, input rst, input D, output reg Q);
// always @ (posedge clk or posedge rst)
// if (rst) begin
// Q <= 1'b0;
// end else begin
// Q <= D;
// end 
//endmodule

//module multiplexer #(parameter n=32) (input [n-1:0]a ,input [n-1:0]b, input s, output [n-1:0]c );

//  genvar i;
  
//  generate 
//    for (i = 0; i < n; i = i + 1) 
//    begin : gen
    
//             mux m (s,a[i],b[i],c[i]);
//    end
//  endgenerate

//endmodule

//module mux(input selector, input a, input b, output y);

//assign y=selector?b:a;

//endmodule

//module nbitreg # (parameter n=32) (input clk, input reset,input load, input [n-1:0] d, output [n-1:0] q);

//wire [n-1:0] new;
//genvar i;
//generate 
//for (i=0;i<n;i=i+1)
//begin
//DFlipFlop f(clk,reset,new[i],q[i]);
//mux m (load,q[i],d [i],new[i]);

//end
//endgenerate

//endmodule

//module ALUcontrolunit(input [3:0] inst,input[1:0] ALUOp,output reg [3:0]ALUsel );

//always @(*)
//begin
//if (ALUOp==2'b00 ) 
//begin
//ALUsel = 4'b0010; //ADD
//end else
//    if (ALUOp==2'b01 ) 
//    begin
//    ALUsel = 4'b0110; //sub
//    end 
//    else
//        if (ALUOp==2'b10 && inst[2:0]== 3'b000 &&inst[3]==1'b0 ) 
//        begin
//        ALUsel = 4'b0010; //ADD
//        end else
//            if (ALUOp==2'b10 && inst[2:0]== 3'b000 &&inst[3]==1'b1 ) 
//            begin
//            ALUsel = 4'b0110; //sub
//            end else
//                if (ALUOp==2'b10 && inst[2:0]== 3'b111 &&inst[3]==1'b0 ) 
//                begin
//                ALUsel = 4'b0000; //AND
//                end else
//                    if (ALUOp==2'b10 && inst[2:0]== 3'b110 &&inst[3]==1'b0 ) 
//                    begin
//                    ALUsel = 4'b0001; //OR
//                    end
//                    else ALUsel = 4'b0000; //OR


//end
//endmodule

//module controlunit(input [31:0] instruction, output reg[7:0] out );

//always@(*)
//begin
//if (instruction[6:2] == 5'b01100)//R
//begin  out=8'b00010001;
//end
//else if (instruction[6:2]==5'b00000)//LW
//begin  out=8'b01100011;
//end
//else if (instruction[6:2]==5'b01000)//SW
//begin  out=8'b00000110;
//end
//else if (instruction[6:2]==5'b11000)//BEQ
//begin  out=8'b10001000;
//end
//else out=0;
//end

//endmodule





//module RegFile #(parameter n=32)(input clk, input rst,input [4:0] rr1, input [4:0]rr2, input [4:0]wr, input [n-1:0] wd,
// input regwrite, output [n-1:0] rd1, output [n-1:0] rd2 );

//    reg [31:0]load;
//    wire [n-1:0]q[31:0];
//    //assign loadline= (regwrite==0) ? 0:1 <<wr;
    
    
//    //nbitreg  #(32)registers(clk,rst, 0,0,q[0]);
//    genvar i;
//    generate
//    for (i=0;i<32;i=i+1)
//    begin
//        nbitreg  #(.n(32)) registers(clk,rst, load[i],wd,q[i]);
//    end
//    endgenerate
    
//    assign rd1 = q[rr1];
//    assign rd2 = q[rr2];  
    
    
//    integer j;
    
//    always@(*)begin
//        if(regwrite && wr!=0)begin
//            for(j = 0; j<32; j = j+1)begin
//                if(j == wr)
//                    load[j] = 1;
//                else
//                    load[j] = 0;
//            end
//        end
//        else begin
//             for(j = 0; j<32; j = j+1)begin
//                 load[j] = 0;
//            end       
//        end
//    end  
    
//endmodule

//module Full_Adder(a,b,cin, sum, cout);
//input wire a, b, cin;
//output wire sum, cout; 
//assign {cout,sum} = a+b+cin;
//endmodule

//module ripple#( parameter n=32)   (input [n-1:0] a, input [n-1:0] b, output [n-1:0] out); 
//genvar i;

//wire [n:0]carry;

//assign carry[0] = 1'b0;

//generate
//for (i=0; i<n; i=i+1)
//begin
//Full_Adder inst( .a(a[i]), .b(b[i]), .cin(carry[i]), .sum(out[i]), .cout(carry[i+1]));
//end 
//endgenerate

////assign out[31] = carry[31];
 
//endmodule 

//module alu #(parameter n=32)( input [n-1:0]a,input  [n-1:0]b, input [3:0]select, output reg [n-1:0]c, output reg z);
//wire [n:0] add;
//reg [n-1:0] b2;

//ripple# (n) addmod(a,b2,add);

//always@(*)
//begin
//case (select)
//4'b0010: begin
//b2=b;
//c=add;
//end
//4'b0110: begin
//b2=~b+1;
//c=add;
//end
//4'b0000: begin
//c=a&b;
//end
//4'b0001: begin
//c=a|b;
//end 
//default: begin 
//c=0;
//end
//endcase

//if (c==0)
//z=1'b1;
//else
//z=1'b0;
//end

//endmodule

//module datamem(input clk, input MemRead, input MemWrite, input [4:0] addr,
// input [31:0] data_in, output reg[31:0]  data_out);
// reg [31:0] mem [0:63];

// always @(posedge clk)
// begin
// if (MemWrite)
// mem[addr] = data_in;

// end

// always @(*) 
// begin
// if (MemRead==1)
//     data_out=mem[addr];
//     else
//          data_out=0;
// end



// initial begin
//  mem[0]=32'd17;
//  mem[1]=32'd9;
//  mem[2]=32'd25;
// end
//endmodule

//module InstMem (input [5:0] addr, output [31:0] data_out);
// reg [31:0] mem [0:63];
// assign data_out = mem[addr];
// initial begin
// mem[0]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// //added to be skipped since PC starts with 4 after reset
// mem[1]=32'b000000000000_00000_010_00001_0000011 ; //lw x1, 0(x0)
// mem[2]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[3]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[4]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[5]=32'b000000000100_00000_010_00010_0000011 ; //lw x2, 4(x0)
// mem[6]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[7]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[8]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[9]=32'b000000001000_00000_010_00011_0000011 ; //lw x3, 8(x0)
//mem[10]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
//mem[11]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
//mem[12]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[13]=32'b0000000_00010_00001_110_00100_0110011 ; //or x4, x1, x2
//mem[14]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
//mem[15]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
//mem[16]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[17]=32'b0_000001_00011_00100_000_0000_0_1100011; //beq x4, x3, 16
// mem[18]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[19]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
//mem[20]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[21]=32'b0000000_00010_00001_000_00011_0110011 ; //add x3, x1, x2
// mem[22]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[23]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[24]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[25]=32'b0000000_00010_00011_000_00101_0110011 ; //add x5, x3, x2
// mem[26]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[27]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[28]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0 
// mem[29]=32'b0000000_00101_00000_010_01100_0100011; //sw x5, 12(x0)
// mem[30]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[31]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[32]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[33]=32'b000000001100_00000_010_00110_0000011 ; //lw x6, 12(x0)
// mem[34]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[35]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[36]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[37]=32'b0000000_00001_00110_111_00111_0110011 ; //and x7, x6, x1
//mem[38]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[39]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[40]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[41]=32'b0100000_00010_00001_000_01000_0110011 ; //sub x8, x1, x2
//mem[42]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[43]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[44]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[45]=32'b0000000_00010_00001_000_00000_0110011 ; //add x0, x1, x2
//mem[46]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[47]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[48]=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
// mem[49]=32'b0000000_00001_00000_000_01001_0110011 ; //add x9, x0, x1 
// end 
 
//endmodule

//// initial begin
////  mem[0]=32'd17;
////  mem[1]=32'd9;
////  mem[2]=32'd25;
//// end
////endmodule
//module shift( input [31:0] in, output [31:0] out);
    
//    assign out = {  in[30: 0],1'b0};

//endmodule

//module ImmGen(output reg [31:0] gen_out, input [31:0] inst);
//always@(*)
//begin 
//if(inst[6]==1)
//begin
//    gen_out={{20{inst[31]}},inst[31],inst[7],inst[30:25], inst[11:8]};
//end
//else if(inst[5]==1)
 
//    gen_out={{20{inst[31]}},inst[31:25],inst[11:7]};
    
//   else 
 
//    gen_out={{20{inst[31]}},inst[31:20]};
//end
//endmodule

module UART_receiver_multiple_Keys(
      input clk, // input clock
      input uart_in, // input receiving data line
      output [7:0]out // output
    );
	
	UART_receiver_switch #(8'h61) IN7 (clk, uart_in, out[7]);	//character 'a'
	UART_receiver_switch #(8'h73) IN6 (clk, uart_in, out[6]);	//character 's'
	UART_receiver_switch #(8'h64) IN5 (clk, uart_in, out[5]);	//character 'd'
	UART_receiver_switch #(8'h66) IN4 (clk, uart_in, out[4]);	//character 'f'
	
	UART_receiver_switch #(8'h7a) IN3 (clk, uart_in, out[3]);	//character 'z'
	UART_receiver_switch #(8'h78) IN2 (clk, uart_in, out[2]);	//character 'x'
	UART_receiver_switch #(8'h63) IN1 (clk, uart_in, out[1]);	//character 'c'
	UART_receiver_switch #(8'h76) IN0 (clk, uart_in, out[0]);	//character 'v'
	
endmodule


// UART (Asynchronous) receiver, that gives 0/1 output on out output when 'a' keyboard key ascii value is received
    module UART_receiver_switch # (parameter key = 8'h61) ( 
      input clk, // input clock
      input uart_in, // input receiving data line
      output [7:0] out // output level
      );
          
      //internal variables
      reg [3:0] bitcounter = 0; // 4 bits counter to count if 10 bits data transmission complete or not
      reg [1:0] samplecounter = 0; // 2 bits sample counter to count up to 4 for oversampling
      reg clear_bitcounter, inc_bitcounter, inc_samplecounter, clear_samplecounter; // clear or increment the counter
    
      reg [13:0] counter = 0; // 14 bits counter to count the baud rate (symbol rate) for UART receiving
      reg state = 0;  // initial state variable (mealy finite state machine)
      reg nextstate; // next state variable (mealy finite state machine)
      reg shift; // signal to indicate shifting data is ready
      reg [9:0] rxshiftreg; // 10 bits data needed to be shifted in during transmission. For storing the serial package and sending its bits one by one. The least significant bit is initialized with the binary value "0" (a start bit) A binary value "1" is introduced in the most significant bit
    
      reg output_reset = 0; // our output reset
      reg [31:0] time_counter = 0; // needed for our output reset
    
      // Constants (a parameter infers its type from its value)
      parameter clk_freq = 100_000_000;  // system clock frequency
      parameter baud_rate = 9_600; // baud rate (should be agreed upon with the transmitter)
      parameter oversamples = 4; // oversampling
      parameter reset_counter = clk_freq/(baud_rate*oversamples);  // counter upper bound
   
      // reset_counter = 2604, means counter goes from 0 to 2604 (during that time I should take 1 sample)
      parameter counter_mid_sample = (oversamples/2);  // this is the middle point of a bit where you want to sample it
      parameter num_bit = 10; // 1 start, 8 data, 1 stop
    
      //parameter key = 8'b01100001; // 8'b01100001; is the binary value of the ASCII character of small 'a' keyboard button
      parameter reset_high_seconds = 1;
      parameter reset_time_counter = clk_freq*reset_high_seconds;
    
    
      assign RxData = rxshiftreg [8:1]; // assign the RxData from the shiftregister
      assign out = output_reset;
    
      // UART receiver logic
      always @ (posedge clk) begin 
        counter <= counter +1; // start count in the counter
        if (counter >= reset_counter-1) begin // if counter reach the baud rate with sampling 
          counter <=0; //reset the counter
          state <= nextstate; // assign the state to nextstate
          if (shift)rxshiftreg <= {uart_in,rxshiftreg[9:1]}; //if shift asserted, load the receiving data
          if (clear_samplecounter) samplecounter <=0; // if clear sampl counter asserted, reset sample counter
          if (inc_samplecounter) samplecounter <= samplecounter +1; //if increment counter asserted, start sample count
          if (clear_bitcounter) bitcounter <=0; // if clear bit counter asserted, reset bit counter
          if (inc_bitcounter)bitcounter <= bitcounter +1; // if increment bit counter asserted, start count bit counter
        end
        
       
          
        if (rxshiftreg[8:1] == key) begin
           output_reset <= ~output_reset;
           rxshiftreg[8:1] <= 0;
           end 
//        else begin
//            output_reset <= output_reset;
//            //rxshiftreg[8:1] <= 0;
//           end 
          
      end
         
      // Finite state machine
      always @ (posedge clk) begin //trigger by clock 
        shift <= 0; // set shift to 0 to avoid any shifting 
        clear_samplecounter <=0; // set clear sample counter to 0 to avoid reset
        inc_samplecounter <=0; // set increment sample counter to 0 to avoid any increment
        clear_bitcounter <=0; // set clear bit counter to 0 to avoid claring
        inc_bitcounter <=0; // set increment bit counter to avoid any count
        nextstate <=0; // set next state to be idle state
        case (state)
          0: begin // idle state
            if (uart_in) // if input uart_in data line asserted
              nextstate <=0; // back to idle state because uart_in needs to be low to start transmission    
            else begin // if input uart_in data line is not asserted
              nextstate <=1; // jump to receiving state 
              clear_bitcounter <=1; // trigger to clear bit counter
              clear_samplecounter <=1; // trigger to clear sample counter
            end
          end
          1: begin // receiving state
            nextstate <= 1; // DEFAULT 
            if (samplecounter == counter_mid_sample - 1) shift <= 1; // if sample counter is 1, trigger shift 
            if (samplecounter == oversamples - 1) begin // if sample counter is 3 as the sample rate used is 3
              if (bitcounter == num_bit - 1) // check if bit counter if 9 or not
                nextstate <= 0; // back to idle state if bit counter is 9 as receving is complete
              inc_bitcounter <=1; // trigger the increment bit counter if bit counter is not 9
              clear_samplecounter <=1; //trigger the sample counter to reset the sample counter
            end
            else inc_samplecounter <=1; // if sample is not equal to 3, keep counting
          end
           default: nextstate <=0; //default idle state
         endcase
      end
    endmodule


module Full_datapath( input clk, input rst, input [1:0] ledsel, input [3:0] ssdsel, output reg [7:0] leds, output reg [12:0] ssd);
wire [31:0] inst;
//wire [7:0] out;
wire [4:0] readreg1, readreg2, writereg;
wire  branch, memRead, memtoReg;
wire  [1:0] ALUOp;
wire   memWrite, ALUSrc, regWrite;
wire [31:0] PCsum ;
wire [31:0] PCin ;
wire [31:0] PC;
wire [31:0] ALUresult;
wire zero;
wire [31:0] data_out,data_out_1;
// wire regwrite ;
wire jalr, AUIPC;


wire [31:0] gen_out;
wire [31:0]sum;
wire [31:0] muxout1;
wire [3:0] ALUsel;
wire [31:0] muxout2;
wire [31:0] readdata1, readdata2;
wire [31:0] IF_ID_PC, IF_ID_Inst;
wire [31:0] outIF_ID_PC, outIF_ID_Inst;
wire stall;
wire [11:0] mem_in;
wire sclk;
wire [3:0] EX_MEM_Func_out; 
wire cf_out,zf_out,vf_out,sf_out;
wire [4:0] EX_MEM_RS2;
wire EX_MEM_AUIPC_out;
wire EX_MEM_Jalr_out;
wire branch1;
wire [31:0] EX_MEM_BranchAddOut;
wire [31:0] EX_MEM_ALU_out;
wire [31:0] EX_MEM_RegR2;
wire [4:0] EX_MEM_Ctrl;
wire [4:0] EX_MEM_Rd;
wire EX_MEM_Zero;
wire [1:0] forwardA;
wire [1:0] forwardB;
wire [31:0] aluinput1;
wire [31:0] aluinput2;
wire [1:0] ALUop1;
wire ALUSrc1;
wire [31:0] ID_EX_PC, ID_EX_RegR1, ID_EX_RegR2, ID_EX_Imm;
wire [9:0] ID_EX_Ctrl;
wire [3:0] ID_EX_Func;
wire [4:0] ID_EX_Rs1, ID_EX_Rs2;
//ID_EX_Rd;
wire [4:0] ID_EX_lastInst;
wire [4:0] out_ID_EX_lastInst;
wire [31:0] ID_EX_PC_out, ID_EX_RegR1_out, ID_EX_RegR2_out, ID_EX_Imm_out;
wire [9:0] ID_EX_Ctrl_out;
wire [3:0] ID_EX_Func_out;
wire [4:0] ID_EX_Rs1_out, ID_EX_Rs2_out;
wire [4:0] ID_EX_shamt;
wire [4:0] ID_EX_shamt_out;
wire [31:0] MEM_WB_sum; 
wire [31:0] MEM_WB_PCsum; 
wire  MEM_WB_AUIPC;
wire  MEM_WB_JALR; 
wire [31:0] EX_MEM_in;
wire [4:0] MEM_WB_Rd;

clkdiv clk1(clk, rst, sclk);
//module nbitreg # (parameter n=32) (input clk, input reset,input load, input [n-1:0] d, output [n-1:0] q);
wire [2:0] func;
assign mem_in = (sclk) ? EX_MEM_ALU_out[11:0] : PC[11:0];
assign func = (sclk) ?EX_MEM_Func_out[2:0] : 3'b010 ;
SingleMem singlem(sclk, clk, memread1, memwrite1,
 mem_in, func, EX_MEM_in, data_out);

assign IF_ID_PC=PC;
assign IF_ID_Inst=(sclk) ? 32'b0000000_00000_00000_000_00000_0110011 : data_out;
wire [1:0] branchcontrolsignal;

PC PCmux(PCsum, EX_MEM_BranchAddOut, EX_MEM_ALU_out, branchcontrolsignal,  PCin);
//(if branch or jalr): 32'b: 
nbitreg #(32) Pcc (sclk, rst,1'b1 ,PCin,PC);
ripple adderr(32'd4, PC, PCsum);
//wire pc_sel; 
//assign pc_sel = branch1 & EX_MEM_Zero; 

//multiplexer muxx(PCsum,EX_MEM_BranchAddOut, pc_sel, PCin);
wire [31:0] out_IF_ID_PCsum;
wire [31:0] rfin;

wire[95:0] IF_IDin= (EX_MEM_Jalr_out || branch1) ? 32'b0000000_00000_00000_000_00000_0110011 :
 {IF_ID_PC, IF_ID_Inst, PCsum};  
 
 nbitreg #(96) IF_ID (clk,rst,1'b1,
 {IF_IDin},
 {outIF_ID_PC, outIF_ID_Inst, out_IF_ID_PCsum}
  );    

RFMux rfmuxx ( MEM_WB_sum, MEM_WB_PCsum,muxout2, MEM_WB_JALR, MEM_WB_AUIPC, rfin);
RegFile RF(!clk, rst, readreg1, readreg2,writereg ,rfin, MEM_WB_Ctrl[0] , readdata1, readdata2 );

rv32_ImmGen imminstr ( outIF_ID_Inst, gen_out  );
controlunit CUI (outIF_ID_Inst , {jalr, AUIPC, branch, memRead, memtoReg,  ALUOp,   memWrite, ALUSrc, regWrite} );



// ID_EX_Rd_out;
assign ID_EX_Ctrl={jalr, AUIPC, branch, memRead, memtoReg,  ALUOp,   memWrite, ALUSrc, regWrite};
assign ID_EX_PC=outIF_ID_PC;
assign ID_EX_Rs1=readreg1;
assign ID_EX_Rs2=readreg2;
assign ID_EX_RegR1=readdata1;
assign ID_EX_RegR2=readdata2;
assign ID_EX_Imm=gen_out;
assign ID_EX_Func={outIF_ID_Inst[30], outIF_ID_Inst[14:12]};
assign ID_EX_lastInst=outIF_ID_Inst[11:7];  
assign ID_EX_shamt = outIF_ID_Inst[24:20];
wire [31:0] ID_EX_PCsum; 
wire[193:0] ID_EXin= (EX_MEM_Jalr_out || branch1) ? 32'b0000000_00000_00000_000_00000_0110011 :
 {ID_EX_Ctrl,ID_EX_PC,ID_EX_RegR1,ID_EX_RegR2,
    ID_EX_Imm, ID_EX_Func,ID_EX_Rs1,ID_EX_Rs2,ID_EX_lastInst,ID_EX_shamt,out_IF_ID_PCsum};  
 nbitreg #(194) ID_EX (clk,rst,1'b1,
 {ID_EXin},
{ID_EX_Ctrl_out,ID_EX_PC_out,ID_EX_RegR1_out,ID_EX_RegR2_out,
    ID_EX_Imm_out, ID_EX_Func_out,ID_EX_Rs1_out,ID_EX_Rs2_out, out_ID_EX_lastInst,
    ID_EX_shamt_out, ID_EX_PCsum});

// {ID_EX_Ctrl,ID_EX_PC,ID_EX_RegR1,ID_EX_RegR2,
// ID_EX_Imm, ID_EX_Func,ID_EX_Rs1,ID_EX_Rs2,ID_EX_Rd} );


assign ALUop1=ID_EX_Ctrl_out[4:3];
assign ALUSrc1=ID_EX_Ctrl_out[1];  
 // Rs1 and Rs2 are needed later for the forwarding unit
wire cf,zf,vf,sf;
ripple  add2(ID_EX_Imm_out,ID_EX_PC_out, sum); 
multiplexer muxx1(aluinput2, ID_EX_Imm_out, ALUSrc1,muxout1);
ALUcontrolunit acu(ID_EX_Func_out, ALUop1, ALUsel);
prv32_ALU aluu1(aluinput1,muxout1,ID_EX_shamt_out, ALUresult,cf,zf,vf,sf, ALUsel );

//inst[24:20]????? 


forwarding_unit f1(ID_EX_Rs1_out, ID_EX_Rs2_out, EX_MEM_Rd, MEM_WB_Rd, 
  EX_MEM_Ctrl[0], MEM_WB_Ctrl[0], forwardA,  forwardB);
mux4x1 m1 (ID_EX_RegR1_out, muxout2, EX_MEM_ALU_out,32'd0, forwardA, aluinput1);
mux4x1 m2 (ID_EX_RegR2_out, muxout2, EX_MEM_ALU_out,32'd0, forwardB, aluinput2);




//assign  EX_MEM_BranchAddOut=sum;
//assign EX_MEM_ALU_out= ALUresult;
//assign  EX_MEM_RegR2= ID_EX_RegR2; //?
//assign EX_MEM_Zero=zero;
////assign EX_MEM_Ctrl=;
//assign EX_MEM_Rd= ID_EX_lastInst;
//wire [3:0] EX_MEM_Func_out; 
//wire cf_out,zf_out,vf_out,sf_out;
//wire [4:0] EX_MEM_RS2;
//hazardunit hu(ID_EX_Rs1,ID_EX_Rs2,ID_EX_Ctrl_out[5],muxout2, stall);
wire EX_MEM_Jalr = ID_EX_Ctrl_out[9];
wire EX_MEM_AUIPC = ID_EX_Ctrl_out[8];

wire [4:0]control_new= {ID_EX_Ctrl_out[7:5], ID_EX_Ctrl_out[2], ID_EX_Ctrl_out[0]};
//wire [4:0] cc;
//assign cc = (stall == 1)? 0 : control_new; 
wire [31:0] EX_MEM_PCsum; 
wire[184:0] EX_MEMin= (EX_MEM_Jalr_out || branch1) ? 32'b0000000_00000_00000_000_00000_0110011 :
 {control_new, sum, ALUresult,ID_EX_RegR2_out,out_ID_EX_lastInst,
 ID_EX_Func_out,cf,zf,vf,sf,ID_EX_Rs2_out,EX_MEM_Jalr,EX_MEM_AUIPC, ID_EX_PCsum,aluinput2};  
 nbitreg #(185) EX_MEM (clk,rst,1'b1,
 {EX_MEMin},
 {EX_MEM_Ctrl, EX_MEM_BranchAddOut,
 EX_MEM_ALU_out, EX_MEM_RegR2, EX_MEM_Rd,EX_MEM_Func_out,cf_out,zf_out,vf_out,sf_out,
 EX_MEM_RS2,EX_MEM_Jalr_out,EX_MEM_AUIPC_out,EX_MEM_PCsum,EX_MEM_in} );

assign branch1= EX_MEM_Ctrl[4];
assign memread1=EX_MEM_Ctrl[3];
assign memwrite1=EX_MEM_Ctrl[1];

branchControl bc(cf_out,zf_out,sf_out,vf_out, branch1,EX_MEM_Jalr_out ,branchcontrolsignal);

wire [31:0] MEM_WB_Mem_out, MEM_WB_ALU_out;
wire [1:0] MEM_WB_Ctrl;
//assign  MEM_WB_Mem_out= data_out_1;
//assign MEM_WB_ALU_out= EX_MEM_ALU_out;
//assign  MEM_WB_Rd= EX_MEM_Rd;
//// assign  MEM_WB_Ctrl= ;

 nbitreg #(137) MEM_WB (clk,rst,1'b1,
 {{EX_MEM_Ctrl[2], EX_MEM_Ctrl[0]}, data_out, EX_MEM_ALU_out,EX_MEM_Rd,
 EX_MEM_BranchAddOut,EX_MEM_PCsum,EX_MEM_AUIPC_out,EX_MEM_Jalr_out },
 {MEM_WB_Ctrl,MEM_WB_Mem_out, MEM_WB_ALU_out,
 MEM_WB_Rd, MEM_WB_sum,MEM_WB_PCsum,MEM_WB_AUIPC, MEM_WB_JALR} ); 





assign readreg1=outIF_ID_Inst[19:15];
assign readreg2=outIF_ID_Inst[24:20];
assign writereg= MEM_WB_Rd;

//PC

//PC + 4 [Output = PCSum] 

//Branched PC calculation [Output = sum] 
//shift sh1(ID_EX_Imm_out, shiftout);

//Choosing correct PC  [Output = PCin] 

//InstMem instmem(PC[7:2],data_out);
//assign inst =data_out;
//
//
//


//datamem  data1( clk,  memread1,  memwrite1,  EX_MEM_ALU_out [6:2], EX_MEM_RegR2, data_out_1);

multiplexer muxx3( MEM_WB_ALU_out,MEM_WB_Mem_out , MEM_WB_Ctrl[1],muxout2);
//multiplexer muxx3(data_out_1,ALUresult , memtoReg,muxout2);
//always@(*)
//begin 
//case(ledsel)
//    2'b00: leds = {branch, memRead, memtoReg,  ALUOp,   memWrite, ALUSrc, regWrite};
//    2'b01: leds =  {1'b0, ALUsel, zero, branch, pc_sel}; 
//    default: leds = 0; 
//endcase

//case(ssdsel)
//            4'b0000: ssd = PC;
//            4'b0001: ssd = PCsum;
//            4'b0010: ssd = sum;
//            4'b0011: ssd = PCin;
//            4'b0100: ssd = readdata1;
//            4'b0101: ssd = readdata2;
//            4'b0110: ssd = muxout2;
//            4'b0111: ssd = gen_out;
//            4'b1000: ssd = shiftout;
//            4'b1001: ssd = muxout1;
//            4'b1010: ssd = ALUresult;
//            4'b1011: ssd = data_out;
//            default: ssd = inst;
//endcase
//end
endmodule
