`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/28/2020 04:32:37 PM
// Design Name: 
// Module Name: PC
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module PC(input [31:0] PCsum, input [31:0] sum, input [31:0] ALUresult, input[1:0] branchcontrolsignal, output reg [31:0] PCin);

always@(*)
begin
case(branchcontrolsignal)

//correct implementation

2'b00:    PCin= PCsum;
2'b01:    PCin= sum; 
//2'b10:    PCin= sum;
2'b11:    PCin= ALUresult;
default: PCin= PCsum;

//Use this so the simulation can work

//2'b00:    PCin= PCsum;
//2'b01:    PCin=PCsum; 
//2'b10:    PCin= PCsum;
//2'b11:    PCin= PCsum;
//default: PCin=PCsum;

endcase
end


endmodule
