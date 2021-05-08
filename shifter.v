`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/25/2020 09:06:23 PM
// Design Name: 
// Module Name: shifter
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:ss
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module shifter( input [31:0]a,  input shamt, input [1:0] type, output reg [31:0] r);

 always@ (*)
 begin  
 case (type)
   //
 //we're supposed to shift a by the amount, depending on alufn (?)
2'b00: r = a >> shamt; //srl
2'b01: r = a << shamt; //sll
2'b10: r = a >>> shamt; // sra


 endcase
 

end
endmodule
