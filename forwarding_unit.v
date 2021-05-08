`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/10/2020 09:13:05 AM
// Design Name: 
// Module Name: forwarding_unit
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


module forwarding_unit(input[4:0] rs1, input [4:0]rs2, input[4:0] memrd,input [4:0] wbrd, input regwritemem,
 input regwritewb, output reg [1:0] forwardA, output reg [1:0] forwardB);

always@ (*)
begin 

if ((memrd!=0) && (memrd==rs1) && (regwritemem==1))
    forwardA=2'b10;
    
   
    else if ((regwritewb==1) && (wbrd!=0) &&(wbrd==rs1))
                forwardA=2'b01; 
                    else forwardA=2'b00;
                    
                    
if ((regwritemem==1) && (memrd!=0) && (memrd==rs2))
                        forwardB=2'b10;  //forward from exmem
else if( (regwritewb==1) && (wbrd!=0) &&(wbrd==rs2))
             forwardB=2'b01; 
           else 
             forwardB=2'b00; 




end



endmodule
