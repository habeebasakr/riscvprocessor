module controlunit(input [31:0] instruction, output reg[9:0] out );

always@(*)
begin
//jal/jalr, auipc}{branch, memRead, memtoReg,  ALUOp,   memWrite, ALUSrc, regWrite, 
if (instruction[6:2] == 5'b01100)//R
begin  out=10'b0000010001;
end
else if (instruction[6:2] == 5'b00100)//Rimmedate
begin  out=10'b0000010011;
end
else if (instruction[6:2]==5'b00000)//Loads
begin  out=10'b0001100011;
end
else if (instruction[6:2]==5'b01000)//Stores
begin  out=10'b0000000110;
end
else if (instruction[6:2]==5'b11000)//Branch
begin  out=10'b0010001000;
end
else if (instruction[6:2]==5'b11011)//Jal
begin  out=10'b1010000011;  //RD register  must be updated with pc+4 so regWrite must be 1
end
else if (instruction[6:2]==5'b11001)//Jalr
begin  out=10'b1010010011;  //RD register  must be updated with pc+4 so regWrite must be 1
end
else if (instruction[6:2]==5'b00101)//AUIPC 
begin  out=10'b0100000011;
end
else out=10'd0;
end

endmodule