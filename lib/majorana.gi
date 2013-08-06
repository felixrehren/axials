
#
#  majorana implementation
#

InstallValue( MajoranaSakuma,
	Sakuma(
	[ [2,"A"],
		[2,"B"],
		[3,"A"],
		[3,"C"],
		[4,"A"],
		[4,"B"],
		[5,"A"],
		[6,"A"] ],
	[ [1,0,0,0,0,1,0,1],
		[0,1,0,0,1,0,0,0],
		[0,0,1,0,0,0,0,1],
		[0,0,0,1,0,0,0,0],
		[0,0,0,0,1,0,0,0],
		[0,0,0,0,0,1,0,0],
		[0,0,0,0,0,0,1,0],
		[0,0,0,0,0,0,0,1] ] )
	);
InstallValue( MajoranaTheory, VirasoroMtheory(4,3) );

InstallMethod( MajoranaShapes,
	[IsGroup],
	G -> Shapes(G,MajoranaSakuma)
	);
	InstallMethod( MajoranaShapes,
	[IsTrgp],
	G -> Shapes(G,MajoranaSakuma)
	);
InstallMethod( StartMajRep,
	[HasShape],
	S -> StartMrep(S,MajoranaTheory)
	);
