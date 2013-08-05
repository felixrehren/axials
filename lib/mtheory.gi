
#
#  m theory implementation
#

InstallMethod( Mtheory,
	[IsRat,IsList,IsList],
	function( c, fields, fusiontbl )
	return Objectify(
		TypeMtheory@,
		rec( 
			cc := c,
			fields := fields,
			fuse := function(f,g)
				return fusiontbl[Position(fields,f)][Position(fields,g)]; end
		)
	);
	end
);
	InstallMethod( CentralCharge,
		[IsMtheory],
		T -> T!.cc
	);
	InstallMethod( Fields,
		[IsMtheory],
		T -> T!.fields
	);
	InstallMethod( Fuse,
		[IsMtheory,IsRat,IsRat],
		function(T,f,g)
		return T!.fuse(f,g);
		end
		);
	InstallMethod( ViewString,
		[IsMtheory],
		function(T)
		return Concatenation("an Mtheory, central charge ",CentralCharge(T));
		end
		);
	InstallMethod( Display,
		[IsMtheory],
		function(T)
		return Concatenation("Mtheory of central charge ",CentralCharge(T),
			" with fields ",JoinStringsWithSeparator(Fields(T),", "));
		end
);

InstallMethod( VirasoroMtheory,
	[IsPosInt,IsPosInt],
	function(p,q)
	local pairs, field, fields, fusiontbl, T;
	pairs := Filtered(Cartesian([1..p-1],[1..q-1]),
		xx -> xx[1]/xx[2] < p/q);
	field := xx -> ((p*xx[2]-q*xx[1])^2-(p-q)^2)/(4*p*q);
	fields := List(pairs,xx -> field);
	fusiontbl := List(pairs,p1->List(pairs,function(p2)
		local minx, maxx, miny, maxy;
		minx := 1 + AbsoluteValue(p1[1]-p2[1]);
		maxx := Minimum(p1[1]+p2[1]-1,2*p-p1[1]-p2[1]-1);
		miny := 1 + AbsoluteValue(p1[2]-p2[2]);
		maxy := Minimum(p1[2]+p2[2]-1,2*q-p1[2]-p2[2]-1);
		return List(Cartesian([minx,minx+2..maxx],[miny,miny+2..maxy]),
			field);
		end ));
	T := Mtheory( 
		1 - 6*(p-q)^2/(p*q),
		fields,
		fusiontbl
	);
	SetIsRationalVirasoroMtheory(T,true);
	if p = q+1 or p=q-1 then SetIsUnitaryMtheory(T,true); fi;
	return T;
	end
);

InstallMethod( Sakuma,
	[IsList,IsMatrix],
	function( algs, incidence )
	return Objectify(
		TypeSakuma@,
		rec(
			orders := List(algs,a->a[1]),
			letters := List(algs,a->a[2]),
			incidence := incidence,
			find := function(n,X)
				return First([1..Length(algs)],
					i->algs[i][1]=n and algs[i][2]=X);
				end
		)
	);
	end
	);
	InstallMethod( ViewString,
		[IsSakuma],
		function(S)
		return Concatenation("a specification of ",String(Length(S!.orders)),
		" Sakuma (2-generated) algebras (or something)");
		end
		);
InstallMethod( GetAlgebra,
	[IsSakuma,IsPosInt,IsString],
	function(Sak,n,X)
	local i;
	i := Sak!.find(n,X);
	return [Sak!.orders[i],Sak!.letters[i]];
	end
	);
InstallMethod( GetAlgebras,
	[IsSakuma,IsPosInt],
	function(Sak,n)
	return List(FilteredPositions(Sak!.orders,o->o=n),
		i -> [n,Sak!.letters[i]]);
	end
	);
InstallMethod( SubAlgebras,
	[IsSakuma,IsList],
	function(Sak,nX)
	return List(Filtered([1..Length(Sak!.orders)],
		i -> not IsZero(Sak!.incidence[i][Sak!.find(nX[1],nX[2])]) ),
		i->[Sak!.orders[i],Sak!.letters[i]]);
	end
	);
InstallMethod( SupAlgebras,
	[IsSakuma,IsList],
	function(Sak,nX)
	return List(Filtered([1..Length(Sak!.orders)],
		i -> not IsZero(Sak!.incidence[Sak!.find(nX[1],nX[2])][i]) ),
		i->[Sak!.orders[i],Sak!.letters[i]]);
	end
	);
InstallMethod( Orders,
	[IsSakuma],
	function(Sak)
	return Set(Sak!.orders);
	end
);

InstallValue( MajoranaTheory,
	Mtheory(1,[1,0,1/4,1/32],
		[ [ [1],[0],[1/4],[1/32] ],
			[ [0],[0],[1/4],[1/32] ],
			[ [1/4],[1/4],[1,0],[1/32] ],
			[ [1/32],[1/32],[1/32],[1,0,1/4] ] ])
	);
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

