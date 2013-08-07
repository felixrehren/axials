
#
#  m theory implementation
#

InstallMethod( Mtheory,
	[IsRat,IsList,IsList,IsString],
	function( c, fields, fusiontbl, Tag )
	return Objectify(
		TypeMtheory@,
		rec( 
			cc := c,
			fields := fields,
			tbl := fusiontbl,
			fuse := function(f,g)
				return ~.tbl[Position(fields,f)][Position(fields,g)]; end,
			tag := Tag
		)
	);
	end
);
	InstallMethod( CentralCharge,
		[IsMtheory],
		T -> T!.cc
	);
	InstallMethod( Tag,
		[IsMtheory],
		T -> T!.tag
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
	InstallMethod( Tag,
		[IsMtheory],
		function(T)
		return T!.tag;
		end
		);
	InstallMethod( ViewString,
		[IsMtheory],
		T -> Concatenation(
			"Mtheory ",Tag(T),
			" of central charge ",String(CentralCharge(T))
		)
		);
	InstallMethod( DisplayString,
		[IsMtheory],
		T -> Concatenation(
			ViewString(T),
			" with fields ",JoinStringsWithSeparator(List(Fields(T),String),", ")
		)
		);
	InstallMethod( PrintString,
		[IsMtheory],
		T -> Concatenation(
			"Mtheory(",
			String(CentralCharge(T)),",",
			String(Fields(T)),",\n",
			"\t",String(T!.tbl),",\n",
			"\t\"",Tag(T),"\"\n",
			")"
		)
);

InstallMethod( VirasoroMtheory,
	[IsPosInt,IsPosInt],
	function(p,q)
	local pairs, field, fields, fusiontbl, T;
	if not p > q then return VirasoroMtheory(q,p); fi;
	pairs := Filtered(Cartesian([1..p-1],[1..q-1]),
		xx -> xx[1]/xx[2] < p/q);
	field := xx -> 1/2*((p*xx[2]-q*xx[1])^2-(p-q)^2)/(4*p*q);
	fields := List(pairs,field);
	fusiontbl := List(pairs,p1->List(pairs,function(p2)
		local minx, maxx, miny, maxy;
		minx := 1 + AbsoluteValue(p1[1]-p2[1]);
		maxx := Minimum(p1[1]+p2[1]-1,2*p-p1[1]-p2[1]-1);
		miny := 1 + AbsoluteValue(p1[2]-p2[2]);
		maxy := Minimum(p1[2]+p2[2]-1,2*q-p1[2]-p2[2]-1);
		return List(Cartesian([minx,minx+2..maxx],[miny,miny+2..maxy]),field);
		end ));
	T := Mtheory( 
		1 - 6*(p-q)^2/(p*q),
		fields,
		fusiontbl,
		Concatenation("vir-",String(p),"-",String(q))
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
