
#
#  fusion implementation
#

InstallMethod( Fusion,
	[IsRat,IsList,IsList,IsString],
	function( c, fields, fusiontbl, tag )
		local R;
		R := rec( tbl := fusiontbl );
		ObjectifyWithAttributes(
			R, TypeFusion@,
			CentralCharge, c,
			Fields, fields,
			Fuse, function(f,g)
				local p, q;
				p := Position(fields,f);
				if p = fail then return fail; fi;
				q := Position(fields,g);
				if q = fail then return fail; fi;
				return fusiontbl[p][q]; end,
			Tag, tag
		);
		return R;
	end
);
	InstallMethod( \=, "for two fusions",
		[IsFusion,IsFusion],
		function( f,g )
		return CentralCharge(f) = CentralCharge(g)
			and Fields(f) = Fields(g)
			and f!.tbl = g!.tbl;
		end
		);
	InstallMethod( ViewString,
		[IsFusion],
		T -> Concatenation(
			"fusion ",Tag(T),
			" of central charge ",String(CentralCharge(T))
		)
		);
	InstallMethod( DisplayString,
		[IsFusion],
		T -> Concatenation(
			ViewString(T),
			" with fields ",JoinStringsWithSeparator(List(Fields(T),String),", ")
		)
		);
	InstallMethod( PrintString,
		[IsFusion],
		T -> Concatenation(
			"Fusion(",
			String(CentralCharge(T)),",",
			String(Fields(T)),",\n",
			"\t",String(T!.tbl),",\n",
			"\t\"",Tag(T),"\"\n",
			")"
		)
	);
InstallMethod( Subfusion,
	[IsFusion,IsList,IsString],
	function( F, ff, tag )
		local pos;
		pos := List(ff, f-> Position(Fields(F),f));
		return Fusion(
			CentralCharge(F),
			ff,
			List(F!.tbl{pos}{pos},r->List(r,e->Filtered(e,f->f in ff))),
			tag );
	end
	);
InstallMethod( Miyamoto,
	[IsFusion],
	function( th )
	local part0, part1, f;
	part0 := Union(List(Fields(th),f->Fuse(th)(f,f)));
	part1 := Difference(Fields(th),part0);
	while true do
		f := FirstPosition(part1,f->ForAny(part0,g->not IsSubset(part1,Fuse(th)(f,g))));
		if f = fail then return part1;
		else
			Add(part0,part1[f]);
			Remove(part1,f); 
		fi;
	od;
	end
	);
InstallMethod( MiyamotoFixedFusion,
	[IsFusion],
	function( th )
		local m;
		m := Miyamoto(th);
		if m = [] then return th;
		else return Subfusion(th,Filtered(Fields(th),f->not f in m),Tag(th)); fi;
		end
	);
InstallMethod( ChangeFields,
	[IsFusion,IsList,IsString],
	function( fus, fields, tag )
		return Fusion(
			CentralCharge(fus),
			fields,
			List( [1..Fields(fus)], i ->
				List( [1..Fields(fus)], j ->
					List( Fuse(fus)(Fields(fus)[i],Fields(fus)[j]),
					f -> fields[Position(Fields(fus))] ) ) ),
			tag
		);
	end
);


InstallMethod( VirasoroFusion,
	[IsPosInt,IsPosInt],
	function(p,q)
	local pairs, field, fields, virtbl, fusiontbl, i, j, T;
	if not (p > 1 and q > 1 and Gcd(p,q) = 1) then return fail; fi;
	if not p > q then return VirasoroFusion(q,p); fi;
	pairs := Filtered(Cartesian([1..p-1],[1..q-1]),
		xx -> xx[1]/xx[2] < p/q);
	field := xx -> 1/2*((p*xx[2]-q*xx[1])^2-(p-q)^2)/(4*p*q);
	fields := Concatenation([1],List(pairs,field));
	virtbl := List(pairs,p1->List(pairs,function(p2)
		local minx, maxx, miny, maxy;
		minx := 1 + AbsoluteValue(p1[1]-p2[1]);
		maxx := Minimum(p1[1]+p2[1]-1,2*p-p1[1]-p2[1]-1);
		miny := 1 + AbsoluteValue(p1[2]-p2[2]);
		maxy := Minimum(p1[2]+p2[2]-1,2*q-p1[2]-p2[2]-1);
		return List(Cartesian([minx,minx+2..maxx],[miny,miny+2..maxy]),field);
		end ));
	fusiontbl := [List(fields,f->[f])];
	for i in [1..Length(pairs)] do
		fusiontbl[i+1] := [[fields[i+1]]];
		for j in [1..Length(pairs)] do
			fusiontbl[i+1][j+1] := virtbl[i][j];
			if 0 in virtbl[i][j] then Add(fusiontbl[i+1][j+1],1); fi;
		od;
	od;
	i := Position(fields,0);
	j := Position(fields,1);
	fusiontbl[i][i] := [0];
	#fusiontbl[j][i] := [];
	#fusiontbl[i][j] := [];
	T := Fusion( 
		1 - 6*(p-q)^2/(p*q),
		fields,
		fusiontbl,
		Concatenation("vir-",String(p),"-",String(q))
	);
	SetIsVirasoroFusion(T,true);
	SetIsRationalVirasoroFusion(T,true);
	SetVirasoroP(T,p);
	SetVirasoroQ(T,q);
	if p = q+1 or p = q-1 then SetIsUnitaryFusion(T,true); fi;

	if p mod 2 = 0
	then SetMiyamoto(T,List(Filtered(pairs,p -> p[1] mod 2 = 0),field)); fi;
	if q mod 2 = 0
	then SetMiyamoto(T,List(Filtered(pairs,p -> p[2] mod 2 = 0),field));
	else SetMiyamoto(T,List(Filtered(pairs,p->Sum(p) mod 2 = 1),field));
	fi;

	return T;
	end
	);
	InstallMethod( PrintString,
	[IsRationalVirasoroFusion],
	T -> Concatenation( "VirasoroFusion(",
		String(VirasoroP(T)),",",String(VirasoroQ(T)),")" )
);


																		#sakuma
###############################################################################

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
	InstallMethod( PrintString,
	[IsSakuma],
	S -> Concatenation("Sakuma(\n",
		PrintString( Classes(Sakuma) ),",\n",
		PrintString( S!.incidence ),
		"\n)"
	)
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
	Sak -> Set(Sak!.orders)
	);
	InstallMethod( Classes,
	[IsSakuma],
	Sak -> List([1..Length(Sak!.orders)],i->[Sak!.orders[i],Sak!.letters[i]])
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
InstallValue( MajoranaFusion, VirasoroFusion(4,3) );
InstallMethod( MajoranaShapes,
	[IsGroup],
	G -> Shapes(G,MajoranaSakuma)
	);
	InstallMethod( MajoranaShapes,
	[IsTrgp],
	G -> Shapes(G,MajoranaSakuma)
);

InstallMethod( ObservedSakuma,
	[IsFusion],
	function( fus )
	local SS, shapes, cl, mat;
	SS := Concatenation(List(
		Filtered(GetAxialRep(fus),
			str -> str = "2^2"
					or str = "S3"
			or str[1] = 'D' and ForAll(str{[2..Length(str)]},IsDigitChar)
		),
		str -> List(GetAxialRep(fus,str),Trgp)
	) );
	shapes := List(SS,Shape);
	cl := Set(Concatenation(shapes));
	mat := List([1..Length(cl)],i -> List([1..Length(cl)],function(j)
		if ForAny(SS,function(S) local pi,pj;
			pi := FilteredPositions(Shape(S),s->s=cl[i]);
			if IsEmpty(pi) then return false; fi;
			pj := FilteredPositions(Shape(S),s->s=cl[j]);
			if IsEmpty(pj) then return false; fi;
			return ForAny(pi,p->ForAny(pj,q->q>p and IsOne(IncidencePairs(S)[p][q])));
			end
		) then return 1;
		else return 0; fi;
		end
	));
	return Sakuma( cl,mat );
	end
);

