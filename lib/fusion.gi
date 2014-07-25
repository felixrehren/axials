
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
			and Set(Fields(f)) = Set(Fields(g))
			and ForAll([1..Length(Fields(f))],i->ForAll([1..i],j->
				Fuse(f)(Fields(f)[i],Fields(f)[j])=Fuse(g)(Fields(f)[i],Fields(f)[j])));
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
	fusiontbl[j][i] := [];
	fusiontbl[i][j] := [];
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
	then SetMiyamoto(T,List(Filtered(pairs,p -> p[1] mod 2 = 0),field));
	elif q mod 2 = 0
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
InstallMethod( KacEntry,
	[IsRationalVirasoroFusion,IsPosInt,IsPosInt],
	function( V, i, j )
  local p, q;
		p := VirasoroP(V);
		q := VirasoroQ(V);
		i := i mod p;
		j := j mod q;
		if i*j = 0 then return fail; fi;
		return 1/2*((p*j-q*i)^2-(p-q)^2)/(4*p*q);
	end
	);
InstallMethod( KacPosition,
	[IsRationalVirasoroFusion,IsRat],
	function( V, hw )
  local p, q, i, j;
		if not hw in Fields(V) then return fail; fi;
		p := VirasoroP(V);
		q := VirasoroQ(V);
		for i in [1..VirasoroP(V)-1] do
			for j in [1..VirasoroQ(V)-1] do
				if hw = 1/2*((p*j-q*i)^2-(p-q)^2)/(4*p*q)
				then return [i,j]; fi;
			od;
		od;
		return fail;
	end
	);
InstallMethod( VirasoroRamond,
	[IsPosInt],
	function(m)
	local c, fields, tbl;
	c := 3/2*(1-8/(m*(m+2)));
	fields := Union(List([1..m],p->List(Filtered([1..m+2],q->(p-q) mod 2 = 0),
		q->(((m+2)*p-m*q)^2-4)/(8*m*(m+2)) )));
	tbl := List(fields,f->List(fields,g->[]));
	return Fusion(
		c,
		fields,
		tbl,
		Concatenation("virR-",String(m))
		);
	end
	);
InstallMethod( VirasoroNeveuSchwarz,
	[IsPosInt],
	function(m)
	local c, fields, tbl;
	c := 3/2*(1-8/(m*(m+2)));
	fields := Union(List([1..m],p->List(Filtered([1..m+2],q->(p-q) mod 2 = 1),
		q->(((m+2)*p-m*q)^2-4)/(8*m*(m+2))+1/16 )));
	tbl := List(fields,f->List(fields,g->[]));
	return Fusion(
		c,
		fields,
		tbl,
		Concatenation("virNS-",String(m))
		);
	end
);


InstallValue( MajoranaFusion, VirasoroFusion(4,3) );
InstallMethod( JordanFusion,
	[IsRat],
	al ->
	Fusion(
		1/2,
		[1,0,al],
		[[[1],[],[al]],
		[[],[0],[al]],
		[[al],[al],[1,0]]],
		Concatenation("jordan-",String(al))
	)
);
InstallValue( FischerFusion, JordanFusion(1/4) );
