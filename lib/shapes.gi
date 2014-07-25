
#
#  shapes implementation
#

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
InstallValue( FischerSakuma,
	Sakuma(
	[ [2,"B"],
		[3,"C"] ],
	[ [1,0],
		[0,1] ] )
	);
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

InstallMethod( Shapes,
	[IsTrgp,IsSakuma],
	function(T,S)
	local subs, sups, wip, res, PropCh, sh, j, sh2, permOnPairs;
	subs := i -> Filtered([1..Length(Pairs(T))],j->
		j<>i and IsOne(IncidencePairs(T)[j][i]));
	sups := i -> Filtered([1..Length(Pairs(T))],j->
		j<>i and IsOne(IncidencePairs(T)[i][j]));
	IncidencePairs(T); # changes order of pairs!
	wip := [List(Pairs(T),p->Order(Product(p)))];
	res := [];
	PropCh := function( sh, i, cl )
		local wip, cc, j, c;
		sh := ShallowCopy(sh);
		sh[i] := cl;
		wip := [sh];
		for j in Filtered(subs(i),j->IsInt(sh[j])) do
			cc := Filtered(SubAlgebras(S,cl),a->a[1]=sh[j]);
			if IsEmpty(cc) then return []; fi;
			for c in cc do
				wip := Concatenation(List(wip,sh->PropCh( sh, j, c )));
		od; od;
		for j in Filtered(sups(i),j->IsInt(sh[j])) do
			cc := Filtered(SupAlgebras(S,cl),a->a[1]=sh[j]);
			if IsEmpty(cc) then return []; fi;
			for c in cc do
				wip := Concatenation(List(wip,sh->PropCh( sh, j, c )));
		od; od;
		return wip;
	end;
	while not IsEmpty(wip) do
		sh := Remove(wip);
		j := FirstPosition(sh,IsInt);
		for sh2 in Concatenation(List(GetAlgebras(S,sh[j]),cl->PropCh(sh,j,cl))) do
			if ForAny(sh2,IsInt) then Add(wip,sh2);
			else Add(res,sh2); fi;
		od;
	od;
	if Size(res) <> 1 and Size(Set(List(res,Set))) <> Size(res) then 
		permOnPairs := function(g)
			local targets;
			targets := [1..Length(Pairs(T))];
			return PermListList( [1..Length(Pairs(T))],
				List([1..Length(Pairs(T))], i ->
				First(Filtered(targets,
					t->Order(Product(Pairs(T)[t])) = Order(Product(Pairs(T)[i])) ),
					function(t)
					if RepresentativeAction( T,
						OnSets(Pairs(T)[i],g),Pairs(T)[t],OnSets ) <> fail
					then targets := Difference(targets,[t]); return true;
					else return false; fi;
					end )) );
			end;
		res := List( OrbitsDomain(
			Group(List(GeneratorsOfGroup(AutomorphismGroup(T)),permOnPairs)),
			res,
			Permuted ), Representative );
	fi;
	return List(
		res,
		function(sh)
		local S;
		S := TrgpNC(T,Transpositions(T));
		SetPairs(S,Pairs(T));
		SetShape(S,sh);
		return S; end
	);
	end
	);
	InstallMethod( Shapes,
	[IsGroup,IsSakuma],
	function(G,S)
	return Concatenation(List(GroupToTrgps(G,Orders(S)),T->Shapes(T,S)));
	end
	);
InstallMethod( ShapeStr,
	[HasShape],
	S -> ShapeStr(Shape(S))
	);
	InstallMethod( ShapeStr,
	[IsList],
	S -> Concatenation("(",JoinStringsWithSeparator(
		List(S,sh->Concatenation(String(sh[1]),sh[2])),
		","),")")
	);
	InstallMethod( ShapeStrMlts,
	[HasShape],
	function(S)
  local mlt;
	mlt := function(i)
		if i = 1 then return "";
		else return Concatenation("^",String(i)); fi; end;
	return Concatenation("(",
		JoinStringsWithSeparator(List(Set(Shape(S)),s->
			Concatenation(Concatenation(List(s,String)),mlt(Count(Shape(S),t->t=s)))),"," ),")");
	end
	);
	InstallMethod( ShapeGraph,
	[HasShape],
	S -> PairsGraph(IncidencePairs(S),
		List(Shape(S),s->Concatenation(List(s,String))))
	);
InstallMethod( Description, "for a trgp with shape",
	[IsTrgp and HasShape],
	function( S )
	local t;
	ResetFilterObj(S,HasShape);
	t := Description(S);
	SetFilterObj(S,HasShape);
	return Concatenation(
		t,
		", shape ",
		ShapeStrMlts(S)
	);
	end
	);
	InstallMethod( PrintString,
	[HasShape],
	function( S )
	local txt;
	ResetFilterObj(S,HasShape);
	txt := PrintString(S);
	SetFilterObj(S,HasShape);
	Remove(txt);Remove(txt);
	txt := Concatenation(txt,
		",\n\t",PrintString(
			List([1..Length(Pairs(S))],i->[Pairs(S)[i],Shape(S)[i]])
		),"\n)");
	return txt;
	end
);
InstallMethod( ImagesSet,"for a transposition group with shape",
	[IsMapping,HasShape],SUM_FLAGS,
	function( f, S )
  return TranspositionGroup(
		Image(f),
		Image(f,Transpositions(S)),
		List([1..Length(Pairs(S))],i->[List(Pairs(S)[i],x->x^f),Shape(S)[i]])
	);
	end
);

InstallMethod( TranspositionGroup,
	[IsGroup,IsCollection,IsList],
	function( G, D, Sh )
	return TrgpNC(G,List(Orbits(G,D),Representative),Sh);
	end
	);
	InstallMethod( TrgpNC,
	[IsGroup,IsCollection,IsList],
	function( G, D, X )
	local T;
	T := TrgpNC( G, D );
	SetPairs(T,List(X,x->x[1]));
	SetShape(T,List(X,x->x[2]));
	return T;
	end
	);
InstallMethod( IsIsomOfShapes,
	[HasShape,HasShape,IsMapping],
	function( T,U,f )
	return ForAll(
		[1..Length(Shape(T))],
		i -> Shape(T)[i] = Shape(U)[
			FirstPosition(Pairs(U),
			u -> RepresentativeAction(
				U,
				u,Image(f,Pairs(T)[i]),
				OnSets) <> fail)]
		); end
	);
	InstallMethod( IsIsomOfShapes,
	[IsMapping],
	function( f )
	return IsIsomOfShapes(Source(f),Range(f),f); end
	);
InstallMethod( AllShapeIsomClasses,
	[HasShape,HasShape],
	function( T, U )
	if Sorted(Shape(T)) <> Sorted(Shape(U)) then return []; fi;
	return Filtered(IsomorphismClassesTrgps(T,U),f->IsIsomOfShapes(T,U,f) );
	end);
InstallMethod( AreIsomorphicShapes,
	[HasShape,HasShape],
	function( T, U )
	if Sorted(Shape(T)) <> Sorted(Shape(U)) then return false; fi;
	return ForAny(IsomorphismClassesTrgps(T,U),IsIsomOfShapes);
	end
);

InstallMethod( Subshape,
	[HasShape,IsTrgp],
	function( S, T )
	ResetFilterObj(T,HasShape);
	SetShape(T,
		List( Pairs(T),
			p -> Shape(S)[FirstPosition(Pairs(S),
			q -> RepresentativeAction(S,p,q,OnSets)<>fail)] ) );
	return T;
	end
	);
	InstallMethod( Subshape,
	[HasShape,IsGroup],
	function( R, H )
  local S;
	S := Subtrgp(R,H);
	if S = fail then return S;
	else return Subshape(R,S); fi; end
	);
InstallMethod( MaximalSubshapes,
	[HasShape],
	R -> List(
		Concatenation(
			MaximalSubtrposTrgp( R ),
			MaximalSubgroupsTrgp( R ) ),
		S -> Subshape( R, S ) )
	);
InstallMethod( HasIsomorphicSubshape,
	[HasShape,HasShape],
	function( S, T )
	return ForAny(IsomorphicSubgroups(S,T),
		function(f)
			local s;
			s := Subshape(S,Image(f));
			if s = fail then return false;
			else return AreIsomorphicShapes(s,T); fi; end );
end
);

InstallMethod( AutomorphismGroup,
	[HasShape],
	S -> Subgroup(AutomorphismGroup(S),
	Filtered(AutomorphismGroup(S),
		a -> ForAll([1..Length(Pairs(S))], i ->
		Shape(S)[i] = Shape(S)[First([1..Length(Pairs(S))], j ->
		RepresentativeAction(S,OnSets(Pairs(S)[i],a),Pairs(S)[j],OnSets)<>fail )]) ))
);

