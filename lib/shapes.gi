
#
#  shapes implementation
#

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
		local res, j, cc, c;
		sh := ShallowCopy(sh);
		sh[i] := cl;
		res := [];
		for j in Filtered(subs(i),j->IsInt(sh[j])) do
			cc := Filtered(SubAlgebras(S,cl),a->a[1]=sh[j]);
			if IsEmpty(cc) then return []; fi;
			for c in cc do Append(res,PropCh( sh, j, c )); od; od;
		for j in Filtered(sups(i),j->IsInt(sh[j])) do
			cc := Filtered(SupAlgebras(S,cl),a->a[1]=sh[j]);
			if IsEmpty(cc) then return []; fi;
			for c in cc do Append(res,PropCh( sh, j, c )); od; od;
		if IsEmpty(res)
		then return [sh];
		else return res; fi;
	end;
	while not IsEmpty(wip) do
		sh := Remove(wip);
		j := FirstPosition(sh,IsInt);
		for sh2 in Concatenation(List(GetAlgebras(S,sh[j]),cl->PropCh(sh,j,cl))) do
			if ForAny(sh2,IsInt) then Add(wip,sh2);
			else Add(res,sh2); fi;
		od;
	od;
	permOnPairs := function(g)
		local targets;
		targets := [1..Length(Pairs(T))];
		return PermListList( [1..Length(Pairs(T))],
			List([1..Length(Pairs(T))], i ->
			First(targets,function(t)
				if RepresentativeAction( GroupX(T),
					OnSets(Pairs(T)[i],g),Pairs(T)[t],OnSets ) <> fail
				then targets := Difference(targets,[t]); return true;
				else return false; fi;
				end )) );
		end;
	return List(
		OrbitsDomain(
			Group(List(GeneratorsOfGroup(AutomorphismGroup(T)),permOnPairs)),
			res,
			Permuted ),
		function(sh)
		local S;
		S := TrgpNC(GroupX(T),Transpositions(T));
		SetShape(S,Representative(sh));
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
	S -> Concatenation("(",JoinStringsWithSeparator(
		List(Shape(S),sh->Concatenation(String(sh[1]),sh[2])),
		", "),")")
	);
	InstallMethod( ShapeStrMlts,
	[HasShape],
	function(S)
  local mlt;
	mlt := function(i)
		if i = 1 then return "";
		else return Concatenation("^",String(i)); fi; end;
	return Concatenation("(",
		JoinStringsWithSeparator(List(Set(S),s->Concatenation(s,mlt(Count(S,t->t=s)))),", " ),")");
	end
);
InstallMethod( ViewObj,
	[HasShape],
	function( S )
	Print(
		ViewString(GroupX(S)),
		" with ",StringTrpoClasses@trgps(S), " trpos,",
		" shape ",ShapeStr(S)
		); end
);

InstallMethod( IsIsomOfShapes,
	[HasShape,HasShape,IsMapping],
	function( T,U,f )
	return ForAll(
		[1..Length(Shape(T))],
		i -> Shape(T)[i] = Shape(U)[
			FirstPosition(Pairs(U),
			u -> RepresentativeAction(
				GroupX(U),
				u,Image(f,Pairs(T)[i]),
				OnSets) <> fail)]
		); end
	);
InstallMethod( AllShapeIsomClasses,
	[HasShape,HasShape],
	function( T, U )
	if Sorted(Shape(T)) <> Sorted(Shape(U)) then return []; fi;
	return Filtered(IsomorphismClassesTrgps(T,U),f->IsIsomOfShapes(T,U,f) );
	end);
InstallMethod( HasIsomSubshape,
	[HasShape,HasShape],
	function( T, U )
	if Sorted(Shape(T)) <> Sorted(Shape(U)) then return false; fi;
	return ForAny(IsomorphismClassesTrgps(T,U),f->IsIsomOfShapes(T,U,f) );
	end
);

InstallMethod( Subshape,
	[HasShape,IsTrgp],
	function( S, T )
	SetShape(T,
		List( Pairs(T),
			p -> Shape(S)[FirstPosition(Pairs(S),
			q -> RepresentativeAction(GroupX(S),p,q,OnSets)<>fail)] ) );
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
	return ForAny(IsomorphicSubgroups(GroupX(S),GroupX(T)),
		function(f)
			local s;
			s := Subshape(S,Image(f));
			if s = fail then return false;
			else return HasIsomSubshape(s,T); fi; end );
end
);

InstallMethod( AutomorphismGroup,
	[HasShape],
	S -> Subgroup(AutomorphismGroup(S),
	Filtered(AutomorphismGroup(S),
		a -> ForAll([1..Length(Pairs(S))], i ->
		Shape(S)[i] = Shape(S)[First([1..Length(Pairs(S))], j ->
		RepresentativeAction(GroupX(S),OnSets(Pairs(S)[i],a),Pairs(S)[j],OnSets)<>fail )]) ))
);

