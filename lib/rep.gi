
#
#	create implementation
#

InstallValue( AxialRepHelper@,
	rec(
		getSubreps := function( T,G,th )
			local sr, ss, rr, misspos, prespos, ans, m, s, ff;

			sr := [];
			ss := MaximalSubshapes(T);
			rr := List(ss,s->GetAxialRep(s,th));
			misspos := FilteredPositions(rr,r->r=fail);
			prespos := FilteredPositions(rr,r->r<>fail);

			if ForAny(rr{prespos},IsTrivial) then
				Info(mai,"nonexistent subAlgebras\n",
					JoinStringsWithSeparator(List(Filtered(rr{prespos},IsTrivial),ViewString),",\n"));
				return fail; fi;

			if not IsEmpty(misspos) then
				ans := UserChoice( Concatenation(
						"missing Algebras for\n",
						JoinStringsWithSeparator(List(ss{misspos},ViewString),",\n"),"\n",
						"what would you like to do?\n",
						"1 = quit, ",
						"2 = find all, ",
						"3 = ignore & try subgroups, ",
						"4 = ignore & continue"
					),
					[1..4]
				);
				if ans = 1 then return fail;
				elif ans = 2 then
					FindAxialReps(List(misspos,m->AsSmallerPermTrgp(ss[m])));
					for m in misspos
					do rr[m] := GetAxialRep(ss[m],th); od;
				elif ans = 3 or ans = 4 then
					misspos := Difference([1..Length(ss)],misspos);
					if ans = 3 then
						for s in ss{misspos}
						do Append(sr, AxialRepHelper@.getSubreps(s,G)); od;
					fi;
					ss := ss{misspos};
					rr := rr{misspos};
				fi;
			fi;
			
			ff := List([1..Length(rr)],i->AllShapeIsomClasses(rr[i],ss[i]));
			Assert(1,ForAll(ff,f->ForAll(f,g->g^G =f[1]^G)),
				"we only want one homomorphism up to G, otherwise need extra methods to deal with this"); # e.g. L3(3)?
			ff := List(ff,Representative);
			Append(sr,List([1..Length(rr)],i->ImageX(rr[i],ff[i])));
			return sr;
			end
	,	closedAlphabet := function(G,aa)
			local ff, f, n;
			ff := Filtered(aa,s->not IsList(s));
			for f in ShallowCopy(ff) do
				for n in [1..Order(f)-1]
				do Add(ff,f^n); od;
			od;
			return Union(Orbits(G,ff));
			end
	, canonRep := function( R, x )
			if IsList(x) then
				return Recursive(i->Basis(R)[i])(
					RecursiveSorted(Recursive(y->LastNonzeroPos(R!.map(y)))(x)) );
			else return Basis(R)[LastNonzeroPos(R!.map(x))]; fi;
			end
	,	canonSetPos := function( ss, x )
			local powers;
			powers := List([1..Order(x)-1],n->x^n);
			return First(ss,s->s in powers);
			end
	,	canonSet := function( ss, x )
			if IsList(x) then
				return Recursive(i->ss[i])(
					RecursiveSorted(Recursive(y->AxialRepHelper@.canonSetPos(ss,y))(x)) );
			else return ss[AxialRepHelper@.canonSetPos(ss,x)]; fi;
			end
	, inSubrep := function( R, S )
			local tt, bb, alph, dict, s, A, rr, c, pos, emb, al, pstnsR, elmtsS, i, j, v, NewRep;
			tt := Difference(S!.ss,Alphabet(R));
			bb := Concatenation(R!.ss,tt);
			alph := AxialRepHelper@.closedAlphabet(Trgp(R),bb);
			dict := NewDictionary(false,true,alph);
			for s in Alphabet(R) do AddDictionary(dict,s,R!.map(s)); od;
			A := Alg(R);
			rr := [];

			for c in List( RightTransversal(Trgp(R),Trgp(S)),
								t -> ConjugatorIsomorphism(Trgp(R),t) ) do
				tt := Difference((S!.ss)^c,AxialRepHelper@.closedAlphabet(Trgp(R),bb));
				bb := Concatenation(bb,List(tt,t->AxialRepHelper@.canonRep(R,t)));
				A := AlgHelper@.incBasis(A,Length(tt));

				pos := List((S!.ss)^c,s->Position(bb,AxialRepHelper@.canonSet(bb,s)));
				emb := List( [1..Dimension(S)], i -> Basis(A)[pos[i]] );
				for s in AxialRepHelper@.closedAlphabet(Trgp(R),tt) do
					AddDictionary(dict,s,S!.map(s)*emb); od;

				al := Set(List(Alphabet(S),s->AxialRepHelper@.canonRep(R,s^c)));
				pstnsR := FilteredPositions(bb,s->All(Recursive(x->x in al)(s)));
				elmtsS := List(pstnsR,i->
					S!.map(Recursive(x->First(Alphabet(S),a->a^c=x))(bb[i])) );

				for i in [1..Length(pstnsR)] do
					for j in [i..Length(pstnsR)] do
						v := Mult(S)(elmtsS[i],elmtsS[j])*emb;
						if IsBound(R!.mt[pstnsR[i]][pstnsR[j]])
						then Add(rr,R!.mt[pstnsR[i]][pstnsR[j]] - v);
						else R!.mt[pstnsR[i]][pstnsR[j]] := v;
								 R!.mt[pstnsR[j]][pstnsR[i]] := v; fi;
					od;
				od;
			od;
			NewRep := AxialRepHelper@.makeRep( Fusion(R), Trgp(R), A, s->LookupDictionary(dict,s), bb );
			SetAlphabet(NewRep,alph);
			AddRelations(Alg(NewRep),
				Relations(Alg(R)) + Subspace(Basis(NewRep),rr));
			return NewRep;
			end
	)
);

InstallMethod( AxialRep,
	[IsFusion,IsTrgp,IsAlg,IsDictionary,IsList],
	function( Th, T, A, d, ss )
	local map;
	map := function(x)
		if IsList(x) then return Mult(A)(map(x[1]),map(x[2]));
		else return LookupDictionary(d,x); fi; end;
	return Objectify( 
		TypeAxialRep@,
		rec(
			Fusion := Th,
			trgp := T,
			Alg := A,
			map := map,
			ss := ss,
			act := function(om,g)
				local nz, ws;
				if IsZero(om) then return om; fi;
				nz := Filtered([1..Length(om)],i->not IsZero(om[i]));
				ws := List(ss{nz},w->OnPointsRecursive(w,g));
				return Sum([1..Length(nz)],i->om[nz[i]]*map(ws[i]));
				end
		) );
	end
	);
	InstallMethod( AxialRep,
	[IsFusion,IsTrgp,IsAlg,IsList,IsList],
	function( Th, T, A, f, ss )
		local dict, i;
		dict := NewDictionary(false,true,List(f,x->x[1]));
		for i in [1..Length(f)]
		do AddDictionary(dict,f[i][1],f[i][2]); od;
		return AxialRep( Th, T, A, x -> LookupDictionary(dict,x), ss );
	end
);

InstallMethod( Alg,
	[IsAxialRep],
	R -> R!.Alg
	);
	InstallMethod( Trgp,
	[IsAxialRep],
	R -> R!.trgp
	);
	InstallMethod( Basis,
	[IsAxialRep],
	R -> Basis(R!.V)
	);
	InstallMethod( Alphabet,
	[IsAxialRep],
	R -> AxialRepHelper@.closedAlphabet(Trgp(R),R!.ss)
	);
	InstallMethod( Fusion,
	[IsAxialRep],
	R -> R!.Fusion
	);
	InstallMethod( Axes,
	[IsAxialRep],
	function( R )
	SetAxes( Alg(R),
		List( Transpositions(Trgp(R)),t->
			Axis(Alg(R),R!.map(t),Fusion(R),t,x->R!.act(x,t)) ) );
	return Axes( Alg(R) );
	end
);

InstallMethod( ViewString,
	[IsAxialRep],
	A -> Concatenation(
		"an M-rep of ",ViewString(Trgp(A)),
		" on ", ViewString(Alg(A))
		)
	);
InstallMethod( PrintString,
	[IsAxialRep],
	R -> Concatenation(
		"AxialRep(\n",
		"\t",PrintString(Fusion(R)),",\n",
		"\t",PrintString(Trgp(R)),",\n",
		"\t",PrintString(Alg(R)),",\n",
		"\t",String(List(Alphabet(R),a->[a,R!.map(a)])),",\n",
		"\t",PrintString(R!.ss),"\n",
		")"
	)
);

InstallMethod( ImageX,
	[IsMapping,IsAxialRep],
	function( f, R )
	return AxialRep(
		Fusion(R),
		ImageX(f,Trgp(R)),
		ImageX(f,Alg(R)), ### this part! no
		t -> fail, # ImageX(f,AlgEmbed(R,InverseImage(f,t))), ## obv needs doin'
		Image(f,R!.ss)
	);
	end
);

InstallMethod( Dimension,
	[IsAxialRep],
	R -> Dimension(Alg(R))
	);

InstallMethod( IncreaseClosure,
	[IsAxialRep],
	function( R )
	local A, ss, n, mt, i, j, z;
	A := Alg(R);
	if not HasClosure(A) then SetClosure(A,Rationals^Dimension(A)); fi;
	ss := R!.ss;
	n := Dimension(Closure(A));
	mt := List([1..n],i->[]);
	for i in [1..n] do
		for j in [1..i] do # lower-triangular
			if IsBound(A!.MT[i]) and IsBound(A!.MT[i][j])
			then mt[i][j] := A!.MT[i][j];
			else
				n := n+1;
				Add(ss,ss{[i,j]});
				mt[i][j] := KroneckerVector(n,n);
			fi;
		od;
	od;
	z := List([1..n],i->0);
	for i in [1..Dimension(Closure(A))] do for j in [1..i]
	do mt[i][j] := mt[i][j] + z; od; od;

	return AxialRep( Fusion(R), Trgp(R), 
		Alg( Dimension(Closure(A)), n, mt ),
		CreateDictionary(Alphabet(R),a->R!.map(a)+z), ss );
	end
);


InstallMethod( StartAxialRep,
	[HasShape, IsFusion],
	function( T, Mth )
	local dim, mt, i, A, ss, dict, R, sr, s;
	dim := Sum(Transpositions(T),t->OrbitLength(T,t));
	mt := List([1..dim],i -> []);
	for i in [1..dim] do mt[i][i] := KroneckerVector(i,dim); od;
	A := Alg(dim,mt);
	ss := Immutable(Union(List(Transpositions(T),t->Orbit(T,t))));
	ss := Sorted(ss); # how to make use of sortedness?
	dict := CreateDictionary(ss,s->Basis(A)[Position(ss,s)]);
	R := AxialRep( Mth, T, A, dict, ss );

	sr := AxialRepHelper@.getSubreps(T,T,Mth);
	for s in sr do R := AxialRepHelper@.inSubrep( R, s ); od;

	return R;
	end
);

#	if not IsBound(MajAlgCore) then MajAlgCore := IdFunc; fi;
#	PlusTheClosure := function( R )
#	  local S, rr, v, time, ar, i, j;
#		S := MajAlgCore(R);
#		S.SymbolicSS := [Concatenation(R.SymbolicSS),[]];
#		rr := [];
#		for i in [Dimension(R.V)+1..Dimension(R.W)] do
#			S.MT[i] := []; S.FT[i] := []; od;
#		for i in [1..Dimension(R.W)] do
#			for j in [i..Dimension(R.W)] do
#				if j > Dimension(R.V) or not IsBound(R.MT[i][j]) then
#					Add(S.SymbolicSS[2],S.SymbolicSS[1]{[i,j]});
#					v := Dimension(R.W)+Length(S.SymbolicSS[2]);
#					v := SOB(v,v);
#					S.MT[i][j] := v;
#					S.MT[j][i] := v;
#				fi;
#		od;od;
#		SetMajBasisFns(S);
#		for i in [1..Dimension(S.V)] do for j in [1..Dimension(S.V)] do
#			S.MT[i][j] := S.MT[i][j] + Zero(S.W); od; od;
#		SetMajTblFns(S);
#		rr := List(rr,r->r+Zero(S.W));
#		Info(Mai,5,"increased closure: dim ",PrintAlgDim(S));
#	
#		SetWordInAlg( S,
#			CreateDictionary(
#				MakeAlphabet(S),
#				x -> R.WordInAlg(x) + Zero(S.W) ) );
#	
#		if IsBound(R.Reps.EigSps) and not IsEmpty(R.Reps.EigSps) then
#			time := Runtime();
#			ar := AddRel(S.Rels,Concatenation(List(
#				[1..Length(R.Reps.Transpositions)],
#				function(i) local a;
#					a := S.WordInAlg(S.Reps.Transpositions[i]);
#					return Concatenation(List([1..4], j ->
#						List( R.Reps.EigSps[i][j],x->S.mult(a,x+Zero(S.W))-MajEV[j]*x ) ));
#				end
#			)));
#			Info(Mai,4,"known eigvectors give +",ar," rels (",ElapseStr(time),")");
#			return UseRels(S);
#		else return S; fi;
#	end;

InstallMethod( FindAxialRep,
	[HasShape,IsFusion],
	function(a,b)
	return fail;
	end
	);

InstallMethod( IdealClosure,
	[IsAxialRep,IsVectorSpace],
	function( R, V )
	return CloseUnder( V, Trgp(R), R!.act, R!.V, Mult(R) );
	end
	);
