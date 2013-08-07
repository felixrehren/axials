
#
#	create implementation
#

InstallValue( MrepHelper@,
	rec(
		getSubreps := function( T,G,th )
			local sr, ss, rr, misspos, prespos, ans, m, s, ff;

			sr := [];
			ss := MaximalSubshapes(T);
			rr := List(ss,s->GetMrep(s,th));
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
					FindMreps(List(misspos,m->AsSmallerPermTrgp(ss[m])));
					for m in misspos
					do rr[m] := GetMrep(ss[m],th); od;
				elif ans = 3 or ans = 4 then
					misspos := Difference([1..Length(ss)],misspos);
					if ans = 3 then
						for s in ss{misspos}
						do Append(sr, MrepHelper@.getSubreps(s,G)); od;
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
					RecursiveSorted(Recursive(y->~.canonSetPos(ss,y))(x)) );
			else return ss[~.canonSetPos(ss,x)]; fi;
			end
	, inSubrep := function( R, S )
			local tt, bb, alph, dict, s, A, rr, c, pos, emb, al, pstnsR, elmtsS, i, j, v, NewRep;
			tt := Difference(S!.ss,Alphabet(R));
			bb := Concatenation(R!.ss,tt);
			alph := MrepHelper@.closedAlphabet(GroupX(R),bb);
			dict := NewDictionary(false,true,alph);
			for s in Alphabet(R) do AddDictionary(dict,s,R!.map(s)); od;
			A := Alg(R);
			rr := [];

			for c in List( RightTransversal(GroupX(R),GroupX(S)),
								t -> ConjugatorIsomorphism(GroupX(R),t) ) do
				tt := Difference((S!.ss)^c,~.closedAlphabet(GroupX(R),bb));
				bb := Concatenation(bb,List(tt,t->~.canonRep(R,t)));
				A := MalgHelper@.incBasis(A,Length(tt));

				pos := List((S!.ss)^c,s->Position(bb,~.canonSet(bb,s)));
				emb := List( [1..Dimension(S)], i -> Basis(A)[pos[i]] );
				for s in ~.closedAlphabet(GroupX(R),tt) do
					AddDictionary(dict,s,S!.map(s)*emb); od;

				al := Set(List(Alphabet(S),s->MrepHelper@.canonRep(R,s^c)));
				pstnsR := FilteredPositions(bb,s->All(Recursive(x->x in al)(s)));
				elmtsS := List(pstnsR,i->
					S!.map(Recursive(x->First(Alphabet(S),a->a^c=x))(bb[i])) );

				for i in [1..Length(pstnsR)] do
					for j in [i..Length(pstnsR)] do
						v := mult(S,elmtsS[i],elmtsS[j])*emb;
						if IsBound(R!.mt[pstnsR[i]][pstnsR[j]])
						then Add(rr,R!.mt[pstnsR[i]][pstnsR[j]] - v);
						else R!.mt[pstnsR[i]][pstnsR[j]] := v;
								 R!.mt[pstnsR[j]][pstnsR[i]] := v; fi;
					od;
				od;
			od;
			NewRep := ~.makeRep( Mtheory(R), Trgp(R), A, s->LookupDictionary(dict,s), bb );
			SetAlphabet(NewRep,alph);
			AddRelations(Alg(NewRep),
				Relations(Alg(R)) + Subspace(Basis(NewRep),rr));
			return NewRep;
			end
	)
);

InstallMethod( Mrep,
	[IsMtheory,IsTrgp,IsMalg,IsFunction,IsList],
	function( Th, T, A, f, ss )
	return Objectify( 
		TypeMrep@,
		rec(
			Mtheory := Th,
			trgp := T,
			Alg := A,
			map := f,
			ss := ss,
			act := function(om,g)
				local nz, ws;
				if IsZero(om) then return om; fi;
				nz := Filtered([1..Length(om)],i->not IsZero(om[i]));
				ws := List(Concatenation(~.basis){nz},w->OnPointsRecursive(w,g));
				return Sum([1..Length(nz)],i->om[nz[i]]*~.map(ws[i]));
				end
		) );
	end
	);
	InstallMethod( Mrep,
	[IsMtheory,IsTrgp,IsMalg,IsList,IsList],
	function( Th, T, A, f, ss )
		local dict, i;
		dict := NewDictionary(false,true,List(f,x->x[1]));
		for i in [1..Length(f)]
		do AddDictionary(dict,f[i][1],f[i][2]); od;
		return Mrep( Th, T, A, x -> LookupDictionary(dict,x), ss );
	end
);

InstallMethod( Alg,
	[IsMrep],
	R -> R!.Alg
	);
	InstallMethod( Trgp,
	[IsMrep],
	R -> R!.trgp
	);
	InstallMethod( GroupX,
	[IsMrep],
	R -> GroupX(Trgp(R))
	);
	InstallMethod( Basis,
	[IsMrep],
	R -> Basis(R!.V)
	);
	InstallMethod( Alphabet,
	[IsMrep],
	R -> MrepHelper@.closedAlphabet(GroupX(R),R!.ss)
	);
	InstallMethod( Mtheory,
	[IsMrep],
	R -> R!.Mtheory
);

InstallMethod( ViewString,
	[IsMrep],
	A -> Concatenation(
		"an M-rep of ",ViewString(Trgp(A)),
		" on ", ViewString(Alg(A))
		)
	);
InstallMethod( PrintString,
	[IsMrep],
	R -> Concatenation(
		"Mrep(\n",
		"\t",PrintString(Mtheory(R)),",\n",
		"\t",PrintString(Trgp(R)),",\n",
		"\t",PrintString(Alg(R)),",\n",
		"\t",String(List(Alphabet(R),a->[a,R!.map(a)])),",\n",
		"\t",PrintString(R!.ss),"\n",
		")"
	)
);

InstallMethod( ImageX,
	[IsMapping,IsMrep],
	function( f, R )
	return Mrep(
		Mtheory(R),
		ImageX(f,Trgp(R)),
		ImageX(f,Alg(R)), ### this part! no
		t -> ImageX(f,AlgEmbed(R,InverseImage(f,t))), ## obv needs doin'
		Image(f,R!.ss)
	);
	end
);

InstallMethod( Dimension,
	[IsMrep],
	R -> Dimension(Alg(R))
	);

InstallMethod( StartMrep,
	[HasShape, IsMtheory],
	function( T, Mth )
	local A, ss, dict, R, sr, s, i;
	A := MalgHelper@.emptyMalg(
		Sum(Transpositions(T),t->OrbitLength(GroupX(T),t)) );
	ss := Immutable(Union(List(Transpositions(T),t->Orbit(GroupX(T),t))));
	ss := Sorted(ss); # how to make use of sortedness?
	dict := CreateDictionary(ss,s->Basis(A)[Position(ss,s)]);
	R := Mrep( Mth, T, A, t->LookupDictionary(dict,t), ss );

	sr := MrepHelper@.getSubreps(T,GroupX(T),Mth);
	for s in sr do R := MrepHelper@.inSubrep( R, s ); od;

	for i in [1..Length(ss)]
	do A!.mt[i][i] := Basis(A)[i]; od;
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

InstallMethod( FindMrep,
	[HasShape,IsMtheory],
	function(a,b)
	return fail;
	end
	);
