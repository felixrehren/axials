
#
#	create implementation
#

InstallValue( AxialRepHelper@, rec(
	getSubreps := function( T,G,th,field )
			local sr, ss, rr, misspos, prespos, ans, m, s, ff;

			sr := [];
			ss := MaximalSubshapes(T);
			rr := List(ss,s->GetAxialRep(th,s));
			rr := List(rr,function(r) local s;
				if r = [] then return r;
				else s := ChangeField(r,field);
					if s = fail then return []; else return s; fi;
				fi; end);
			misspos := FilteredPositions(rr,r->r=[]);
			prespos := FilteredPositions(rr,r->r<>[]);

			if ForAny(rr{prespos},IsTrivial) then
				Info(AxRepInfo,"nonexistent subAlgebras\n",
					JoinStringsWithSeparator(List(Filtered(rr{prespos},IsTrivial),Description),",\n"));
				return fail; fi;

			if not IsEmpty(misspos) then
				ans := UserChoice( Concatenation(
						"missing algebras for\n",
						JoinStringsWithSeparator(List(ss{misspos},Description),",\n"),"\n",
						"what would you like to do?\n",
						"1 = quit, ",
						"2 = find all, ",
						"3 = continue without"
					),
					[1..4]
				);
				if ans = 1 then return fail;
				elif ans = 2 then
					for m in misspos
					do rr[m] := FindAxialRep(ss[m],th); od;
				elif ans = 3 or ans = 4 then
					misspos := Difference([1..Length(ss)],misspos);
					if ans = 3 then
						for s in ss{misspos}
						do Append(sr, AxialRepHelper@.getSubreps(s,G,th,field)); od;
					fi;
					ss := ss{misspos};
					rr := rr{misspos};
				fi;
			fi;
			
			ff := List([1..Length(rr)],i->AllShapeIsomClasses(Trgp(rr[i]),ss[i]));
			Assert(1,ForAll(ff,f->ForAll(f,g->g^G =f[1]^G)),
				"we only want one homomorphism up to G, otherwise need extra methods to deal with this"); # e.g. L3(3)?
			ff := List(ff,Representative);
			Append(sr,List([1..Length(rr)],i->Im(ff[i],rr[i])));
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
				return Recursive(i->Basis(Alg(R))[i])(
					RecursiveSorted(Recursive(y->LastNonzeroPos(R!.map(y)))(x)) );
			else return Basis(Alg(R))[LastNonzeroPos(R!.map(x))]; fi;
			end
	,	canonSetPos := function( ss, x )
			local powers;
			powers := List([1..Order(x)-1],n->x^n);
			return FirstPosition(ss,s->s in powers);
			end
	,	canonSet := function( ss, x )
			local powers, f;
			if IsList(x) then
				return Recursive(i->ss[i])(
					RecursiveSorted(Recursive(y->AxialRepHelper@.canonSetPos(ss,y))(x)) );
			else
				powers := List([1..Order(x)-1],n->x^n);
				f := First(ss,s->s in powers);
				if f = fail then return x;
				else return f; fi;
			fi;
			end
	, inSubrep := function( R, S, sym )
			local tt, bb, alph, dict, s, A, mt, i, rr, c, pos, emb, al, pstnsR, elmtsS, j, v, NewRep;
			tt := Difference(List(SpanningWords(S),s->AxialRepHelper@.canonSet(Alphabet(R),s)),Alphabet(R));
			bb := Concatenation(SpanningWords(R),tt);
			alph := AxialRepHelper@.closedAlphabet(Trgp(R),bb);
			dict := NewDictionary(false,true,alph);
			for s in Alphabet(R) do AddDictionary(dict,s,R!.map(s)); od;
			A := Alg(R);
			mt := List(A!.MT,ShallowCopy);
			for i in [Length(SpanningWords(R))+1..Length(bb)]
			do mt[i] := []; od;
			rr := [];

			for c in List( RightTransversal(Trgp(R),Trgp(S)),
								t -> ConjugatorIsomorphism(Trgp(R),t) ) do
				tt := Difference( 
					List(Recursive(s->s^c)(SpanningWords(S)),
						t->AxialRepHelper@.canonSet(bb,t)),
					bb );
				bb := Concatenation(bb,tt);
				A := LeftActingDomain(A)^Length(bb);
				for i in [Length(bb)-Length(tt)+1..Length(bb)]
				do mt[i] := []; od;

				pos := List(Recursive(s->s^c)(SpanningWords(S)),
					s->Position(bb,AxialRepHelper@.canonSet(bb,s)));
				emb := List( [1..Dimension(Alg(S))], i -> Basis(A)[pos[i]] );
				for s in Alphabet(S) do
					if LookupDictionary(dict,s^c) = fail
					then AddDictionary(dict,s^c,S!.map(s)*emb);
					else Add(rr,LookupDictionary(dict,s^c)-S!.map(s)*emb); fi;
				od;

				al := Set(List(Alphabet(S),s->AxialRepHelper@.canonSet(Alphabet(R),s^c)));
				pstnsR := FilteredPositions(bb,s->All(Recursive(x->x in al)(s)));
				elmtsS := List(pstnsR,i->
					S!.map(Recursive(x->First(Alphabet(S),a->a^c=x))(bb[i])) );

				for i in [1..Length(pstnsR)] do
					for j in [1..i] do
						v := Mult(Alg(S))(elmtsS[i],elmtsS[j])*emb;
						if IsBound(mt[pstnsR[i]][pstnsR[j]])
						then Add(rr,mt[pstnsR[i]][pstnsR[j]] - v);
						else mt[pstnsR[i]][pstnsR[j]] := v; fi;
					od;
				od;
			od;
			A := AlgHelper@.incBasis(Alg(A,mt),0);
			NewRep := AxialRep( Fusion(R), Trgp(R), Alg(A,mt), dict, bb );
			SetAlphabet(NewRep,alph);
			rr := Subspace(A,List(rr,r->r+Zero(A)));
			if HasRelations(Alg(R))
			then SetRelations(Alg(NewRep),rr+Subspace(Closure(Alg(NewRep)),List(Basis(Relations(Alg(R))),b->b+Zero(Alg(NewRep))),Zero(Alg(NewRep))));
			else SetRelations(Alg(NewRep),rr); fi;
			return NewRep;
			end
	, startAxialRep :=	function( T, fus, sym )
			local dim, mt, i, A, ss, dict, R, sr, s;
			dim := Sum(Transpositions(T),t->OrbitLength(T,t));
			mt := List([1..dim],i -> []);
			for i in [1..dim] do mt[i][i] := KroneckerVector(i,dim); od;
			if IsField(ValueOption("field"))
			then mt := mt*One(ValueOption("field")); fi;
			A := Alg(dim,mt);
			ss := Immutable(Union(List(Transpositions(T),t->Orbit(T,t))));
			ss := Sorted(ss); # how to make use of sortedness?
			dict := CreateDictionary(ss,s->Basis(A)[Position(ss,s)]);
			R := AxialRep( fus, T, A, dict, ss );
			SetSymmetries(R,sym);

			sr := AxialRepHelper@.getSubreps(T,sym,fus,LeftActingDomain(A));
			if sr = fail then return fail; fi;
			for s in sr do R := AxialRepHelper@.inSubrep( R, s, sym ); od;

			return R;
			end
	)
);

InstallMethod( AxialRep,
	[IsFusion,IsTrgp,IsAlg,IsDictionary,IsList],
	function( Th, T, A, d, ss )
	local map, R;
	map := function(x)
		if IsList(x) then return Mult(A)(map(x[1]),map(x[2]));
		else return LookupDictionary(d,x); fi; end;
	R := rec(
		map := map,
		act := function(om,g)
			local nz, ws;
			if IsZero(om) then return om; fi;
			nz := Filtered([1..Length(om)],i->not IsZero(om[i]));
			ws := List(ss{nz},w->OnPointsRecursive(w,g));
			return Sum([1..Length(nz)],i->om[nz[i]]*map(ws[i]));
			end
	);
	ObjectifyWithAttributes(
		R, TypeAxialRep@,
		Fusion, Th,
		Trgp, T,
		Alg, A,
		SpanningWords, ss
	);
	return R;
	end
	);
	InstallMethod( AxialRep,
	[IsFusion,IsTrgp,IsAlg,IsList,IsList],
	function( Th, T, A, f, ss )
		local dict, i;
		dict := NewDictionary(false,true,List(f,x->x[1]));
		for i in [1..Length(f)]
		do AddDictionary(dict,f[i][1],f[i][2]); od;
		return AxialRep( Th, T, A, dict, ss );
	end
	);
	InstallMethod( IsTrivial,
	[IsAxialRep],
	R -> IsTrivial(Alg(R))
);

InstallMethod( Symmetries,
	[IsAxialRep],
	R -> Trgp(R)
	);
	InstallMethod( IsTrivial,
	[IsAxialRep],
	R -> IsTrivial(Alg(R))
);

InstallMethod( Alphabet,
	[IsAxialRep],
	R -> AxialRepHelper@.closedAlphabet(Trgp(R),SpanningWords(R))
	);
	InstallMethod( InWords,
	[IsAxialRep],
	function(R)
		local f;
		f := function(w)
			if IsList(w)
			then return Concatenation("(",f(w[1]),"*",f(w[2]),")");
			else return String(w); fi; end;
		return w -> JoinStringsWithSeparator(
			List(FilteredPositions(w,x->not IsZero(x)),
				function(i) local s, rat, rep, c;
					rat := InField(w[i]);
					if rat = fail then
						rep := ExtRepPolynomialRatFun(w[i]);
						if SignInt(rep[Length(rep)]) = 1 then s := "+";
						else s := ""; fi;
						c := "";
					else
						if SignInt(rat) = 1 then s := "+";
						else s := ""; fi;
						if IsOne(rat) then c := "";
						else c := String(rat); fi;
					fi;
					return Concatenation(
						s,
						c,
						f(SpanningWords(R)[i])
					); end),
			" ");
		end
	);
	InstallMethod( FromWord,
	[IsAxialRep],
	function(R)
		local f;
		f := function(w)
			if IsList(w) then return Mult(Alg(R))(f(w[1]),f(w[2]));
			else return R!.map(w); fi; end;
		return f;
		end
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
		"an axial rep of ",Description(Trgp(A)),
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
		"\t",PrintString(SpanningWords(R)),"\n",
		")"
	)
);

InstallMethod( Im, "image of an axial representation under gp hom",
	[IsMapping,IsAxialRep],
	function( f, R )
	return AxialRep(
		Fusion(R),
		Images(f,Trgp(R)),
		Alg(R),
		CreateDictionary(List(Alphabet(R),a->a^f),a->R!.map(PreImage(f,a))),
		List(SpanningWords(R),Recursive(l->Image(f,l)))
	);
	end
	);
InstallMethod( IncreaseClosure, "return axial rep considering longer words",
	[IsAxialRep],
	function( R )
	local time, A, ss, n, mt, i, j, z, B;
	time := Runtime();
	A := Alg(R);
	if not HasClosure(A) then SetClosure(A,LeftActingDomain(A)^Dimension(A)); fi;
	ss := ShallowCopy(SpanningWords(R));
	n := Dimension(Closure(A));
	mt := List([1..n],i->[]);
	for i in [1..n] do
		for j in [1..i] do # lower-triangular
			if IsBound(A!.MT[i]) and IsBound(A!.MT[i][j])
			then mt[i][j] := A!.MT[i][j];
			else
				n := n+1;
				Add(ss,ss{[j,i]});
				mt[i][j] := KroneckerVector(n,n)*One(LeftActingDomain(A));
			fi;
		od;
	od;
	z := [1..n]*Zero(LeftActingDomain(A));
	for i in [1..Dimension(Closure(A))] do for j in [1..i]
	do mt[i][j] := mt[i][j] + z; od; od;
	B := Alg( Dimension(Closure(A)), n, mt );
	InfoPro("increased mult table",time);

	AddRelations( B, Subspace(Closure(B),Concatenation(List(Filtered(Axes(R),HasEigenspaces),
		function(a)
		local evv, rr, i;
		evv := List(Eigenspaces(a),Basis);
		rr := [];
		for i in [1..Length(Fields(Fusion(a)))]
		do Append(rr,List(evv[i],v->Fields(Fusion(a))[i]*v-Mult(B)(v,Vector(a)))); od;
		return rr; end ))) );

	Info(AxRepInfo,3,"increased dim: ",Dimension(Closure(A)),"+",n-Dimension(Closure(A)));
	return AxialRep( Fusion(R), Trgp(R), B,
		CreateDictionary(Alphabet(R),a->R!.map(a)+z), ss );
	end
	);
InstallMethod( IdealClosure,
	[IsAxialRep,IsVectorSpace],
	function( R, V )
	return CloseUnder( V, Symmetries(R), R!.act, Alg(R), Alg(R) );
	end
	);
InstallMethod( Quotient,
	[IsAxialRep,IsVectorSpace],
	function( R, X )
	local Q, l, li, A;
	if IsTrivial(X) then return R; fi;
	Q := NaturalHomomorphismBySubspace( Closure(Alg(R)), X );
	if ForAny(Axes(R),a->Vector(a) in Kernel(Q))
	then return AxialRep(Fusion(R),Trgp(R),Alg(LeftActingDomain(Q)^0,[[]]),CreateDictionary([],IdFunc),[]); fi;
	l := AlgHelper@.quoBasisPos(Q);
	li := Intersection([1..Dimension(Alg(R))],l);
	A := Alg( Length(li), Length(l),
		List(li,i->List(Intersection([1..i],li),j->Image(Q,Alg(R)!.MT[i][j]))) );
	Info(AxRepInfo,3,"decreased dim: ",Dimension(A),"+",Dimension(Closure(A))-Dimension(A));
	return AxialRep( Fusion(R), Trgp(R), A,
		CreateDictionary(Alphabet(R),a->Image(Q,R!.map(a))),
		SpanningWords(R){l}
	);
	end
	);
InstallMethod( Subrepresentation,
	[IsAxialRep,IsGroup],
	function( R, H )
	local S;
	if IsSubgroup(Trgp(R),H)
	then return fail;
	### find subalgebra generated by R!.map(Intersection(H,Alphabet(R)))
	else
	### find subalgebra with additional symmetries H
		S := Quotient( R,IdealClosure( R,
			Subspace( Closure(Alg(R)),
				Concatenation(List( Basis(Alg(R)), b -> List(
					Orbit( H, b, R!.act ), o -> b-o ) )) ) ));
		SetSymmetries( S, H );
		return S;
	fi;
	end
);

InstallMethod( FindAxialRep,
	[HasShape,IsFusion,IsGroup,IsList],
	function(S,fus,sym,axioms)
		local time, R, step;
		time := Runtime();
		R := AxialRepHelper@.startAxialRep(S,fus,sym);
		if R = fail then return fail; fi;
		R := IncreaseClosure(R);
		step := function(R)
			local ax, a;
			if Alg(R) = Closure(Alg(R)) then return R; fi;
			if HasRelations(Alg(R)) and not IsTrivial(Relations(Alg(R)))
				then return step(Quotient(R,IdealClosure(R,Relations(Alg(R))))); fi;
			for ax in axioms do
				for a in Axes(R) do
					if not IsVector(Vector(a)) then Error(); fi;
					ax(a);
					if HasRelations(Alg(R)) and not IsTrivial(Relations(Alg(R)))
					then return step(R); fi;
			od; od;
			return step(IncreaseClosure(R));
		end;
		R := step(R);
		WriteAxialRep(R:overwrite:=false);
		Info(AxRepInfo,2,ElapseStr(time)," --- algebra found!");
		return R;
		end
		);
	InstallMethod( FindAxialRep,
		[HasShape,IsFusion],
		function(S,fus)
		return FindAxialRep(S,fus,S,[CheckLinearity,CheckDirectity]); end
		);
	InstallMethod( FindAxialRep,
		[IsGroup,IsSakuma,IsFusion],
		function(G,Sak,fus)
			if IsTrgp(G) then return List(Shapes(G,Sak),s->FindAxialRep(s,fus));
			else return Concatenation(List(
				GroupToTrgps(G,Orders(Sak)), t -> FindAxialRep(t,Sak,fus) )); fi;
		end
		);
	InstallMethod( FindUniversalAxialRep,
		[IsTrgp,IsFusion],
		function(T,fus)
		local sh;
		sh := List(Pairs(T),p->[Order(Product(p)),"U"]);
		if HasShape(T) then T!.Shape := sh; fi;
		SetShape(T,sh);
		return FindAxialRep(T,fus,AutomorphismGroup(T),[CheckLinearity,CheckDirectity]);
		end
	);
InstallMethod( FindForm,
	[IsAxialRep],
	function( R )
		local tail, A, time, ft, aa, pp, i, j, x, c, p, tails, y, pos, xg, a, eses, u, v, uv, old, new, r;
		tail := function(v)
			local u;
			u := ShallowCopy(v);
			u[LastNonzeroPos(u)] := Zero(LeftActingDomain(Alg(R)));
			return u; end;
		A := Alg(R);
		time := Runtime();
		c := 1;
		ft := List([1..Dimension(A)],j->[]);
		aa := Union(List(Transpositions(Trgp(R)),t->t^Trgp(R)));
		pp := FilteredPositions(SpanningWords(R),w->not IsList(w) and w in aa);
		for i in pp
		do ft[i][i] := 2*CentralCharge(Fusion(R)); od;
		for i in [1..Dimension(A)] do
			for j in [1..i] do
				if not IsBound(ft[i][j]) then
					x := Indeterminate(LeftActingDomain(Alg(R)),c);
					c := c + 1;
					for p in Orbit( Symmetries(R),Basis(A){[i,j]},function( om, g )
						return List(om,v->R!.act(v,g)); end ) do
						tails := List(p,tail);
						y := [Mult(A,LeftActingDomain(Alg(R)),ft)(p[1]-tails[1],tails[2]),
						 Mult(A,LeftActingDomain(Alg(R)),ft)(p[2]-tails[2],tails[1]),
						 Mult(A,LeftActingDomain(Alg(R)),ft)(tails[1],tails[2])];
						if ForAll(y,z->z<>fail) then
							pos := List(p,LastNonzeroPos);
							xg := (x - Sum(y))/(p[1][pos[1]]*p[2][pos[2]]);
							pos := Sorted(pos);
							ft[pos[2]][pos[1]] := xg;
						fi;
					od;
				fi;
			od;
		od;
		InfoPro("built indeterminate form",time); time := Runtime();

		old := [];
		for a in Axes(R) do
			for eses in Combinations(Eigenspaces(a),2) do
				for u in Basis(eses[1]) do
					for v in Basis(eses[2]) do
						Add(old,[u,v]);
					od;
				od;
			od;
		od;
		while true do
			c := Length(old);
			new := [];
			for uv in old do
				r := AlgHelper@.relToFn(Mult(A,LeftActingDomain(A),ft)(uv[1],uv[2]));
				if r = fail then Error("alg does not exist??");
				elif r = false then Add(new,uv);
				else ft := r(ft); fi;
			od;
			if Length(new) = c then break; fi;
			old := new;
		od;
		InfoPro("solved form by perps",time);

		SetFT(A,ft);
		end
	);

InstallMethod( Explode,
	[IsAxialRep],
	function( R )
	local a, II;
	if IsTrivial(R) then return [R]; fi;
	for a in Axes(R) do
		II := List(Check1Dimnlity(a),X->IdealClosure(R,X));
		if not ForAll(II,IsTrivial)
		then return Filtered(
			Concatenation(List(II,i->Explode(Quotient(R,i)))),
			R -> not IsTrivial(R)); fi;
	od;
	return [R];
	end
);

InstallMethod( ChangeField, "for an axial rep and a (suitable) field",
	[IsAxialRep,IsField],
	function( R, F )
	if Characteristic(Alg(R)) = Characteristic(F)
	then return R;
	elif not Characteristic(Alg(R)) = 0
	then return fail; fi;
	return AxialRep(
		Fusion(R),
		Trgp(R),
		Alg( F^Dimension(Alg(R)), F^Dimension(Closure(Alg(R))), Alg(R)!.MT*One(F) ),
		CreateDictionary( Alphabet(R), a -> R!.map(a)*One(F) ),
		SpanningWords(R)
	);
	end
);
