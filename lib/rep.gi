
#
#	representations implementation
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
				Info(AxRepInfo,3,"the following subshapes do not admit algebras:\n",
					JoinStringsWithSeparator(
						List(Filtered(rr{prespos},IsTrivial),r->Description(Trgp(r))),
					",\n")
				);
				return rr{prespos};
			fi;

			if not IsEmpty(misspos) then
				ans := UserChoice( Concatenation(
						"missing algebras for\n",
						JoinStringsWithSeparator(List(ss{misspos},Description),",\n"),"\n",
						"what would you like to do?\n"
						, "1 = quit, "
						, "2 = find all, "
						, "3 = continue without "
						#,"or 0 = error"
					),
					[0..3]
				);
				if ans = 1 then return fail;
				elif ans = 2 then
					for m in misspos
					do rr[m] := FindAxialRep(ss[m],th); od;
				elif ans = 3 then
					for s in ss{misspos}
					do Append(sr, AxialRepHelper@.getSubreps(s,G,th,field)); od;
					misspos := Difference([1..Length(ss)],misspos);
					ss := ss{misspos};
					rr := rr{misspos};
				elif ans = 0 then Error(); fi;
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
				for n in Filtered([1..Order(f)-1],n->GcdInt(n,Order(f))=1)
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
	, canonTest := function( ss, x )
			local powers;
			powers := List(Filtered([1..Order(x)-1],n->GcdInt(Order(x),n)=1),n->x^n);
			return ForAny(ss,s->s in powers);
			end
	,	canonSetPos := function( ss, x )
			local powers;
			powers := List(Filtered([1..Order(x)-1],n->GcdInt(Order(x),n)=1),n->x^n);
			return FirstPosition(ss,s->s in powers);
			end
	,	canonSet := function( ss, x )
			local powers, f;
			if IsList(x) then
				return Recursive(i->ss[i])(
					RecursiveSorted(Recursive(y->AxialRepHelper@.canonSetPos(ss,y))(x)) );
			else
				powers :=List(Filtered([1..Order(x)-1],n->GcdInt(Order(x),n)=1),n->x^n);
				f := First(ss,s->s in powers);
				if f = fail then return x;
				else return f; fi;
			fi;
			end
	, inSubrep := function( R, S, sym )
			local bb, alph, dict, s, A, mt, i, rr, c, pos, emb, al, pstnsR, elmtsS, j, v, NewRep;
			bb := ShallowCopy(SpanningWords(R));
			for s in SpanningWords(S) do
				s := AxialRepHelper@.canonSet(bb,s);
				if not s in bb then Add(bb,s); fi;
			od;
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
				for s in Recursive(s->s^c)(SpanningWords(S)) do
					s := AxialRepHelper@.canonSet(bb,s);
					if not s in bb then Add(bb,s); fi;
				od;
				A := LeftActingDomain(A)^Length(bb);
				for i in Filtered([1..Size(bb)],i->not IsBound(mt[i]))
				do mt[i] := []; od;

				pos := List(Recursive(s->s^c)(SpanningWords(S)),
					s->Position(bb,AxialRepHelper@.canonSet(bb,s)));
				emb := List( [1..Dimension(Alg(S))], i -> Basis(A)[pos[i]] );
				for s in Alphabet(S) do
					if LookupDictionary(dict,s^c) = fail
					then AddDictionary(dict,s^c,S!.map(s)*emb);
					else Add(rr,LookupDictionary(dict,s^c)-S!.map(s)*emb);
fi;
				od;

				al := Set(List(Alphabet(S),s->AxialRepHelper@.canonSet(Alphabet(R),s^c)));
				pstnsR := FilteredPositions(bb,s->All(Recursive(x->AxialRepHelper@.canonTest(al,x))(s)));
				elmtsS := List(pstnsR,i->
					S!.map(Recursive(x->First(Alphabet(S),a->a^c=x))(bb[i])) );
				if ForAny(elmtsS,s->s=fail) then Error(); fi;

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
			NewRep := AxialRep( Fusion(R), Trgp(R), Alg(A,mt),
				CreateDictionary(alph,a->LookupDictionary(dict,a)+Zero(A)), bb );
			SetAlphabet(NewRep,alph);
			rr := Subspace(A,List(rr,r->r+Zero(A)));
			return Quotient(NewRep,rr);
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
			if sr = fail then return fail;
			elif ForAny(sr,IsTrivial) then
				return TrivialAxialRep( fus, T, LeftActingDomain(A) ); fi;
			for s in sr do R := AxialRepHelper@.inSubrep( R, s, sym );
				Info(mai,3,"inserted ",Description(Trgp(s)));
		od;
			dict := CreateDictionary(Alphabet(R),a->R!.map(a)+Zero(Alg(R)));
			R := AxialRep( fus, T, Alg(R), dict, SpanningWords(R) );

			return Quotient( R,
				Subspace(Alg(R),
					List([1..Length(SpanningWords(R))],
						i -> Basis(Alg(R))[i] - R!.map(SpanningWords(R)[i]) ),
					Zero(Alg(R)) )
			);
			end
	)
);

InstallMethod( AxialRep,
	[IsFusion,IsTrgp,IsAlg,IsDictionary,IsList],
	function( Th, T, A, d, ss )
	local map, R;
	if IsTrivial(A) then
		map := x -> Zero(A);
	else
		map := function(x)
			if IsList(x) then return Mult(A)(map(x[1]),map(x[2]));
			else return LookupDictionary(d,x); fi; end;
	fi;
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
	SetAxialRep(A,R);
	SetAxes( A, List( Transpositions(T), t -> Axis(A,map(t),Th,t) ) );
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
	InstallMethod( TrivialAxialRep,
	[IsFusion,IsTrgp,IsField],
	function( fus, t, f )
		return AxialRep( fus, t, Alg( f^0, [[]] ), [], [] );
	end
);
InstallMethod( ViewString,
	[IsAxialRep],
	A -> Concatenation(
		"axial rep ",Description(Trgp(A)),
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
	InstallMethod( Symmetries,
	[IsAxialRep],
	R -> Trgp(R)
	);
InstallMethod( Axis,
	[IsAlg and HasAxialRep,IsGeneralizedRowVector,IsFusion,IsMultiplicativeElementWithInverse],
	function( A, v, th, g )
	local a;
	a := Axis(A,v,th);
	SetInvolution(a,g);
	return a;
	end
);

InstallMethod( MiyamotoHom,
	[IsAxialRep],
	function( R )
	local gg, mm; ## or: use Miyamoto functionality on axes
	gg := GeneratorsOfGroup( Symmetries(R) );
	mm := List(gg,g -> List(Basis(Closure(Alg(R))),b->R!.act(b,g)) );
	return GroupHomomorphismByImagesNC( Symmetries(R), GroupByGenerators(mm), gg, mm );
	end
	);
	InstallMethod( Miyamoto,
	[IsAxialRep],
	R -> Image(MiyamotoHom(R))
	);
InstallMethod( Orbiter,
	[IsAxialRep],
	function( R )
		if ValueOption( "permaction" ) = true
		then return function( v )
			if IsList(v[1]) then return Orbits( Symmetries(R),v,R!.act );
			else return Orbit( Symmetries(R),v,R!.act ); fi; end;
		else return function( v )
			if IsList(v[1]) then return Orbits( Miyamoto(R),v );
			else return Orbit( Miyamoto(R),v ); fi; end;
		fi;
	end
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
InstallMethod( SpanningWords,
	[IsAxialRep],
	function( R )
  local words, mb, sw, w, v;
	words := Union( List(Transpositions(Trgp(R)),t->t^Trgp(R)) );
	mb := MutableBasis( LeftActingDomain(Alg(R)),[],Zero(Alg(R)) );
	sw := [];
	while NrBasisVectors(mb) < Dimension(Alg(R)) do
		if IsEmpty(words)
		then words := Union(Cartesian(sw,sw)); fi;
		w := Remove(words[1]);
		v := SiftedVector( mb, FromWord(R)(w) );
		if not IsZero(v) then
			CloseMutableBasis(mb,v);
			Add(sw,w);
		fi;
	od;
	return sw;
	end
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
	local time, A, ss, n, mt, i, j, z, B, dict;
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

	AddRelations( B, Subspace(Closure(B),Concatenation(List(Filtered(Axes(Alg(R)),HasEigenspaces),
		function(a)
		local evv, rr, i;
		evv := List(Eigenspaces(a),Basis);
		rr := [];
		for i in [1..Length(Fields(Fusion(a)))]
		do Append(rr,List(evv[i],v->Fields(Fusion(a))[i]*v-Mult(B)(v,Vector(a)))); od;
		return rr; end ))) );

	dict := List(Alphabet(R),a->[a,R!.map(a)+z]);
	Info(AxRepInfo,3,"increased dim: ",
		Dimension(Closure(A)),"+",n-Dimension(Closure(A)));
	return AxialRep( Fusion(R), Trgp(R), B, dict, ss );
	end
	);
InstallMethod( IdealClosure,
	[IsAxialRep,IsVectorSpace],
	function( R, V )
	if ValueOption("permaction") = true then
		return CloseUnder( V, Symmetries(R), R!.act, Alg(R), Alg(R) );
	else
		return CloseUnder( V, Miyamoto(R), OnPoints, Alg(R), Alg(R) );
	fi;
	end
	);
InstallMethod( Quotient,
	[IsAxialRep,IsVectorSpace],
	function( R, X )
	local Q, l, li, mt, i, I, j, A;
	if IsTrivial(X) then return R; fi;
	Q := NaturalHomomorphismBySubspace( Closure(Alg(R)), X );
	if ForAny(Axes(Alg(R)),a->Vector(a) in Kernel(Q)) then
		Info(AxRepInfo,3,
			JoinStringsWithSeparator(List(Filtered(Axes(Alg(R)),a->Vector(a) in Kernel(Q)),ViewString),", "),
			" killed ---> rep killed");
		return TrivialAxialRep( Fusion(R), Trgp(R), LeftActingDomain(Alg(R)) );
	fi;
	l := AlgHelper@.quoBasisPos(Q);
	li := Intersection([1..Dimension(Alg(R))],l);
	mt := List([1..Length(li)],i->[]);
	for i in [1..Length(li)] do
		I := Intersection(li,[1..li[i]]);
		for j in [1..Length(I)] do
			if IsBound(Alg(R)!.MT[li[i]][I[j]])
			then mt[i][j] := Image(Q,Alg(R)!.MT[li[i]][I[j]]); fi;
		od;
	od;
	A := Alg( Length(li), Length(l), mt );
	Info(AxRepInfo,3,"decreased dim: ",Dimension(A),"+",Dimension(Closure(A))-Dimension(A));
	return AxialRep( Fusion(R), Trgp(R), A,
		CreateDictionary(Alphabet(R),a->Image(Q,R!.map(a))),
		SpanningWords(R){l}
	);
	end
	);
InstallMethod( ChangeField, "for an axial rep and a (suitable) field",
	[IsAxialRep,IsField],
	function( R, F )
	local A;
	A := ChangeField(Alg(R),F);
	if A = fail then return fail; fi;
	return AxialRep(
		Fusion(R),
		Trgp(R),
		A,
		CreateDictionary( Alphabet(R), a -> R!.map(a)*One(F) ),
		SpanningWords(R)
	);
	end
);

InstallMethod( FindAxialRep,
	[HasShape,IsFusion,IsGroup,IsList],
	function(S,fus,sym,axioms)
		local time, R, b, ax, a;
		time := Runtime();
		if ValueOption("recompute") <> true then
			R := GetAxialRep(fus,S);
			if R <> [] then
				if IsField(ValueOption("field")) then
					R := ChangeField(R,ValueOption("field"));
					if R <> fail then return R; fi;
				elif LeftActingDomain(Alg(R)) = Rationals then return R; fi;
			fi;
		fi;

		if not IsPermGroup(S) then S := AsSmallPermTrgp(S); fi;
		Info(AxRepInfo,2,"find algebra for ",Description(S)," with ",ViewString(fus));
		R := AxialRepHelper@.startAxialRep(S,fus,sym);
		if R = fail then return fail; fi;
		if not IsTrivial(R) then
		R := IncreaseClosure(R);

		while true do
			if HasRelations(Alg(R)) and not IsTrivial(Relations(Alg(R)))
			then R := Quotient(R,IdealClosure(R,Relations(Alg(R)))); fi;
			if IsTrivial(R) then break; fi;
			b := false;
			for ax in axioms do
				for a in Axes(Alg(R)) do
					ax(a);
					if HasRelations(Alg(R)) and not IsTrivial(Relations(Alg(R)))
					then b := true; break; fi;
				od;
				if b then break; fi;
			od;
			if b then continue; fi;
			if Alg(R) = Closure(Alg(R)) then break;
			else R := IncreaseClosure(R); fi;
		od;
		fi;

		WriteAxialRep(R);
		Info(AxRepInfo,2,ElapseStr(time)," --- algebra found!");
		return R;
		end
		);
	InstallMethod( FindAxialRep,
		[HasShape,IsFusion],
		function(S,fus)
		return FindAxialRep(S,fus,S,[CheckLinearity,CheckSemisimplicity]); end
		);
	InstallMethod( FindAxialRep,
		[IsGroup,IsSakuma,IsFusion],
		function(G,Sak,fus)
			if not IsPermGroup(G) then G := Image(SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(G)))); fi;
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
		return FindAxialRep(T,fus,AutomorphismGroup(T),[CheckLinearity,CheckSemisimplicity]);
		end
	);
InstallMethod( AxialSubrep,
	[IsAxialRep,IsGroup],
	function( R, T )
	return FindAxialRep( List(
	Intersection( Concatenation(List(Transpositions(Trgp(R)),t->t^Trgp(R))), T ),
	t -> Axis( Alg(R), R!.map(t), Fusion(R) ) )
	);
	end
	);
InstallMethod( FindAxialRep,
	[IsList],
	function( aa )
  local M, vv, mm, F, rels, i, j, G, T, gg, f, sw, sv;
	if not ForAll(aa,a->Fusion(a) = Fusion(aa[1]) and Alg(a) = Alg(aa[1]))
	then return fail; fi;
	M := Group( List(aa,Miyamoto) );
	vv := Concatenation(Orbits(M,List(aa,Vector)));
	mm := List(vv,v->Miyamoto(Axis(Alg(aa[1]),v,Fusion(aa[1]))));
	F := FreeGroup( Size(vv) );
	rels := [];
	for i in [1..Size(vv)] do
		for j in [1..Size(vv)] do
			Add(rels,F.(i)^F.(j)*F.(Position(vv,vv[i]^mm[j])));
	od; od;
	G := F / rels;
	T := AsSmallPermTrgp( Trgp( G,List([1..Size(vv)],i->G.(i)) ) );
	gg := GeneratorsOfGroup(T);
	f := function(g) local p;
		if IsList(g) then return Mult(Alg(aa[1]))(f(g[1]),f(g[2])); fi;
		p := Position(gg,g);
		if p = fail then return fail;
		else return vv[p]; fi;
	end;
	sw := SpanOfWords( Alg(aa[1]),AxialRepHelper@.closedAlphabet(T,gg),f );
	sv := List(sw,f);
	sv := BasisNC(SubspaceNC(Alg(aa[1]),sv,"basis"),sv);
	return AxialRep(
		Fusion(aa[1]),
		T,
		DerivedSubalg( Alg(aa[1]), sv ),
		CreateDictionary(AxialRepHelper@.closedAlphabet(T,gg),
			g -> Coefficients(sv,f(g))),
		sw
	);
	end
);

InstallMethod( FindOtherSakumas,
	[IsAxialRep],
	function( R )
  local A, is, ccs, pos, x, as, OnAxis, ps, res;
	if not IsClosed(Alg(R))
	or not (HasIsUnitaryFusion(Fusion(R)) and IsUnitaryFusion(Fusion(R)))
	or not (HasIsRationalVirasoroFusion(Fusion(R)) and IsRationalVirasoroFusion(Fusion(R)))
	then# return fail; fi;
	fi;
	A := Alg(R);
	as := UnitaryRationalVirasoroAxes(A);
	OnAxis := function(om,g)
		return Axis(A,R!.act(Vector(om),g),Fusion(om));
	end;
	ps := List(
		 OrbitsDomain( Trgp(R),
		 	Filtered(Combinations(as,2),om->Fusion(om[1])=Fusion(om[2])),
			function(om,g) return List(om,o->OnAxis(o,g)); end ),
		Representative
	);
	res := List(ps,FindAxialRep);
	List(res,RecogniseShape);
	return res;
	end
);

InstallMethod( Explosion,
	[IsAxialRep],
	function( R )
	local a, II;
	if IsTrivial(R) then return [R]; fi;
	for a in Axes(Alg(R)) do
		II := List(Check1Dimnlity(a),X->IdealClosure(R,X));
		if not ForAll(II,IsTrivial)
		then return Filtered(
			Concatenation(List(II,i->Explosion(Quotient(R,i)))),
			R -> not IsTrivial(R)); fi;
	od;
	ResetFilterObj(Trgp(R),HasShape);
	return [R];
	end
	);
InstallMethod( RecogniseShape,
	[IsAxialRep],
	function( R )
	local sh, p, S, o, T, newshape, usedlabels, newcl, VS;
	#if HasShape(Trgp(R)) then return Shape(Trgp(R)); fi;
	if not IsClosed(Alg(R)) then return fail; fi;
	if Dimension(Alg(R)) = 1 then return [[1,"A"]]; fi;
	sh := [];
	Trgp(R)!.Pairs := Sorted(Pairs(Trgp(R)),p->Order(Product(p)));
	for p in Pairs(Trgp(R)) do
		S := FindAxialRep(List(p,t->Axis(Alg(R),R!.map(t),Fusion(R))));
		o := Order(Product(p));
		T := Filtered( GetAxialRep(Fusion(R),Trgp(S)),
			R -> Dimension(Alg(R)) = Dimension(Alg(S))
			and ForAll( Shape(Trgp(R)),cl -> o mod cl[1] = 0 )
			and Alg(R)!.MT = Alg(S)!.MT
		);
		if Length(T) = 1
			then Add( sh, Sorted(Shape(Trgp(T[1])),cl -> -cl[1])[1] );
		elif Length(T) < 1 then
			usedlabels := Concatenation(List(GetAxialRep(Fusion(R),Trgp(S)),
				Q -> First(Shape(Trgp(Q)),cl->cl[1] = o)[2]));
			newcl := [o,
				List([First(List([65..90],CharInt),A->not A in usedlabels)],IdFunc)];
			Add( sh, newcl );
			newshape := List(Filtered(Pairs(Trgp(S)),q->Order(Product(q))<o),
				q -> sh[FirstPosition(Pairs(Trgp(R)),p->
					RepresentativeAction(Trgp(R),q,p,OnSets)<>fail)]
			);
			Perform(FilteredPositions(Pairs(Trgp(S)),q->Order(Product(q))=o),
				function(i) newshape[i] := newcl; end);
			VS := ViewString(S);
			SetShape(Trgp(S),newshape);
			if UserChoice(Concatenation(
				"no shape recognised for ",VS,
				" with ",ViewString(Fusion(S)),";\n",
				"proposed new shape: ",ShapeStr(Shape(Trgp(S))),"\n",
				"1 = add to library, 2 = don't"),
				[1,2]
			) = 1 then WriteAxialRep(S); fi;
		else return fail; fi;
	od;
	SetShape(Trgp(R),sh);
	return sh;
	end
);

InstallMethod( CosetAxis,
	[IsAxialRep,IsGroup],
	function( R, H )
	local D, A, B, e;
	if Subtrgp(Trgp(R),H) = fail then return fail; fi;
	D := Intersection(Union(List(Transpositions(Trgp(R)),t->t^Trgp(R))),H);
	A := Alg(R);
	B := CloseUnderMult(Subspace(A,List(D,FromWord(R))),A);
	e := VectorInAlg(A,Identity(A) - Identity(A,B));
	ObservedFusion(e);
	return e;
	end
	);
	InstallMethod( CosetAxis,
	[IsAxialRep,IsGroup,IsGroup],
	function( R, H, K )
	local D, E, A, B, C, e;
	if Subtrgp(Trgp(R),H) = fail or Subtrgp(Trgp(R),K) = fail or not IsSubgroup(H,K) then return fail; fi;
	D := Intersection(Union(List(Transpositions(Trgp(R)),t->t^Trgp(R))),H);
	E := Intersection(Union(List(Transpositions(Trgp(R)),t->t^Trgp(R))),K);
	A := Alg(R);
	B := CloseUnderMult(Subspace(A,List(D,FromWord(R))),A);
	C := CloseUnderMult(Subspace(A,List(E,FromWord(R))),A);
	e := VectorInAlg(A,Identity(A,B) - Identity(A,C));
	ObservedFusion(e);
	return e;
	end
);
