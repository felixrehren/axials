
#
#	alg implementation
#

InstallValue( AlgHelper@, rec(
		trivialAlg := function( field )
			return Alg( field^0, [[]] ); end
	,	incBasis := function( A, n )
			local z, mt, i, j;
			z := [1..Dimension(A)+n]*Zero(LeftActingDomain(A));
			mt := List([1..Dimension(A)],i->[]);
			for i in [1..Dimension(A)] do
				for j in [1..i] do
					if IsBound(A!.MT[i][j])
					then mt[i][j] := A!.MT[i][j]+z; fi;
				od;
			od;
			return Alg(
					Dimension(A)+n,
					mt
				);
			end
	, quoBasisPos := function( Q )
			local K,l,B,s,v,w;
			K := MutableBasis( LeftActingDomain(Source(Q)), [], Zero(Source(Q)) );
			l := [1..Dimension(Source(Q))];
			B := Basis(VectorSpace(LeftActingDomain(Source(Q)),List(Basis(Kernel(Q)),Reversed)));
			for s in [Dimension(Source(Q)),Dimension(Source(Q))-1..1] do
				v := Basis(Source(Q))[s];
				w := v - Reversed(SiftedVector(B,Reversed(v)));
				if IsZero(w) then continue; fi;
				w := SiftedVector(K,w);
				if IsZero(w) then continue;
				else
					CloseMutableBasis(K,w);
					Remove(l,s);
				fi;
			od;
			return l;
			end
	, relToFn := function( r )
			local er, p, x, s;
			if r = fail then return false;
			elif IsZero(r) then return IdFunc;
			elif InField(r)<>fail then return fail; fi;
			er := ExtRepPolynomialRatFun(r);
			p := First([1..Length(er)/2],p -> 
				 not IsEmpty(er[2*p-1]) and er[2*p-1][2]=1);
			if p = fail then return false; fi;
			x := Indeterminate(DefaultField(er[2*p]),er[2*p-1][1]);
			s := x - r/er[2*p];
			return Recursive(function(e)
				if IsRat(e) or IsCyc(e)
				then return e; 
				else return Value(e,[x],[s]); fi;
				end);
			end
	, idempotentSolns := function( A, i )
			local time, rr, ord, solns, r, lm, ss, s;
			time := Runtime();
			rr := FilteredNot(MultNaive(i,i,A!.MT)-i,IsZero);
			if IsEmpty(rr) then return [InField(i)];
			elif ForAny(rr,r->InField(r)<>fail) then return []; fi;
			r := First(rr,IsUnivariatePolynomial);
			if r = fail then
				ord := MonomialLexOrdering();
				rr := GroebnerBasisNC(rr,ord);
				InfoPro("crunching relations",time);
			fi;
			r := First(rr,IsUnivariatePolynomial);
			if r = fail then return []; fi;
			solns := []; 
			lm := IndeterminateOfUnivariateRationalFunction(r);
			ss := RootsOfPolynomial(r);
			for s in ss
			do Append(solns,
				AlgHelper@.idempotentSolns(A,AlgHelper@.relToFn(lm-s)(i)) );
			od;
			return solns;
			end
	,	maximalCliques := function( inc )	 	### bool-valued incidence matrix
			local set, cliques, s, c;
			set := [1..Length(inc)];
			cliques := List( set, s -> [s] );
			for s in set do
				for c in cliques do
					if s > Maximum(c)
					and ForAll(c,i->inc[i][s])
					then Add(cliques,Concatenation(c,[s])); fi;
				od;
			od;
			return Filtered( cliques,
				c -> not ForAny( cliques, d -> Size(d)>Size(c) and IsSubset(d,c) ) );
			end
	, annihSubsets := function( ii, mult )
			local inc, cliques;
			ii := FilteredNot(ii,IsZero);
			inc := List(ii, i -> List(ii, j -> IsZero(mult(i,j)) ));
			cliques := AlgHelper@.maximalCliques( inc );
			cliques := Filtered(cliques,c->Size(c)>2);
			## remove {a}, {a,i-a}
			return List(cliques,c -> ii{c});
			end
	)
);

InstallMethod( Alg,
	[IsVectorSpace,IsList],
	function( V, mt )
	return Alg( V, V, mt );
	end
	);
	InstallMethod( Alg,
	[IsPosInt,IsList],
	function( dim, mt )
	return Alg(DefaultField(mt[1][1])^dim,DefaultField(mt[1][1])^dim,mt);
	end
	);
	InstallMethod( Alg,
	[IsVectorSpace,IsVectorSpace,IsList],
	function( V, W, mt )
	return Alg( V, W, mt, 1 );
	end
	);
	InstallMethod( Alg,
	[IsVectorSpace,IsVectorSpace,IsList,IsInt],
	function( V, W, mt, com )
	SetMT(V,mt);
	SetClosure(V,W);
	SetIsCommutative(V,com = 1);
	if Dimension(V) = Dimension(W) then SetIsClosed(V,true); fi;
	return V;
	end
	);
	InstallMethod( Alg,
	[IsPosInt,IsPosInt,IsList],
	function( dim, cl, mt )
	local W, V;
	W := DefaultField(mt[1][1])^cl;
	V := Subspace(W,Basis(W){[1..dim]});
	return Alg( V, W, mt );
	end
	);
	InstallMethod( ViewString,
	[IsAlg],
	function(A)
		local dim;
		if Dimension(A) = Dimension(Closure(A))
		then dim := String(Dimension(A));
		else dim := Concatenation(String(Dimension(A)),"+",String(Dimension(Closure(A))-Dimension(A))); fi;
		return Concatenation( "an alg of dim ",dim );
	end
	);
	InstallMethod( PrintString,
	[IsAlg],
	function(A)
	return Concatenation(
		"Alg(\n",
			"\t",PrintString(LeftActingDomain(A)),"^",String(Dimension(A)),",\n",
			"\t",String(A!.MT),"\n",
		")"
	);
	end
	);
	InstallMethod( Closure,
	[IsAlg],
	A -> VectorSpace( LeftActingDomain(A), Concatenation(Concatenation(A!.MT)), Zero(A) )
	);
	InstallMethod( IsClosed,
	[IsAlg],
	A -> Dimension(A) = Dimension(Closure(A)) 
	);
	InstallMethod( Mult,
	[IsAlg and IsCommutative],
	A -> MultComm( A, Closure(A), A!.MT )
	);
	InstallMethod( Mult,
	[IsAlg],
	A -> Mult( A, Closure(A), A!.MT )
	);
	InstallMethod( Ad,
	[IsAlg], # 1-dim'l algs??
	function( A )
	return function( v )
		if IsZero(v) then return Basis(A)*Zero(LeftActingDomain(A)); fi;
		return Sum( FilteredPositions(v,x->not IsZero(x)),
			i -> v[i]*Concatenation(
				List([1..i],j->A!.MT[i][j]),
				List([i+1..Dimension(A)],j->A!.MT[j][i])
			)
		); end;
	end
	);
	InstallMethod( Ad,
	[IsAlg,IsVectorSpace],
	function( A, V )
	return function( v )
		return List(Basis(V),b->Coefficients(Basis(V),Mult(A)(v,b))); end;
	end
	);
InstallMethod( ChangeField,
	[IsAlg,IsField],
	function( A, F )
	local B;
	if Characteristic(A) = Characteristic(F)
	then return A;
	elif not Characteristic(A) = 0
	then return fail; fi;
	B := Alg( Dimension(A), Dimension(Closure(A)), A!.MT*One(F) );
	if HasAxes(A) then SetAxes(B,List(Axes(A),a->Axis(B,Vector(a)*One(F),Fusion(a)))); fi;
	return B;
	end
);

InstallMethod( CloseUnderAct,
	[IsVectorSpace,IsGroup,IsFunction],
	function( V, G, act )
		local time, mb, vs, newvs, g, v, w, S;
		time := Runtime();
		mb := MutableBasis( LeftActingDomain(V), Basis(V), Zero(V) );
		vs := BasisVectors(mb);
		while not IsEmpty(vs) do
			newvs := [];
			for g in GeneratorsOfGroup(G) do
				for v in vs do
					w := SiftedVector(mb,act(v,g)); # don't necessarily sift w completely,
					if not IsZero(w) then # just observe if nonzero entries in positions
						CloseMutableBasis(mb,w); # which cannot be sifted away
						Add(newvs,w);
					fi;
				od;
			od;
			vs := newvs;
		od;
		S := VectorSpace( LeftActingDomain(V), BasisVectors(mb), Zero(V) );
		InfoPro("orbiting",time);
		return S;
		end
	);
InstallMethod( ImageUnderMult,
	[IsVectorSpace,IsVectorSpace,IsAlg],
	function( V, U, A )
		local time, mb, v, u, uv, S;
		time := Runtime();
		mb := MutableBasis( LeftActingDomain(A), [], Zero(V) );
		for v in Basis(Intersection(A,V)) do for u in Basis(Intersection(A,U))
		do uv := Mult(A)(v,u); if uv <> fail then CloseMutableBasis( mb, uv );
		fi; od; od;
		S := VectorSpace( LeftActingDomain(A), BasisVectors(mb), Zero(V) );
		InfoPro("multiplying",time);
		return S;
		end
	);
	InstallMethod( ImageUnderMult,
	[IsVector,IsVectorSpace,IsAlg],
	function( v, U, A )
	if not v in A then return fail;
	else return
		VectorSpace(LeftActingDomain(A),List(Basis(Intersection(A,U)),u->Mult(A)(v,u)));
	fi;
	end
	);
InstallMethod( CloseUnderMult,
	[IsVectorSpace,IsVectorSpace,IsAlg],
	function(U,V,A)
	local W, X, Y;
	W := U;
	X := U;
	while true do
		X := ImageUnderMult( X,V,A );
		Y := W + X;
		if Dimension(Y) = Dimension(W) then break;
		else W := Y; fi;
	od;
	return W;
	end
	);
InstallMethod( CloseUnderMult,
	[IsVectorSpace,IsAlg],
	function(V,A)
	local W, X, Y;
	W := V;
	X := V;
	while true do
		X := ImageUnderMult( X,W,A );
		Y := W + X;
		if Dimension(Y) = Dimension(W) then break;
		else W := Y; fi;
	od;
	return W;
	end
	);
InstallMethod( IdealClosure,
	[IsAlg,IsVectorSpace],
	function( A, V )
	return CloseUnderMult(V,A,A);
	end
	);
InstallMethod( CloseUnder,
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsAlg],
	function( V, G, act, U, A )
		local W, X, Y, Z;
		W := V;
		Y := V;
		while true do
			X := CloseUnderAct( Y, G, act );
			W := W + X;
			Y := ImageUnderMult( X, U, A ); 
			Z := W + Y;
			if Dimension(Z) = Dimension(W) then break;
			else W := Z; fi;
		od;
		return W;
		end
);

InstallMethod( DerivedSubalg,
	[IsAlg,IsVectorSpace],
	function( A, V )
	return DerivedSubalg(A,Basis(CloseUnderMult(V,A)));
	end
	);
	InstallMethod( DerivedSubalg,
	[IsAlg,IsBasis],
	function( A, B )
	local T; # use left inverse of B
	T := TransposedMat(B);
	return Alg( LeftActingDomain(A)^Length(B),
		List([1..Length(B)],i ->
		List([1..i],j -> Mult(A)(B[i],B[j])*( T*(B*T)^-1 ) ))
	);
	end
	);
InstallMethod( SpanOfWords,
	[IsAlg,IsList,IsFunction],
	function( A, letters, map )
	local words, mb, mult, newwords, l, dim, n, v;
	words := [];
	mb := MutableBasis( DefaultField(Concatenation(Concatenation(Concatenation(A!.MT)),Concatenation(List(letters,map)))),
		[], Zero(A) );
	mult := function( w )
		if IsList(w) then return Mult(A)(mult(w[1]),mult(w[2]));
		else return map(w); fi; end;
	newwords := letters;
	l := 1;
	while true do
		dim := NrBasisVectors(mb);
		for n in newwords do
			v := SiftedVector( mb, mult(n) );
			if not IsZero(v) then
				Add(words,n);
				CloseMutableBasis(mb,v);
				if NrBasisVectors(mb) = Dimension(A) then return words; fi;
			fi;
		od;
		if NrBasisVectors(mb) = dim then return words; fi;
		newwords := Sorted(Filtered(Cartesian(words,words),w->Length(Flat([w]))>l),Length);
		l := l + 1;
	od;
	end
);

InstallMethod( IncreaseClosure,
	[IsAlg],
	function( A )
	local mt, n, i, j, bound, z, C, B;
	if not HasClosure(A) then SetClosure(A,LeftActingDomain(A)^Dimension(A)); fi;
	n := Dimension(Closure(A));
	mt := List([1..Dimension(Closure(A))],i->[]);
	for i in [1..Dimension(Closure(A))] do
		if IsCommutative(A) then bound := i; else bound := Dimension(Closure(A)); fi;
		for j in [1..bound] do
			if IsBound(A!.MT[i]) and IsBound(A!.MT[i][j])
			then mt[i][j] := A!.MT[i][j];
			else
				n := n+1;
				mt[i][j] := KroneckerVector(n,n)*One(LeftActingDomain(A));
			fi;
		od;
	od;
	z := [1..n]*Zero(LeftActingDomain(A));
	for i in [1..Dimension(Closure(A))] do for j in [1..i]
	do mt[i][j] := mt[i][j] + z; od; od;
	C := LeftActingDomain(A)^n;
	B := Subspace(C,Basis(C){[1..Dimension(Closure(A))]});
	if IsCommutative(A)
	then B := Alg( B,C,mt,1 );
	else B := Alg( B,C,mt,0 ); fi;
	if HasAxes(A) then SetAxes(B,List(Axes(A),function(a) a!.Alg := B; a!.v := a!.v+z; return a; end)); fi;
	return B;
	end
	);
InstallMethod( AddRelations,
	[IsAlg,IsVectorSpace],
	function( A, X )
	if HasRelations(A) then A!.Relations := Relations(A) + X;
	else SetRelations(A,X); fi;
	end
	);
InstallMethod( Quotient,
	[IsAlg,IsVectorSpace],
	function( A, X )
	local Q, mt, f, Bcl, B;
	if Dimension(X) = Dimension(Closure(A))
	then return AlgHelper@.trivialAlg(LeftActingDomain(A)); fi;
	Q := NaturalHomomorphismBySubspace( Closure(A), X );		
	f := Intersection(AlgHelper@.quoBasisPos(Q),[1..Dimension(A)]);
	Bcl := LeftActingDomain(A)^(Dimension(Closure(A)) - Dimension(X));
	B := Subspace(Bcl,Basis(Bcl){[1..Dimension(A) - Dimension(Intersection(A,X))]});
	if IsCommutative(A)
	then B := Alg( B, Bcl, List(f,i->List(Intersection([1..i],f),j->Image(Q,A!.MT[i][j]))), 1 );
	else B := Alg( B, Bcl, List(f,i->List(f,j->Image(Q,A!.MT[i][j]))), 0 ); fi;
	if HasAxes(A) then SetAxes(B,List(Axes(A),a->Axis(B,Vector(a)^Q,Fusion(a)))); fi;
	if HasPlusses(A) then SetPlusses(B,Plusses(A){AlgHelper@.quoBasisPos(Q)}); fi;
	return B;
	end
);

InstallMethod( Form,
	[IsAlg and HasFT],
	A -> MultComm( A, LeftActingDomain(A), A!.FT )
	);
	InstallMethod( Form,
	[IsAlg and HasAxialRep],
	function( A )
	local tail, time, R, ft, aa, pp, i, j, x, c, p, tails, y, pos, xg, a, eses, u, v, uv, old, new, r;
	tail := function(v)
		local u;
		u := ShallowCopy(v);
		u[LastNonzeroPos(u)] := Zero(LeftActingDomain(A));
		return u; end;
	time := Runtime();
	R := AxialRep(A);
	c := 1;
	ft := List([1..Dimension(A)],j->[]);
	aa := Union(List(Transpositions(Trgp(R)),t->t^Trgp(R)));
	pp := FilteredPositions(SpanningWords(R),w->not IsList(w) and w in aa);
	for i in pp
	do ft[i][i] := 2*CentralCharge(Fusion(R)); od;
	for i in [1..Dimension(A)] do
		for j in [1..i] do
			if not IsBound(ft[i][j]) then
				x := Indeterminate(LeftActingDomain(A),c);
				c := c + 1;
				for p in Orbit( Symmetries(R),Basis(A){[i,j]},function( om, g )
					return List(om,v->R!.act(v,g)); end ) do
					tails := List(p,tail);
					y := [Mult(A,LeftActingDomain(A),ft)(p[1]-tails[1],tails[2]),
					 Mult(A,LeftActingDomain(A),ft)(p[2]-tails[2],tails[1]),
					 Mult(A,LeftActingDomain(A),ft)(tails[1],tails[2])];
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
	for a in Axes(A) do
		for eses in Combinations(Eigenspaces(a),2) do
			for u in Basis(eses[1]) do
				for v in Basis(eses[2]) do
					Add(old,[u,v]);
				od;
			od;
		od;
	od;
	while true do
		new := [];
		for uv in old do
			r := AlgHelper@.relToFn(MultComm(A,LeftActingDomain(A),ft)(uv[1],uv[2]));
			if r = fail then Error("alg does not exist??");
			elif r = false then Add(new,uv);
			else ft := r(ft); fi;
		od;
		if Length(new) = Length(old) then break; fi;
		old := new;
	od;
	InfoPro("solved form by perps",time);

	SetFT(A,InField(ft));
	return Form(A);
	end
	);
InstallMethod( CentralCharge,
	[IsAlg and IsClosed],
	A ->
	1/2*Form(A)(Identity(A),Identity(A))
	);
InstallMethod( OrthogonalComplement,
	[IsAlg and HasFT,IsVectorSpace],
	function( A, B )
  local ii, x, rr, i;
	ii := List( [1..Dimension(A)], i -> Indeterminate( LeftActingDomain(A), i ) );
	x := Sum( [1..Dimension(A)], i -> ii[i]*Basis(A)[i] );
	rr := List( Basis(B), b -> Form(A)(b,x) );
	for i in [1..Length(rr)] do
		x := List(x,AlgHelper@.relToFn(rr[i]));
		rr := List(rr,AlgHelper@.relToFn(rr[i]));
	od;
	return Subspace( A, List( [1..Dimension(A)], i -> List(x,function(y) if IsRationalFunction(y) then return Value( y, ii, Basis(A)[i] ); else return y; fi; end) ) );
	end
	);
	InstallMethod( OrthogonalComplement,
	[IsAlg and HasFT],
	A -> OrthogonalComplement( A, A )
);

InstallMethod( Identity,
	[IsAlg and IsClosed],
	A -> Identity(A,A)
	);
	InstallMethod( Identity,
	[IsAlg and IsClosed,IsVectorSpace],
	function( A, B )
	local x, rr, i, f;
	if IsTrivial(B) then return Zero(A); fi;
	x := Sum( [1..Dimension(B)], i -> Indeterminate( LeftActingDomain(A), i )*Basis(B)[i] );
	rr := FilteredNot(Concatenation(List( Basis(B), b -> Mult(A)(b,x) - b )),IsZero);
	for i in [1..Length(rr)] do
		f := AlgHelper@.relToFn(rr[i]);
		if f = fail then return fail; fi;
		x := List(x,f);
		rr := List(rr,f);
	od;
	return InField(x);
	end
);

InstallMethod( Idempotents, "in subspace of an axial alg",
	[IsAlg and IsClosed,IsVectorSpace],
	function( A, V )
		local B, i;
		B := Basis(V);
		i := Sum([1..Dimension(V)], i -> Indeterminate(LeftActingDomain(A),i)*B[i]);
		# mistake here?? try finding idempotents in tau-fixed subalg of (3A) if (3A)-idempots are not known
		return InField(Set(AlgHelper@.idempotentSolns(A,i)));
	end
	);
	InstallMethod( Idempotents, "in subspace of an axial alg",
	[IsAlg and IsClosed and HasIdempotents,IsVectorSpace],
	function( A, V )
	return Intersection( V, Idempotents(A) );
	end
	);
	InstallMethod( Idempotents, "of an axial alg",
	[IsAlg and IsClosed],
	A -> Idempotents(A,A)
	);
InstallMethod( IsAssociativeSubalgebra,
	[IsAlg,IsVectorSpace],
	function( A, V )
	return ForAll( [1..Dimension(V)], i ->
		ForAll( [1..i], j ->
			ForAll( [1..j], k ->
				Mult(A)(Mult(A)(Basis(V)[i],Basis(V)[j]),Basis(V)[k])
				= Mult(A)(Basis(V)[i],Mult(A)(Basis(V)[j],Basis(V)[k]))
			)
		)
	);
	end
	);
InstallMethod( AssociativeSubalgebras, "in subspace of an axial alg",
	[IsAlg and IsClosed,IsVectorSpace],
	function( A, V )
	return List(
		AlgHelper@.annihSubsets(Idempotents(A,V),Mult(A)),
		B->Subspace(A,B,"basis")
	);
	end
	);
	InstallMethod( AssociativeSubalgebras, "of an axial alg",
	[IsAlg and IsClosed],
	A -> AssociativeSubalgebras(A,A)
	);
InstallMethod( UnitaryRationalVirasoroAxes,
	[IsAlg and IsClosed and HasFT],
	function( A )
  local is, ccs, pos, x;
	is := Idempotents(A);
	ccs := InField(List(is,i->1/2*Form(A)(i,i)));
	if not ForAll(ccs,cc->cc in Rationals) then return fail; fi;
	pos := Filtered([1..Length(is)],i->ccs[i]<1 and ccs[i]>0);
	is := is{pos};
	ccs := ccs{pos};
	x := Indeterminate( Rationals );
	return List([1..Length(is)], function(i) local j;
		j := First( RootsOfPolynomial( x^2 + x - 6/(1-ccs[i]) ), IsPosInt );
		return Axis( A, is[i], VirasoroFusion(j,j+1) ); end
	);
	end
);

InstallMethod( EnforceAxioms,
	[IsAxialAlg,IsList],
	function( A, axioms )
  local b, ax, a;
	while true do
		if HasRelations(A) and not IsTrivial(Relations(A))
			then A := Quotient(A,Relations(A)); fi;
		if IsTrivial(A) then break; fi;
		b := false;
		for ax in axioms do
			for a in Axes(A) do
				ax(a);
				if HasRelations(A) and not IsTrivial(Relations(A))
				then b := true; break; fi;
			od;
			if b then break; fi;
		od;
		if b then continue;
		else break; fi;
	od;
	return A;
	end
);

InstallMethod( Matsuo,
	[IsTrgp,IsRat,IsRat],
	function( T, alpha, cc )
  local D, s, mat, V, B, mt, ft, A, fus, i, j, k, l;
	D := Union( List(Transpositions(T),t->Set(Orbit(T,t))) );
	s := Size(D);
	mat := List([1..s],d->List([1..s],function(c)
		if IsOne(Comm(D[c],D[d])) then return 0;
		else return Position(D,D[c]^D[d]); fi; end));
	V := Rationals^(s);
	B := Basis(V);
	mt := List([1..Dimension(V)],i->[]);
	ft := List([1..Dimension(V)],i->[]);
	for k in [1..s] do
		for l in [1..s] do
			if IsZero(mat[k][l]) then
				mt[k][l] := Zero(V);
				ft[k][l] := 0;
			else
				mt[k][l] := alpha/2*(Basis(V)[k]+Basis(V)[l]-Basis(V)[mat[k][l]]);
				ft[k][l] := alpha*cc;
			fi;
		od;
		mt[k][k] := Basis(V)[k];
		ft[k][k] := 2*cc;
	od;
	A := Alg(V,mt);
	SetFT(A,ft);
	Form(A);
	SetAxes(A,List(
		Basis(A){[1..l]},
		x -> Axis(A,x,JordanFusion(alpha)))
	);
	return A;
	end
	);
InstallMethod( 2Matsuo,
	[IsTrgp,IsRat,IsRat],
	function( T, alpha, cc )
  local D, s, mat, V, B, mt, ft, A, fus, i, j, k, l;
	D := Union( List(Transpositions(T),t->Set(Orbit(T,t))) );
	s := Size(D);
	mat := List([1..s],d->List([1..s],function(c)
		if IsOne(Comm(D[c],D[d])) then return 0;
		else return Position(D,D[c]^D[d]); fi; end));
	V := Rationals^(2*s);
	B := Basis(V);
	mt := List([1..Dimension(V)],i->[]);
	ft := List([1..Dimension(V)],i->[]);
	for i in [0..1] do
		for j in [0..i] do
			for k in [1..s] do
				mt[k+i*s][k+j*s] := Zero(V);
				ft[k+i*s][k+j*s] := 0;
				for l in [1..s] do
					if IsZero(mat[k][l]) then
						mt[k+i*s][l+j*s] := Zero(V);
						ft[k+i*s][l+j*s] := 0;
					else
						mt[k+i*s][l+j*s] := alpha/2*(Basis(V)[k+i*s]+Basis(V)[l+j*s]-Basis(V)[mat[k][l]+((i+j) mod 2)*s]);
						ft[k+i*s][l+j*s] := alpha*cc;
					fi;
				od;
			od;
		od;
		for k in [1..s] do
			mt[k+i*s][k+i*s] := Basis(V)[k+i*s];
			ft[k+i*s][k+i*s] := 2*cc;
		od;
	od;
	A := Alg(V,mt);
	SetFT(A,ft);
	Form(A);
	SetAxes(A,List(
		Basis(A){[1..l]},
		x -> Axis(A,x,JordanFusion(alpha)))
	);
	return A;
	end
	);
InstallMethod( DLMN,
	[IsString,IsPosInt],
	function( X, n )
	return 2Matsuo( WeylGroup( X, n ), 1/4, 1/2 );
	end
);

InstallMethod( ParabolicChain,
	[IsAlg],
	A -> ParabolicChain(A,TrivialSubspace(A))
	);
InstallMethod( ParabolicChain,
	[IsAlg,IsVectorSpace],
	function( A,B0 )
  local B, BB, b;
	B := Basis(A);
	BB := [B0];
	while BB[Length(BB)] < A do
		b := First(B,b->not b in BB[Length(BB)] and ForAny(Basis(BB[Length(BB)]),
			c->not IsZero(Mult(A)(b,c))));
		if b = fail then b := First(B,b->not b in BB[Length(BB)]); fi;
		BB[Length(BB)+1] := CloseUnderMult(BB[Length(BB)]+Subspace(A,[b]),A);
	od;
	return BB;
	end
	);
InstallMethod( ParabolicTorus,
	[IsAlg],
	function( A )
  local ii;
	ii := List(ParabolicChain(A),B->Identity(A,B));
	return List([2..Length(ii)],i->ii[i]-ii[i-1]);
	end
	);
InstallMethod( FlatTorus,
	[IsAlg],
	function( A )
  local B, C, b;
	B := Basis(A);
	C := Subspace(A,B{[1]});
	while C < A do
		b := First(B,b->not b in C and ForAll(Basis(C),c->IsZero(Mult(A)(b,c))));
		if b = fail then break; fi;
		C := C+Subspace(A,[b]);
	od;
	return Basis(C);
	end
	);
InstallMethod( ToralBasis,
	[IsAlg,IsList],
	function( A, T )
  local ess, B, C, c, cc, es;
	T := List(T,t->VectorInAlg(A,t));
	ess := List(T,Eigenspaces);
	B := [];
	C := ShallowCopy(ess[1]);
	while not IsEmpty(C) do
		c := Remove(C,1);
		if Dimension(c) = 1 then AddSet(B,Basis(c)[1]); continue; fi;
		for es in ess{[2..Length(T)]} do
			cc := List(es,s->Intersection(c,s));
			if not c in cc then break; fi;
			cc := [];
		od;												# lots of superfluous intersections
		if IsEmpty(cc) then UniteSet(B,Basis(c));
		else Append(C,Filtered(cc,c->not IsTrivial(c))); fi;
	od;
	return B;
	end
	);
InstallMethod( ToralDecomposition,
	[IsAlg,IsList],
	function( A, T )
  local B, dteigval;
	B := ToralBasis(A,T);
	if B = fail then return fail; fi;
	dteigval := function (t,v)
		local p;
		p := FirstPosition(v,x->not IsZero(x));
		return Mult(A)(t,v)[p]/v[p]; end;
	return List(B,b->List(T,t->dteigval(t,b)));
	end
	);
InstallMethod( ToralReconstruct,
	[IsList,IsField],
	function( td, field )
	local V, l, toralpos, mt, v, i, j;
	V := field^Length(td);
	l := Length(td[1]);
	toralpos := List([1..l],i->Position(td,KroneckerVector(i,l)));
	if ForAny(toralpos,x->x=fail) then return fail; fi;
	mt := List([1..Dimension(V)],i->[]);
	for i in [1..Dimension(V)] do
		for j in [1..l] do
			v := td[i][j]*Basis(V)[i];
			if toralpos[j] > i
			then mt[toralpos[j]][i] := v;
			else mt[i][toralpos[j]] := v; fi;
		od;
	od;
	return Alg(V,mt);
	end
);

InstallMethod( IsJordan,
	[IsAlg],
	A -> IsJordan(A,A)
	);
	InstallMethod( IsJordan,
	[IsAlg,IsVectorSpace],
	function( A, B )
	local M;
	M := Mult(A);
#	return ForAll(UnorderedTuples(Basis(B),3),xyz -> IsZero( 
#		M(M(M(xyz[1],xyz[1]),xyz[2]),xyz[3]) - M(M(xyz[1],xyz[1]),M(xyz[2],xyz[3]))
#		 + 2*M(M(M(xyz[1],xyz[3]),xyz[2]),xyz[1]) - 2*M(M(xyz[1],xyz[3]),M(xyz[2],xyz[1]))
	return ForAll(UnorderedTuples(Basis(B),4),wxyz -> IsZero( 
		M(M(M(wxyz[2],wxyz[4]),wxyz[3]),wxyz[1]) - M(M(wxyz[2],wxyz[4]),M(wxyz[3],wxyz[1]))
	 +M(M(M(wxyz[4],wxyz[1]),wxyz[3]),wxyz[2]) - M(M(wxyz[4],wxyz[1]),M(wxyz[3],wxyz[2]))
	 +M(M(M(wxyz[1],wxyz[2]),wxyz[3]),wxyz[4]) - M(M(wxyz[1],wxyz[2]),M(wxyz[3],wxyz[4]))
	));
	end
);
