
#
#	alg implementation
#

InstallValue( AlgHelper@, rec(
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
			rr := FilteredNot(Mult(A)(i,i)-i,IsZero);
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
	SetMT(V,mt);
	SetClosure(V,W);
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
	A -> VectorSpace( LeftActingDomain(A), A!.MT, Zero(A) )
	);
	InstallMethod( IsClosed,
	[IsAlg],
	A -> Dimension(A) = Dimension(Closure(A)) 
	);
	InstallMethod( Mult,
	[IsAlg],
	A -> Mult( A, Closure(A), A!.MT )
	);
	InstallMethod( Ad,
	[IsAlg], # 1-dim'l algs??
	function( A )
	return function( v )
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
		local time, mb, v, u, S;
		time := Runtime();
		mb := MutableBasis( LeftActingDomain(A), [], Zero(V) );
		for v in Basis(Intersection(A,V)) do for u in Basis(Intersection(A,U))
		do CloseMutableBasis( mb, Mult(A)(v,u) ); od; od;
		S := VectorSpace( LeftActingDomain(A), BasisVectors(mb), Zero(V) );
		InfoPro("multiplying",time);
		return S;
		end
	);
	InstallMethod( ImageUnderMult,
	[IsVector,IsVectorSpace,IsAlg],
	function( v, U, A )
	if not v in A then return TrivialSubspace(A);
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
InstallMethod( Subalg,
	[IsAlg,IsVectorSpace],
	function( A, V )
		local W;
		#W := CloseUnderMult(V,V itself again!!,A);
		#then prep MT
	end
	);

InstallMethod( IncreaseClosure,
	[IsAlg],
	function( A )
	local mt, n, i, j, z;
	if not HasClosure(A) then SetClosure(A,LeftActingDomain(A)^Dimension(A)); fi;
	n := Dimension(Closure(A));
	mt := List([1..Dimension(Closure(A))],i->[]);
	for i in [1..Dimension(Closure(A))] do
		for j in [1..i] do # lower-triangular
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
	return Alg( Dimension(Closure(A)),n,mt );
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
	local Q, mt, f;
	if Dimension(X) = Dimension(Closure(A))
	then return AlgHelper@.trivialAlg; fi;
	Q := NaturalHomomorphismBySubspace( Closure(A), X );		
	f := Intersection(AlgHelper@.quoBasisPos(Q),[1..Dimension(A)]);
	mt := List(f,i->List(Intersection([1..i],f),j->Image(Q,A!.MT[i][j])));
	return Alg( Dimension(A) - Dimension(Intersection(A,X)),
							Dimension(Closure(A)) - Dimension(X), mt );
	end
);

InstallMethod( Identity,
	[IsAlg and IsClosed],
	function( A )
	local x, rr, i;
	x := List( [1..Dimension(A)], i -> Indeterminate( LeftActingDomain(A), i ) );
	rr := Concatenation(List( Basis(A), b -> Mult(A)(b,x) - b ));
	for i in [1..Length(rr)] do
		x := List(x,AlgHelper@.relToFn(rr[i]));
		rr := List(rr,AlgHelper@.relToFn(rr[i]));
	od;
	return InField(x);
	end
);

InstallMethod( Form,
	[IsAlg and HasFT],
	A -> Mult( A, LeftActingDomain(A), A!.FT )
	);
InstallMethod( CentralCharge,
	[IsAlg and IsClosed],
	A -> 1/2*Form(A)(Identity(A),Identity(A))
	);

InstallMethod( Idempotents, "in subspace of an axial alg",
	[IsAlg and IsClosed,IsVectorSpace],
	function( A, V )
		local B, i;
		B := Basis(V);
		i := Sum([1..Dimension(V)], i -> Indeterminate(LeftActingDomain(A),i)*B[i]);
		return Set(AlgHelper@.idempotentSolns(A,i));
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
