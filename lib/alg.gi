
#
#	alg implementation
#

InstallValue( AlgHelper@,
	rec(
		emptyAlg := dim ->
			Alg( dim, List([1..dim],i->[]) )
	,	incBasis := function( A, n )
		local z;
		z := List([1..Dimension(A)+n],i->0);
		return Alg(
				Dimension(A)+n,
				List( [1..Dimension(A)],i->List([1..i],function(j)
					if IsBound(A!.MT[i][j]) then return A!.MT[i][j]+z; fi; end) )
			);
		end
	)
);

InstallMethod( Alg,
	[IsPosInt,IsList],
	function( dim, mt )
	local V;
	V := Rationals^dim;
	SetMT(V,mt);
	SetClosure(V,Rationals^dim);
	return V;
	end
	);
	InstallMethod( Alg,
	[IsPosInt,IsPosInt,IsList],
	function( dim, cl, mt )
	local W, V;
	W := Rationals^cl;
	V := Subspace(W,Basis(W){[1..dim]});
	SetMT(V,mt);
	SetClosure(V,W);
	return V;
	end
	);
	InstallMethod( ViewString,
	[IsAlg],
	A -> Concatenation(
		"an alg of dim ",String(Dimension(A)) )
	);
	InstallMethod( PrintString,
	[IsAlg],
	A -> Concatenation(
		"Alg(\n",
			"\tRationals^",String(Dimension(A)),",\n",
			"\t",String(A!.MT),"\n",
		")"
	)
	);
	InstallMethod( TrivialAlg,
	[],
	function()
	return AlgHelper@.emptyAlg(0);
	end
);

InstallMethod( Mult,
	[IsAlg],
	A -> Mult( A, Closure(A), A!.MT )
	);

InstallMethod( IncreaseClosure,
	[IsAlg],
	function( A )
	local mt, n, i, j, z;
	if not HasClosure(A) then SetClosure(A,Rationals^Dimension(A)); fi;
	n := Dimension(Closure(A));
	mt := List([1..Dimension(Closure(A))],i->[]);
	for i in [1..Dimension(Closure(A))] do
		for j in [1..i] do # lower-triangular
			if IsBound(A!.MT[i]) and IsBound(A!.MT[i][j])
			then mt[i][j] := A!.MT[i][j];
			else
				n := n+1;
				mt[i][j] := KroneckerVector(n,n);
			fi;
		od;
	od;
	z := List([1..n],i->0);
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
	local Q, mt;
	Q := NaturalHomomorphismBySubspace( Closure(A), X );		
	mt := List(A!.MT,R -> List(R,e->Image(Q,e)));
	return Alg( Dimension(A) - Dimension(Intersection(A,X)),
							Dimension(Closure(A)) - Dimension(X), mt );
	end
);

InstallMethod( CloseUnderAct,
	[IsVectorSpace,IsGroup,IsFunction],
	function( V, G, act )
		local time, mb, vs, newvs, g, v, w, S;
		time := Runtime();
		mb := MutableBasis( Rationals, Basis(V), Zero(V) );
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
		S := VectorSpace( Rationals, BasisVectors(mb) );
		InfoPro("orbiting",time);
		return S;
		end
	);
InstallMethod( ImageUnderMult,
	[IsVectorSpace,IsVectorSpace,IsAlg],
	function( V, U, A )
		local time, mb, v, u, S;
		time := Runtime();
		mb := MutableBasis( Rationals, [], Zero(V) );
		for v in Basis(Intersection(A,V)) do for u in Basis(Intersection(A,U))
		do CloseMutableBasis( mb, Mult(A)(v,u) ); od; od;
		S := VectorSpace( Rationals, BasisVectors(mb), Zero(V) );
		InfoPro("multiplying",time);
		return S;
		end
	);
	InstallMethod( ImageUnderMult,
	[IsVector,IsVectorSpace,IsAlg],
	function( v, U, A )
	if not v in A then return TrivialSubspace(A);
	else return
		VectorSpace(Rationals,List(Basis(Intersection(A,U)),u->Mult(A)(v,u)));
	fi;
	end
	);
InstallMethod( IdealClosure,
	[IsAlg,IsVectorSpace],
	function( A, V )
	local W, X, Y;
	W := V;
	X := V;
	while true do
		X := ImageUnderMult( X,A,A );
		Y := W + X;
		if Dimension(Y) = Dimension(W) then break;
		else W := Y; fi;
	od;
	return W;
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
