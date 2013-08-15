
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
	return V;
	end
	);
	InstallMethod( Alg,
	[IsPosInt,IsPosInt,IsList],
	function( dim, cl, mt )
	local A;
	A := Alg( dim, mt );
	SetClosure(A,Rationals^cl);
	return A;
	end
	);
	InstallMethod( ViewString,
	[IsAlg],
	A -> Concatenation(
		"an M-alg of dim ",String(Dimension(A)) )
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

InstallMethod( AddRelations,
	[IsAlg,IsVectorSpace],
	function( A, X )
	if HasRelations(A) then A!.Relations := Relations(A) + X;
	else SetRelations(A,X); fi;
	end
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
	[IsVectorSpace,IsVectorSpace,IsFunction],
	function( V, U, mult )
		local time, mb, v, u, S;
		time := Runtime();
		mb := MutableBasis( Rationals, [], Zero(V) );
		for v in Basis(V) do for u in Basis(U)
		do CloseMutableBasis( mb, mult(v,u) ); od; od;
		S := VectorSpace( Rationals, BasisVectors(mb), Zero(V) );
		InfoPro("multiplying",time);
		return S;
		end
	);
	InstallMethod( ImageUnderMult,
	[IsVector,IsVectorSpace,IsFunction],
	function( v, U, mult )
	return VectorSpace( Rationals, List(Basis(U),u->mult(v,u)) );
	end
	);
	InstallMethod( CloseUnder,
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsFunction],
	function( V, G, act, U, mult )
		local W, X, Y, Z;
		W := V;
		Y := V;
		while true do
			X := CloseUnderAct( Y, G, act );
			W := W + X;
			Y := ImageUnderMult( X, U, mult ); 
			Z := W + Y;
			if Dimension(Z) = Dimension(W) then break;
			else W := Z; fi;
		od;
		return W;
		end
);
