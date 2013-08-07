
#
#	alg implementation
#

InstallValue( MalgHelper@,
	rec(
		emptyMalg := dim ->
			Malg( Rationals^dim, List([1..dim],i->[]) )
	,	incBasis := function( A, n )
		return Objectify( 
			TypeMalg@,
			rec(
				V := Rationals^(Dimension(A)+n),
				mt := List( [1..Dimension(A)],i->List([1..i],function(j)
					if IsBound(A!.mt[i][j]) then return A!.mt[i][j]+Zero(~.V); fi; end))
			) );
		end
	)
);

InstallMethod( Malg,
	[IsVectorSpace,IsVectorSpace,IsList],
	function( V, W, mt )
	return Objectify( 
		TypeMalg@,
		rec(
			V := V,
			W := W,
			mt := mt ## lower-triangular
		) );
	end
	);
	InstallMethod( Malg,
	[IsVectorSpace,IsList],
	function( V, mt )
	return Malg( V, V, mt );
	end
	);
	InstallMethod( ViewString,
	[IsMalg],
	A -> Concatenation(
		"an M-alg of dim ",String(Dimension(A)) )
	);
	InstallMethod( PrintString,
	[IsMalg],
	A -> Concatenation(
		"Malg(\n",
			"\tRationals^",String(Dimension(A)),",\n",
			"\t",String(A!.mt),"\n",
		")"
	)
);

InstallMethod( TrivialMalg,
	[],
	function()
	return MalgHelper@.emptyMalg(0);
	end
);

InstallMethod( Basis,
	[IsMalg],
	A -> Basis(A!.V)
	);
InstallMethod( Dimension,
	[IsMalg],
	A -> Dimension(A!.V)
	);
InstallMethod( DimensionOuter,
	[IsMalg],
	A -> Dimension(A!.W)
	);
InstallMethod( Zero,
	[IsMalg],
	A -> Zero(A!.V)
	);
InstallMethod( Trivial,
	[IsMalg],
	A -> IsZero(Dimension(A!.V))
	);

InstallMethod( AddRelations,
	[IsMalg,IsVectorSpace],
	function( A, X )
	if HasRelations(A) then A!.Relations := Relations(A) + X;
	else SetRelations(A,X); fi;
	end
	);

InstallMethod( IncreaseClosure,
	[IsMalg],
	function( A )
	local mt, n, i, j, W;
	n := DimensionOuter(A);
	mt := List([1..DimensionOuter(A)],i->[]);
	for i in [1..DimensionOuter(A)] do
		for j in [1..i] do # lower-triangular
			if IsBound(A!.mt[i]) and IsBound(A!.mt[i][j])
			then mt[i][j] := A!.mt[i][j];
			else
				n := n+1;
				mt[i][j] := KroneckerVector(n,n);
			fi;
		od;
	od;
	W := Rationals^n;
	for i in [1..DimensionOuter(A)] do for j in [1..i]
	do mt[i][j] := mt[i][j] + Zero(W); od; od;
	return Malg( Rationals^DimensionOuter(A),W,mt );
	end
	);
