
#
#	alg implementation
#

InstallValue( MalgHelper@,
	rec(
		basicMalg := function( dim )
		return Objectify( 
			TypeMalg@,
			rec(
				V := Rationals^dim,
				mt := List([1..dim],i->List([1..dim],j->[]))
			) );
		end
	,	incBasis := function( A, n )
		return Objectify( 
			TypeMalg@,
			rec(
				V := Rationals^(Dimension(A)+n),
				mt := List( [1..Dimension(A)],i->List([1..Dimension(A)],j->
					A!.mt[i][j]+Zero(~.V)) )
			) );
		end
	)
);

InstallMethod( TrivialMalg,
	[],
	function()
	return MalgHelper@.basicMalg(0);
	end
);

InstallMethod( Dimension,
	[IsMalg],
	A -> Dimension(A!.V)
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

InstallMethod( ViewString,
	[IsMalg],
	A -> Concatenation(
		"an M-alg of dim ",String(Dimension(A)) )
	);
