
#
#	alg declarations
#

DeclareInfoClass( "mai" );
SetInfoLevel( mai, 3 );

DeclareAttribute( "MT", IsVectorSpace );
DeclareSynonym( "IsAlg", HasMT );
DeclareAttribute( "Mult", IsAlg );
DeclareAttribute( "Closure", IsAlg );
DeclareProperty( "IsClosed", IsAlg );
DeclareAttribute( "Relations", IsAlg );

DeclareAttribute( "Axes", IsAlg );

DeclareGlobalVariable( "AlgHelper@" );

DeclareOperation( "Alg", [IsPosInt,IsList] );
DeclareOperation( "Alg", [IsPosInt,IsPosInt,IsList] );
DeclareOperation( "TrivialAlg", [] );
DeclareOperation( "IncreaseClosure", [IsAlg] );
DeclareOperation( "AddRelations", [IsAlg,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAlg,IsVectorSpace] );

DeclareOperation( "CloseUnderAct", [IsVectorSpace,IsGroup,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVectorSpace,IsVectorSpace,IsAlg] );
DeclareOperation( "ImageUnderMult", [IsVector,IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnder",
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsAlg] );
DeclareOperation( "IdealClosure", [IsAlg,IsVectorSpace] );

