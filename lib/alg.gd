
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
DeclareOperation( "AddRelations", [IsAlg,IsVectorSpace] );
DeclareOperation( "IncreaseClosure", [IsAlg] );

DeclareOperation( "CloseUnderAct", [IsVectorSpace,IsGroup,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVectorSpace,IsVectorSpace,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVector,IsVectorSpace,IsFunction] );
DeclareOperation( "CloseUnder",
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsFunction] );
DeclareOperation( "IdealClosure", [IsAlg,IsVectorSpace] );

