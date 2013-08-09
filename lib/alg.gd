
#
#	alg declarations
#

DeclareInfoClass( "mai" );
SetInfoLevel( mai, 3 );

DeclareAttribute( "MT", IsVectorSpace );
DeclareSynonym( "IsMalg", HasMT );
DeclareAttribute( "Mult", IsMalg );
DeclareAttribute( "Closure", IsMalg );
DeclareProperty( "Closed", IsMalg );
DeclareAttribute( "Relations", IsMalg );

DeclareAttribute( "Axes", IsMalg );

DeclareGlobalVariable( "MalgHelper@" );

DeclareOperation( "Malg", [IsPosInt,IsList] );
DeclareOperation( "Malg", [IsPosInt,IsPosInt,IsList] );
DeclareOperation( "TrivialMalg", [] );
DeclareOperation( "AddRelations", [IsMalg,IsVectorSpace] );
DeclareOperation( "IncreaseClosure", [IsMalg] );

DeclareOperation( "CloseUnderAct", [IsVectorSpace,IsGroup,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVectorSpace,IsVectorSpace,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVector,IsVectorSpace,IsFunction] );
DeclareOperation( "CloseUnder",
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsFunction] );
DeclareOperation( "IdealClosure", [IsMalg,IsVectorSpace] );

