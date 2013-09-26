
#
#	alg declarations
#

DeclareInfoClass( "mai" );
SetInfoLevel( mai, 3 );

DeclareAttribute( "MT", IsVectorSpace );
DeclareAttribute( "Closure", HasMT );
DeclareSynonym( "IsAlg", HasMT and HasClosure );
DeclareAttribute( "Mult", IsAlg );
DeclareAttribute( "Ad", IsAlg );
DeclareOperation( "Ad", [IsAlg,IsVectorSpace] );
DeclareProperty( "IsClosed", IsAlg );
DeclareAttribute( "Relations", IsAlg );

DeclareAttribute( "Axes", IsAlg );
DeclareSynonym( "IsAxialAlg", IsAlg and HasAxes );

DeclareGlobalVariable( "AlgHelper@" );

DeclareOperation( "Alg", [IsVectorSpace,IsList] );
DeclareOperation( "Alg", [IsVectorSpace,IsVectorSpace,IsList] );
DeclareOperation( "Alg", [IsPosInt,IsList] );
DeclareOperation( "Alg", [IsPosInt,IsPosInt,IsList] );
DeclareOperation( "ChangeField", [IsAlg,IsField] );

DeclareOperation( "CloseUnderAct", [IsVectorSpace,IsGroup,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVectorSpace,IsVectorSpace,IsAlg] );
DeclareOperation( "ImageUnderMult", [IsVector,IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnderMult", [IsVectorSpace,IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnderMult", [IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnder",
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsAlg] );
DeclareOperation( "IdealClosure", [IsAlg,IsVectorSpace] );

DeclareOperation( "Centraliser", [IsVectorSpace,IsGroup] );

DeclareOperation( "DerivedSubalg", [IsAlg,IsVectorSpace] );
DeclareOperation( "DerivedSubalg", [IsAlg,IsBasis] );
DeclareOperation( "SpanOfWords", [IsAlg,IsList,IsFunction] );

DeclareOperation( "IncreaseClosure", [IsAlg] );
DeclareOperation( "AddRelations", [IsAlg,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAlg,IsVectorSpace] );

DeclareAttribute( "Identity", IsAlg and IsClosed );
DeclareAttribute( "FT", IsAlg and IsClosed );
DeclareAttribute( "Form", IsAlg and HasFT );
DeclareAttribute( "CentralCharge", IsAlg and IsClosed );

DeclareAttribute( "Idempotents", IsAlg and IsClosed );
DeclareOperation( "Idempotents", [IsAlg and IsClosed,IsVectorSpace] );
DeclareOperation( "IsAssociativeSubalgebra", [IsAlg,IsVectorSpace] );
DeclareAttribute( "AssociativeSubalgebras", IsAlg and IsClosed );
DeclareOperation( "AssociativeSubalgebras", [IsAlg and IsClosed,IsVectorSpace]);
DeclareOperation( "UnitaryRationalVirasoroAxes", [IsAlg and IsClosed and HasFT] );
