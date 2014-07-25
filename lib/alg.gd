
#
#	alg declarations
#

DeclareInfoClass( "mai" );
SetInfoLevel( mai, 3 );

DeclareGlobalVariable( "AlgHelper@" );

DeclareAttribute( "MT", IsVectorSpace );
DeclareAttribute( "Closure", HasMT );
DeclareSynonym( "IsAlg", HasMT and HasClosure );
DeclareProperty( "IsCommutative", IsAlg );
DeclareAttribute( "Mult", IsAlg );
DeclareAttribute( "Ad", IsAlg );
DeclareOperation( "Ad", [IsAlg,IsVectorSpace] );
DeclareProperty( "IsClosed", IsAlg );
DeclareAttribute( "Relations", IsAlg );

DeclareOperation( "Alg", [IsVectorSpace,IsList] );
DeclareOperation( "Alg", [IsVectorSpace,IsVectorSpace,IsList] );
DeclareOperation( "Alg", [IsPosInt,IsList] );
DeclareOperation( "Alg", [IsPosInt,IsPosInt,IsList] );
DeclareOperation( "Alg", [IsVectorSpace,IsVectorSpace,IsList,IsInt] );
DeclareOperation( "ChangeField", [IsAlg,IsField] );

DeclareOperation( "CloseUnderAct", [IsVectorSpace,IsGroup,IsFunction] );
DeclareOperation( "ImageUnderMult", [IsVectorSpace,IsVectorSpace,IsAlg] );
DeclareOperation( "ImageUnderMult", [IsVector,IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnderMult", [IsVectorSpace,IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnderMult", [IsVectorSpace,IsAlg] );
DeclareOperation( "CloseUnder",
	[IsVectorSpace,IsGroup,IsFunction,IsVectorSpace,IsAlg] );
DeclareOperation( "IdealClosure", [IsAlg,IsVectorSpace] );

DeclareOperation( "DerivedSubalg", [IsAlg,IsVectorSpace] );
DeclareOperation( "DerivedSubalg", [IsAlg,IsBasis] );
DeclareOperation( "SpanOfWords", [IsAlg,IsList,IsFunction] );

DeclareOperation( "IncreaseClosure", [IsAlg] );
DeclareOperation( "AddRelations", [IsAlg,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAlg,IsVectorSpace] );

DeclareAttribute( "FT", IsAlg and IsClosed );
DeclareAttribute( "Form", IsAlg );
DeclareAttribute( "CentralCharge", IsAlg and IsClosed );
DeclareAttribute( "OrthogonalComplement", IsAlg and HasFT );
DeclareOperation( "OrthogonalComplement", [IsAlg and HasFT,IsVectorSpace] );

DeclareAttribute( "Identity", IsAlg and IsClosed );
DeclareOperation( "Identity", [IsAlg and IsClosed,IsVectorSpace] );

DeclareAttribute( "Idempotents", IsAlg and IsClosed );
DeclareOperation( "Idempotents", [IsAlg and IsClosed,IsVectorSpace] );
DeclareOperation( "IsAssociativeSubalgebra", [IsAlg,IsVectorSpace] );
DeclareAttribute( "AssociativeSubalgebras", IsAlg and IsClosed );
DeclareOperation( "AssociativeSubalgebras", [IsAlg and IsClosed,IsVectorSpace]);
DeclareOperation( "UnitaryRationalVirasoroAxes", [IsAlg and IsClosed and HasFT] );

DeclareAttribute( "Axes", IsAlg );
DeclareSynonym( "IsAxialAlg", IsAlg and HasAxes );
DeclareOperation( "EnforceAxioms", [IsAxialAlg,IsList] );
DeclareAttribute( "AxialRep", IsAlg );

DeclareOperation( "Matsuo", [IsTrgp,IsRat,IsRat] );
DeclareOperation( "2Matsuo", [IsTrgp,IsRat,IsRat] );
DeclareOperation( "DLMN", [IsString,IsPosInt] );

DeclareAttribute( "Plusses", IsAlg );

DeclareOperation( "ParabolicChain", [IsAlg] );
DeclareOperation( "ParabolicChain", [IsAlg,IsVectorSpace] );
DeclareOperation( "ParabolicTorus", [IsAlg] );
DeclareOperation( "FlatTorus", [IsAlg] );
DeclareOperation( "ToralBasis", [IsAlg,IsList] );
DeclareOperation( "ToralDecomposition", [IsAlg,IsList] );
DeclareOperation( "ToralReconstruct", [IsList,IsField] );

DeclareAttribute( "IsJordan", IsAlg );
DeclareOperation( "IsJordan", [IsAlg,IsVectorSpace] );
