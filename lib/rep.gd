
#
#	create declarations
#

FamilyAxialRep@ := NewFamily("AxialRepFamily");
DeclareCategory("IsAxialRep",IsObject);
DeclareRepresentation("IsAxialRepStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeAxialRep@ := NewType(FamilyAxialRep@,IsAxialRep and IsAxialRepStdRep);

DeclareGlobalVariable( "AxialRepHelper@" );

DeclareOperation( "AxialRep", [IsFusion,IsTrgp,IsAlg,IsDictionary,IsList] );
DeclareOperation( "AxialRep", [IsFusion,IsTrgp,IsAlg,IsList,IsList] );
DeclareAttribute( "Alg", IsAxialRep );
DeclareOperation( "Trgp", [IsAxialRep] );

DeclareAttribute( "Fusion", IsAxialRep );
DeclareAttribute( "Basis", IsAxialRep );
DeclareAttribute( "Dimension", IsAxialRep );
DeclareProperty( "Trivial", IsAxialRep );
DeclareAttribute( "Alphabet", IsAxialRep );
DeclareAttribute( "Axes", IsAxialRep );

DeclareOperation( "ImageX", [IsMapping,IsAxialRep] );
DeclareOperation( "IncreaseClosure", [IsAxialRep] );

DeclareOperation( "StartAxialRep", [HasShape,IsFusion] );
DeclareOperation( "AddIdempotentRelations", [IsAxialRep] );
DeclareOperation( "FindAxialRep", [IsTrgp,IsFusion] );
DeclareOperation( "FindAxialReps", [IsTrgp,IsFusion] );

DeclareOperation( "ConvertAxialRep", [IsRecord,IsFusion] );
DeclareOperation( "ConvertAxialReps", [IsDirectory,IsFusion] );

DeclareOperation( "IdealClosure", [IsAxialRep,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAxialRep,IsVectorSpace] );
