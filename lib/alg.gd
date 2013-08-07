
#
#	alg declarations
#

FamilyAxes@ := NewFamily("AxesFamily");
DeclareCategory("IsAxis",IsObject);
DeclareRepresentation("IsAxisStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeAxis@ := NewType(FamilyAxes@,IsAxis and IsAxisStdRep);

FamilyMalg@ := NewFamily("MalgFamily");
DeclareCategory("IsMalg",IsObject);
DeclareRepresentation("IsMalgStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeMalg@ := NewType(FamilyMalg@,IsMalg and IsMalgStdRep);

DeclareInfoClass( "mai" );
SetInfoLevel( mai, 3 );

DeclareGlobalVariable( "MalgHelper@" );

DeclareOperation( "Malg", [IsVectorSpace,IsVectorSpace,IsList] );
DeclareOperation( "Malg", [IsVectorSpace,IsList] );
DeclareOperation( "TrivialMalg", [] );
DeclareAttribute( "Dimension", IsMalg );
DeclareAttribute( "DimensionOuter", IsMalg );
DeclareAttribute( "Basis", IsMalg );
DeclareAttribute( "Axes", IsMalg );
DeclareAttribute( "AutomorphismGroup", IsMalg );
DeclareAttribute( "Relations", IsMalg );
DeclareAttribute( "Zero", IsMalg );
DeclareProperty( "Trivial", IsMalg );
DeclareProperty( "Closed", IsMalg );

DeclareOperation( "AddRelations", [IsMalg,IsVectorSpace] );
DeclareOperation( "IncreaseClosure", [IsMalg] );
