
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

DeclareOperation( "TrivialMalg", [] );
DeclareAttribute( "Dimension", IsMalg );
DeclareAttribute( "Axes", IsMalg );
DeclareAttribute( "AutomorphismGroup", IsMalg );
DeclareAttribute( "Relations", IsMalg );
DeclareAttribute( "Zero", IsMalg );
DeclareProperty( "Trivial", IsMalg );
DeclareProperty( "Closed", IsMalg );

DeclareOperation( "AddRelations", [IsMalg,IsVectorSpace] );
