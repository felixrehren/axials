
#
#	create declarations
#

FamilyMrep@ := NewFamily("MrepFamily");
DeclareCategory("IsMrep",IsObject);
DeclareRepresentation("IsMrepStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeMrep@ := NewType(FamilyMrep@,IsMrep and IsMrepStdRep);

DeclareGlobalVariable( "MrepHelper@" );

DeclareOperation( "Alg", [IsMrep] );
DeclareOperation( "Trgp", [IsMrep] );
DeclareOperation( "GroupX", [IsMrep] );

DeclareAttribute( "Theory", IsMrep );
DeclareAttribute( "Basis", IsMrep );
DeclareAttribute( "Dimension", IsMrep );
DeclareProperty( "Trivial", IsMrep );
DeclareAttribute( "Alphabet", IsMrep );

DeclareOperation( "ImageX", [IsMapping,IsMrep] );

DeclareOperation( "StartMrep", [HasShape,IsMtheory] );
DeclareOperation( "FindMrep", [IsTrgp,IsMtheory] );
DeclareOperation( "FindMreps", [IsTrgp,IsMtheory] );


### temp
DeclareOperation( "LoadMrep", [HasShape,IsString] );
DeclareOperation( "LoadMrep", [HasShape,IsMtheory] );
