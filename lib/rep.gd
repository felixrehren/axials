
#
#	create declarations
#

FamilyMrep@ := NewFamily("MrepFamily");
DeclareCategory("IsMrep",IsObject);
DeclareRepresentation("IsMrepStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeMrep@ := NewType(FamilyMrep@,IsMrep and IsMrepStdRep);

DeclareGlobalVariable( "MrepHelper@" );

DeclareOperation( "Mrep", [IsMtheory,IsTrgp,IsMalg,IsFunction,IsList] );
DeclareOperation( "Mrep", [IsMtheory,IsTrgp,IsMalg,IsList,IsList] );
DeclareOperation( "Alg", [IsMrep] );
DeclareOperation( "Trgp", [IsMrep] );
DeclareOperation( "GroupX", [IsMrep] );

DeclareAttribute( "Mtheory", IsMrep );
DeclareAttribute( "Basis", IsMrep );
DeclareAttribute( "Dimension", IsMrep );
DeclareProperty( "Trivial", IsMrep );
DeclareAttribute( "Alphabet", IsMrep );

DeclareOperation( "ImageX", [IsMapping,IsMrep] );

DeclareOperation( "StartMrep", [HasShape,IsMtheory] );
DeclareOperation( "AddIdempotentRelations", [IsMrep] );
DeclareOperation( "FindMrep", [IsTrgp,IsMtheory] );
DeclareOperation( "FindMreps", [IsTrgp,IsMtheory] );

DeclareOperation( "ConvertMrep", [IsRecord,IsMtheory] );
DeclareOperation( "ConvertMreps", [IsDirectory,IsMtheory] );

