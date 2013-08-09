
#
#	axes declarations
#

DeclareRepresentation("IsAttrVector",
	IsGeneralizedRowVector and IsAttributeStoringRep,[]);

DeclareAttribute( "Malg", IsVector );
DeclareAttribute( "Eigenvectors", IsVector and HasMalg );
DeclareProperty( "Idempotent", IsVector and HasMalg );
DeclareAttribute( "Mtheory", IsVector and IsIdempotent );
DeclareAttribute( "Miyamoto", IsVector and HasMtheory );
DeclareSynonymAttr( "IsAxis", IsVector and IsIdempotent and HasMtheory );

DeclareOperation( "Axis", [IsMalg,IsVector,IsMtheory] );

DeclareGlobalVariable( "AxisHelper@" );
