
#
#	axes declarations
#

FamilyAttrVector@ := NewFamily("AttrVectorFamily");
DeclareCategory("IsAttrVector",IsObject);
DeclareRepresentation("IsAttrVectorStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,["v"]);
TypeAttrVector@ := NewType(FamilyAttrVector@,
	IsAttrVector and IsAttrVectorStdRep);

DeclareOperation( "Vector", [IsAttrVector] );
# can't declare \+( IsAttrVector, IsVector )
# since IsVector is always? first treated as IsList
# and thereby weird (sort-of-pointwise) addition occurs

DeclareAttribute( "Alg", IsAttrVector );
DeclareAttribute( "Ad", IsAttrVector and HasAlg );
DeclareAttribute( "Eigenspaces", IsAttrVector and HasAlg );
DeclareProperty( "IsIdempotent", IsAttrVector and HasAlg );
DeclareAttribute( "Fusion", IsAttrVector and IsIdempotent );
DeclareSynonym( "IsAxis", IsAttrVector and IsIdempotent and HasFusion );
DeclareAttribute( "AxialRep", IsAxis );
DeclareAttribute( "Involution", IsAxis );
DeclareAttribute( "Miyamoto", IsAxis );

DeclareOperation( "Axis", [IsAlg,IsGeneralizedRowVector,IsFusion] );

DeclareAttribute( "Relations", IsAxis );
DeclareOperation( "CheckLinearity", [IsAxis] );
DeclareOperation( "CheckSemisimplicity", [IsAxis] );
DeclareOperation( "Check1Dimnlity", [IsAxis] );

DeclareAttribute( "CentralCharge", IsAttrVector and HasAlg );
DeclareAttribute( "Explosion", IsIdempotent );


DeclareGlobalVariable( "AxisHelper@" );
