
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
DeclareProperty( "IsIdempotent", IsAttrVector and HasAlg );
DeclareAttribute( "Fusion", IsAttrVector and IsIdempotent );
DeclareSynonym( "IsAxis", IsAttrVector and IsIdempotent and HasFusion );
DeclareAttribute( "Involution", IsAxis and IsIdempotent );
DeclareAttribute( "Miyamoto", IsAxis and IsIdempotent );
DeclareAttribute( "Eigenspaces", IsAxis );

DeclareOperation( "Axis", [IsAlg,IsGeneralizedRowVector,IsFusion] );
DeclareOperation( "Axis", [IsAlg,IsGeneralizedRowVector,IsFusion,IsMultiplicativeElementWithInverse] );
DeclareOperation( "Axis", [IsAlg,IsGeneralizedRowVector,IsFusion,IsMultiplicativeElementWithInverse,IsFunction] );

DeclareAttribute( "Relations", IsAxis );
DeclareOperation( "CheckLinearity", [IsAxis] );
DeclareOperation( "CheckDirectity", [IsAxis] );
DeclareOperation( "Check1Dimnlity", [IsAxis] );

DeclareAttribute( "CentralCharge", IsAttrVector and HasAlg );
DeclareAttribute( "Decomposition", IsIdempotent );

DeclareGlobalVariable( "AxisHelper@" );
