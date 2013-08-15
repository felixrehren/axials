
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
DeclareAttribute( "Eigenvectors", IsAttrVector and HasAlg );
DeclareProperty( "IsIdempotent", IsAttrVector and HasAlg );
DeclareAttribute( "Fusion", IsAttrVector and IsIdempotent );
DeclareSynonym( "IsAxis", IsAttrVector and IsIdempotent and HasFusion );
DeclareAttribute( "Involution", IsAxis and IsIdempotent );
DeclareAttribute( "Miyamoto", IsAxis and IsIdempotent );
DeclareAttribute( "Eigenspaces", IsAxis );

DeclareOperation( "Axis", [IsAlg,IsVector,IsFusion] );
DeclareOperation( "Axis", [IsAlg,IsVector,IsFusion,IsMultiplicativeElementWithInverse] );
DeclareOperation( "Axis", [IsAlg,IsVector,IsFusion,IsMultiplicativeElementWithInverse,IsFunction] );

DeclareOperation( "CheckLinearity", [IsAxis] );
DeclareOperation( "CheckDirectity", [IsAxis] );

DeclareGlobalVariable( "AxisHelper@" );
