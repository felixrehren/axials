
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
DeclareOperation( "Eigenspaces", [IsAttrVector and HasAlg,IsList] );
DeclareAttribute( "Eigenspaces", IsAttrVector and HasAlg );
#DeclareOperation( "Eigenvalues", [IsAttrVector and HasAlg] );
DeclareProperty( "IsIdempotent", IsAttrVector and HasAlg );
DeclareAttribute( "Fusion", IsAttrVector and IsIdempotent );
DeclareSynonym( "IsAxis", IsAttrVector and IsIdempotent and HasFusion );
DeclareOperation( "ObservedFusion", [IsAttrVector and HasAlg,IsVectorSpace] );
DeclareAttribute( "ObservedFusion", IsAttrVector and HasAlg );
DeclareAttribute( "Involution", IsAxis );
DeclareAttribute( "Miyamoto", IsAxis );

DeclareOperation( "VectorInAlg", [IsAlg,IsGeneralizedRowVector] );
DeclareOperation( "Axis", [IsAlg,IsGeneralizedRowVector,IsFusion] );

DeclareAttribute( "Relations", IsAxis );
DeclareOperation( "CheckLinearity", [IsAxis] );
DeclareOperation( "CheckSemisimplicity", [IsAxis] );
DeclareOperation( "Check1Dimnlity", [IsAxis] );
DeclareOperation( "CheckFusion", [IsAxis] );

DeclareAttribute( "CentralCharge", IsAttrVector and HasAlg );
DeclareAttribute( "Explosion", IsIdempotent );

DeclareGlobalVariable( "AxisHelper@" );
