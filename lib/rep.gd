
#
#	create declarations
#

FamilyAxialRep@ := NewFamily("AxialRepFamily");
DeclareCategory("IsAxialRep",IsObject);
DeclareRepresentation("IsAxialRepStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeAxialRep@ := NewType(FamilyAxialRep@,IsAxialRep and IsAxialRepStdRep);
DeclareInfoClass( "AxRepInfo" );
SetInfoLevel( AxRepInfo, 5 );

DeclareGlobalVariable( "AxialRepHelper@" );

DeclareOperation( "AxialRep", [IsFusion,IsTrgp,IsAlg,IsDictionary,IsList] );
DeclareOperation( "AxialRep", [IsFusion,IsTrgp,IsAlg,IsList,IsList] );
DeclareAttribute( "Alg", IsAxialRep );
DeclareAttribute( "Trgp", IsAxialRep );
DeclareAttribute( "Fusion", IsAxialRep );
DeclareAttribute( "SpanningWords", IsAxialRep );

DeclareAttribute( "Symmetries", IsAxialRep );
DeclareProperty ( "IsTrivial", IsAxialRep );

DeclareAttribute( "Alphabet", IsAxialRep );
DeclareAttribute( "InWords", IsAxialRep );
DeclareAttribute( "FromWord", IsAxialRep );
DeclareAttribute( "Axes", IsAxialRep );

DeclareOperation( "Im", [IsMapping,IsAxialRep] );
DeclareOperation( "IdealClosure", [IsAxialRep,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAxialRep,IsVectorSpace] );
DeclareOperation( "IncreaseClosure", [IsAxialRep] );
DeclareOperation( "Subrepresentation", [IsAxialRep,IsGroup] );

DeclareOperation( "FindAxialRep", [HasShape,IsFusion,IsGroup,IsList] );
DeclareOperation( "FindAxialRep", [HasShape,IsFusion] );
DeclareOperation( "FindAxialRep", [IsGroup,IsSakuma,IsFusion] );
DeclareOperation( "FindUniversalAxialRep", [IsTrgp,IsFusion] );

DeclareOperation( "FindForm", [IsAxialRep] );
DeclareOperation( "Explode", [IsAxialRep] );

DeclareGlobalVariable( "Field@" );
InstallValue( Field@, Rationals );
MakeReadWriteGlobal("Field@axials");

DeclareOperation( "ChangeField", [IsAxialRep,IsField] );
