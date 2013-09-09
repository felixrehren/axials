
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
DeclareOperation( "ChangeField", [IsAxialRep,IsField] );
DeclareOperation( "Rebase", [IsAxialRep] );

DeclareOperation( "FindAxialRep", [HasShape,IsFusion,IsGroup,IsList] );
DeclareOperation( "FindAxialRep", [HasShape,IsFusion] );
DeclareOperation( "FindAxialRep", [IsGroup,IsSakuma,IsFusion] );
DeclareOperation( "FindUniversalAxialRep", [IsTrgp,IsFusion] );
DeclareOperation( "AxialSubrep", [IsAxialRep,IsGroup] );
DeclareOperation( "FindAxialRep", [IsList] );
DeclareOperation( "FindOtherSakumas", [IsAxialRep] );

DeclareOperation( "FindForm", [IsAxialRep] );
DeclareOperation( "Explode", [IsAxialRep] );
DeclareOperation( "FindShape", [IsAxialRep] );

