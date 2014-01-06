
#
#	representations declarations
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
DeclareOperation( "TrivialAxialRep", [IsFusion,IsTrgp,IsField] );
DeclareProperty ( "IsTrivial", IsAxialRep );
DeclareAttribute( "Alg", IsAxialRep );
DeclareAttribute( "Trgp", IsAxialRep );
DeclareAttribute( "Fusion", IsAxialRep );
DeclareAttribute( "SpanningWords", IsAxialRep );

DeclareAttribute( "Symmetries", IsAxialRep );
DeclareAttribute( "Miyamoto", IsAxialRep );
DeclareAttribute( "MiyamotoHom", IsAxialRep );
DeclareAttribute( "Orbiter", IsAxialRep );

DeclareAttribute( "Alphabet", IsAxialRep );
DeclareAttribute( "InWords", IsAxialRep );
DeclareAttribute( "FromWord", IsAxialRep );
DeclareOperation( "Axis", [IsAlg and HasAxialRep,IsGeneralizedRowVector,IsFusion,IsMultiplicativeElementWithInverse] );

DeclareOperation( "Im", [IsMapping,IsAxialRep] );
DeclareOperation( "IdealClosure", [IsAxialRep,IsVectorSpace] );
DeclareOperation( "Quotient", [IsAxialRep,IsVectorSpace] );
DeclareOperation( "IncreaseClosure", [IsAxialRep] );
DeclareOperation( "ChangeField", [IsAxialRep,IsField] );

DeclareOperation( "FindAxialRep", [HasShape,IsFusion,IsGroup,IsList] );
DeclareOperation( "FindAxialRep", [HasShape,IsFusion] );
DeclareOperation( "FindAxialRep", [IsGroup,IsSakuma,IsFusion] );
DeclareOperation( "FindUniversalAxialRep", [IsTrgp,IsFusion] );
DeclareOperation( "AxialSubrep", [IsAxialRep,IsGroup] );
DeclareOperation( "FindAxialRep", [IsList] );
DeclareOperation( "FindOtherSakumas", [IsAxialRep] );

DeclareAttribute( "Explosion", IsAxialRep );
DeclareOperation( "RecogniseShape", [IsAxialRep] );

DeclareOperation( "CosetAxis", [IsAxialRep,IsGroup] );
DeclareOperation( "CosetAxis", [IsAxialRep,IsGroup,IsGroup] );
DeclareOperation( "FixOfCentraliser", [IsAxialRep,IsAxis] );
