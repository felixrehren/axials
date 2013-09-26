
#
#	library declarations
#

DeclareGlobalVariable( "LibHelper@" );

DeclareOperation( "GetAxialRep", [IsFusion] );
DeclareOperation( "GetAxialRep", [IsFusion,IsObject] );

DeclareOperation( "WriteAxialRep", [IsAxialRep] );

DeclareOperation( "DeleteAxialRep", [IsAxialRep] );
DeclareOperation( "DeleteAxialRep", [IsFusion,IsTrgp and HasShape] );
