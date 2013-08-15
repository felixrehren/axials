
#
#	library declarations
#

DeclareOperation( "DirectoryFusion", [IsFusion] );
DeclareOperation( "DirectoryFusion", [IsString] );
DeclareOperation( "GetAxialRep", [IsFusion] );
DeclareOperation( "GetAxialRep", [IsString,IsString] );
DeclareOperation( "GetAxialRep", [IsString,IsGroup] );
DeclareOperation( "GetAxialRep", [IsFusion,IsString] );
DeclareOperation( "GetAxialRep", [IsFusion,IsGroup] );

DeclareOperation( "WriteAxialRep", [IsAxialRep,IsBool] );
DeclareOperation( "WriteAxialRep", [IsAxialRep] );
