
#
#	library declarations
#

DeclareOperation( "DirectoryMtheory", [IsMtheory] );
DeclareOperation( "DirectoryMtheory", [IsString] );
DeclareOperation( "GetMrep", [IsMtheory] );
DeclareOperation( "GetMrep", [IsString,IsString] );
DeclareOperation( "GetMrep", [IsString,IsGroup] );
DeclareOperation( "GetMrep", [IsString,IsTrgp] );
DeclareOperation( "GetMrep", [IsMtheory,IsString] );
DeclareOperation( "GetMrep", [IsMtheory,IsGroup] );
DeclareOperation( "GetMrep", [IsMtheory,IsTrgp] );

DeclareOperation( "WriteMrep", [IsMrep,IsBool] );
DeclareOperation( "WriteMrep", [IsMrep] );
