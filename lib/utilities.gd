
#
#	utilities declarations
#

# lists: positions
	DeclareOperation( "FilteredPositions", [IsList,IsFunction] );
	DeclareOperation( "FirstPosition", [IsList,IsFunction] );
	DeclareOperation( "LastNonzeroPos", [IsList] );
	DeclareOperation( "KroneckerVector", [IsPosInt,IsPosInt] );
	DeclareOperation( "Independify", [IsList,IsList] );

# lists: logic
	DeclareOperation( "Count", [IsList,IsFunction] );

# lists: ordering
	DeclareOperation( "Sorted", [IsList,IsFunction] );
	DeclareOperation( "Sorted", [IsList] );
	DeclareOperation( "RecursiveSorted", [IsList] );
	DeclareOperation( "PartitionBy", [IsList,IsFunction] );
	DeclareOperation( "SortedTo", [IsList,IsFunction,IsList] );

# lists: comprehension
	DeclareOperation( "Recursive", [IsFunction] );
	DeclareOperation( "All", [IsList] );
	DeclareOperation( "All", [IsBool] );
	DeclareOperation( "Any", [IsList] );
	DeclareOperation( "Any", [IsBool] );

# dict
	DeclareOperation( "CreateDictionary", [IsList,IsFunction] );
	DeclareOperation( "CreateDictionary", [IsList,IsList] );
	DeclareOperation( "CreateDictionary", [IsList] );

# actions
	DeclareOperation( "OnPointsRecursive",
		[IsObject,IsMultiplicativeElementWithInverse] );

# this one is tough to name
	DeclareOperation( "Mult", [IsVectorSpace,IsVectorSpace,IsList] );
	DeclareGlobalFunction( "AsRat" );

# user
	DeclareOperation( "UserChoice", [IsString,IsList] );

# profiling
	DeclareOperation( "ElapseStr", [IsPosInt] );
	DeclareInfoClass( "pro" );
	SetInfoLevel( pro, 2 );
	DeclareOperation( "InfoPro", [IsString,IsPosInt] );
