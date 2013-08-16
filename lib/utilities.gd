
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
	DeclareOperation( "Any", [IsList] );

# dict
	DeclareOperation( "CreateDictionary", [IsCollection,IsFunction] );
	DeclareOperation( "CreateDictionary", [IsCollection,IsCollection] );

# actions
	DeclareOperation( "OnPointsRecursive",
		[IsObject,IsMultiplicativeElementWithInverse] );

# this one is tough to name
	DeclareOperation( "Mult", [IsVectorSpace,IsVectorSpace,IsList] );

# user
	DeclareOperation( "UserChoice", [IsString,IsList] );

# profiling
	DeclareOperation( "ElapseStr", [IsPosInt] );
	DeclareInfoClass( "pro" );
	SetInfoLevel( pro, 2 );
	DeclareOperation( "InfoPro", [IsString,IsPosInt] );
