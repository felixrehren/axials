
#
#	utilities declarations
#

# lists: positions
	DeclareOperation( "FilteredPositions", [IsList,IsFunction] );
	DeclareOperation( "FirstPosition", [IsList,IsFunction] );
	DeclareOperation( "LastNonzeroPos", [IsList] );

# lists: logic
	DeclareOperation( "Count", [IsList,IsFunction] );

# lists: ordering
	DeclareOperation( "Sorted", [IsList,IsFunction] );
	DeclareOperation( "Sorted", [IsList] );
	DeclareOperation( "RecursiveSorted", [IsList] );

# lists: comprehension
	DeclareOperation( "Recursive", [IsFunction] );
	DeclareOperation( "All", [IsList] );
	DeclareOperation( "Any", [IsList] );

# dict
	DeclareOperation( "CreateDictionary", [IsCollection,IsFunction] );

# actions
	DeclareOperation( "OnPointsRecursive",
		[IsMultiplicativeElementWithInverse,IsList] );
