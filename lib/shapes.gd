
#
#  shapes declarations
#

DeclareAttribute("Shape",IsTrgp);

DeclareOperation("IsShape",[IsString]);
DeclareOperation("TranspositionGroup",[IsGroup,IsCollection,IsList]);
DeclareOperation("TrgpNC",[IsGroup,IsCollection,IsList]);

DeclareOperation("Shapes",[IsGroup,IsSakuma]);
DeclareOperation("ShapeStr",[HasShape]);
DeclareOperation("ShapeStrMlts",[HasShape]);

DeclareOperation("IsIsomOfShapes",[HasShape,HasShape,IsMapping]);
DeclareOperation("IsIsomOfShapes",[IsMapping]);
DeclareOperation("AllShapeIsomClasses",[HasShape,HasShape]);
DeclareOperation("AreIsomorphicShapes",[HasShape,HasShape]);

DeclareOperation("Subshape",[HasShape,IsGroup]);
DeclareOperation("MaximalSubshapes",[HasShape]);
DeclareOperation("HasIsomorphicSubshape",[HasShape,HasShape]);

DeclareOperation("AutomorphismGroupShape",[HasShape]);
