
#
#  shapes declarations
#

DeclareAttribute("Shape",IsTrgp);

DeclareOperation("Shapes",[IsTrgp,IsSakuma]);
DeclareOperation("ShapeStr",[HasShape]);
DeclareOperation("ShapeStrMlts",[HasShape]);

DeclareOperation("IsIsomOfShapes",[HasShape,HasShape,IsMapping]);
DeclareOperation("AllShapeIsomClasses",[HasShape,HasShape]);
DeclareOperation("HasIsomSubshape",[HasShape,HasShape]);

DeclareOperation("Subshape",[HasShape,IsTrgp]);
DeclareOperation("Subshape",[HasShape,IsGroup]);
DeclareOperation("MaximalSubshapes",[HasShape]);
DeclareOperation("HasIsomorphicSubshape",[HasShape,HasShape]);

DeclareOperation("AutomorphismGroupShape",[HasShape]);
