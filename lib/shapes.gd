
#
#  shapes declarations
#

FamilySakuma@ := NewFamily("SakumaFamily");
DeclareCategory("IsSakuma",IsObject);
DeclareRepresentation("IsSakumaStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeSakuma@ := NewType(FamilySakuma@,IsSakuma and IsSakumaStdRep);

DeclareOperation("Sakuma",[IsList,IsMatrix]);
DeclareOperation("GetAlgebra",[IsSakuma,IsPosInt,IsString]);
DeclareOperation("GetAlgebras",[IsSakuma,IsPosInt]);
DeclareOperation("SubAlgebras",[IsSakuma,IsList]);
DeclareOperation("SupAlgebras",[IsSakuma,IsList]);
DeclareAttribute("Orders",IsSakuma);
DeclareOperation("Classes",[IsSakuma]);

DeclareGlobalVariable("MajoranaSakuma");
DeclareGlobalVariable("FischerSakuma");

DeclareOperation("ObservedSakuma",[IsFusion]);

DeclareAttribute("Shape",IsTrgp);

DeclareOperation("IsShape",[IsString,IsSakuma]);
DeclareOperation("TranspositionGroup",[IsGroup,IsCollection,IsList]);
DeclareOperation("TrgpNC",[IsGroup,IsCollection,IsList]);

DeclareOperation("Shapes",[IsGroup,IsSakuma]);
DeclareOperation("MajoranaShapes", [IsGroup]);
DeclareOperation("ShapeStr",[IsList]);
DeclareOperation("ShapeStr",[HasShape]);
DeclareOperation("ShapeStrMlts",[HasShape]);
DeclareOperation("ShapeGraph",[HasShape]);

DeclareOperation("IsIsomOfShapes",[HasShape,HasShape,IsMapping]);
DeclareOperation("IsIsomOfShapes",[IsMapping]);
DeclareOperation("AllShapeIsomClasses",[HasShape,HasShape]);
DeclareOperation("AreIsomorphicShapes",[HasShape,HasShape]);

DeclareOperation("Subshape",[HasShape,IsGroup]);
DeclareOperation("MaximalSubshapes",[HasShape]);
DeclareOperation("HasIsomorphicSubshape",[HasShape,HasShape]);

DeclareOperation("AutomorphismGroupShape",[HasShape]);

