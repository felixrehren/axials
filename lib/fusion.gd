
#
#  fusion declarations
#

FamilyFusion@ := NewFamily("FusionFamily");
DeclareCategory("IsFusion",IsObject);
DeclareRepresentation("IsFusionStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeFusion@ := NewType(FamilyFusion@,IsFusion and IsFusionStdRep);

DeclareOperation("Fusion",[IsRat,IsList,IsList,IsString]);
DeclareOperation("CentralCharge",[IsFusion]);
DeclareOperation("Fields",[IsFusion]);
DeclareOperation("Tag",[IsFusion]);
DeclareOperation("Fuse",[IsFusion]);

DeclareAttribute("Miyamoto",IsFusion);

DeclareOperation("VirasoroFusion",[IsPosInt,IsPosInt]);

DeclareProperty("IsVirasoroFusion",IsFusion);
DeclareProperty("IsRationalVirasoroFusion",IsVirasoroFusion);
DeclareProperty("IsUnitaryFusion",IsFusion);

### maybe move this in with shapes
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
