
#
#  m theory declarations
#

FamilyMtheory@ := NewFamily("MtheoryFamily");
DeclareCategory("IsMtheory",IsObject);
DeclareRepresentation("IsMtheoryStdRep",
	IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeMtheory@ := NewType(FamilyMtheory@,IsMtheory and IsMtheoryStdRep);

DeclareOperation("Mtheory",[IsRat,IsList,IsList,IsString]);
DeclareOperation("CentralCharge",[IsMtheory]);
DeclareOperation("Fields",[IsMtheory]);
DeclareOperation("Tag",[IsMtheory]);
DeclareOperation("Fuse",[IsMtheory,IsRat,IsRat]);

DeclareAttribute("Axioms",IsMtheory);
DeclareAttribute("Miyamoto",IsMtheory);

DeclareOperation("VirasoroMtheory",[IsPosInt,IsPosInt]);

DeclareProperty("IsVirasoroMtheory",IsMtheory);
DeclareProperty("IsRationalVirasoroMtheory",IsVirasoroMtheory);
DeclareProperty("IsUnitaryMtheory",IsMtheory);

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
