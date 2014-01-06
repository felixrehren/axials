
#
#  fusion declarations
#

FamilyFusion@ := NewFamily("FusionFamily");
DeclareCategory("IsFusion",IsObject);
DeclareRepresentation("IsFusionStdRep",
	IsFusion and IsComponentObjectRep and IsAttributeStoringRep,[]);
TypeFusion@ := NewType(FamilyFusion@,IsFusion and IsFusionStdRep);

DeclareOperation("Fusion",[IsRat,IsList,IsList,IsString]);
DeclareAttribute("CentralCharge",IsFusion);
DeclareAttribute("Fields",IsFusion);
DeclareAttribute("Tag",IsFusion);
DeclareAttribute("Fuse",IsFusion);
DeclareOperation("Subfusion",[IsFusion,IsList,IsString]);
DeclareAttribute("Miyamoto",IsFusion);
DeclareOperation("MiyamotoFixedFusion",[IsFusion]);
DeclareOperation("ChangeFields",[IsFusion,IsList,IsString]);

DeclareOperation("VirasoroFusion",[IsPosInt,IsPosInt]);
DeclareProperty("IsVirasoroFusion",IsFusion);
DeclareProperty("IsRationalVirasoroFusion",IsVirasoroFusion);
DeclareAttribute("VirasoroP",IsRationalVirasoroFusion);
DeclareAttribute("VirasoroQ",IsRationalVirasoroFusion);
DeclareProperty("IsUnitaryFusion",IsFusion);

DeclareGlobalVariable("MajoranaFusion");
DeclareGlobalVariable("FischerFusion");
