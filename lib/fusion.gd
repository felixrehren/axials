
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
DeclareProperty("IsUnitaryFusion",IsFusion);

DeclareOperation("VirasoroFusion",[IsPosInt,IsPosInt]);
DeclareProperty("IsVirasoroFusion",IsFusion);
DeclareProperty("IsRationalVirasoroFusion",IsVirasoroFusion);
DeclareAttribute("VirasoroP",IsRationalVirasoroFusion);
DeclareAttribute("VirasoroQ",IsRationalVirasoroFusion);
DeclareOperation("KacEntry",[IsRationalVirasoroFusion,IsPosInt,IsPosInt]);
DeclareOperation("KacPosition",[IsRationalVirasoroFusion,IsRat]);

DeclareOperation("VirasoroRamond",[IsPosInt]);
DeclareOperation("VirasoroNeveuSchwarz",[IsPosInt]);

DeclareGlobalVariable("MajoranaFusion");
DeclareOperation("JordanFusion",[IsRat]);
DeclareGlobalVariable("FischerFusion");
