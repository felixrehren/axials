
#
#	library implementation
#

InstallMethod( DirectoryFusion,
	[IsString],
	function( str )
	return Directory(Filename(DirectoriesPackageLibrary("axials","data"),str));
	end
	);
	InstallMethod( DirectoryFusion,
	[IsFusion],
	th -> DirectoryFusion(Tag(th))
);

InstallMethod( GetAxialRep,
	[IsFusion],
	function( th )
	return Filtered(
		DirectoryContents(DirectoryFusion(th)),
		s -> s[1]<>'.');
	end 			## to do: how to create directories
	);
InstallMethod( GetAxialRep,
	[IsString,IsString],
	function( th, G )
	local file;
	file := Filename( DirectoryFusion(th), G );
	if IsReadableFile(file)
	then return ReadAsFunction(file)();
	else return []; fi;
	end
	);
	InstallMethod( GetAxialRep,
	[IsString,IsGroup],
	function( th, G )
	return GetAxialRep( th,StructureDescription(G:short) );
	end
	);
	InstallMethod( GetAxialRep,
	[IsString,IsTrgp],
	function( th, T )
	return Filtered(
		GetAxialRep(th,StructureDescription(T:short)),
		R -> AreIsomorphicTrgp(Trgp(R),T) );
	end
	);
	InstallMethod( GetAxialRep,
	[IsString,HasShape],
	function( th, S )
	local ff;
	ff := Filtered(
		GetAxialRep(th,StructureDescription(S:short)),
		R -> HasShape(Trgp(R)) ## always, right?
			and AreIsomorphicShapes(Trgp(R),S) );
	if Length(ff)>1 then Error("handle more than one alg, same shape");
	elif Length(ff)=1 then return ff[1];
	else return ff; fi;
	end
	);
	InstallMethod( GetAxialRep,
	[IsFusion,IsGroup],
	function( th, G )
	return GetAxialRep( Tag(th), G );
	end
	);
	InstallMethod( GetAxialRep,
	[IsFusion,IsString],
	function( th, G )
	return GetAxialRep( Tag(th), G );
	end
);

InstallMethod( WriteAxialRep,
	[IsAxialRep,IsBool],
	function( R, OW )
	local rr, p, ans;
	if Symmetries( R ) <> Trgp( R )
	then Print("WARNINGWARNIWAR... extra symmetries"); Error(); fi;

	rr := GetAxialRep( Fusion(R), StructureDescription(Trgp(R):short) );
	p := FirstPosition(rr,r->AreIsomorphicShapes(Trgp(r),Trgp(R)));
	if p = fail then Add(rr,R);
	else
		if OW then rr[p] := R;
		else
			ans := UserChoice("such a rep already exists, overwrite? 1 = yes, 2 = no",
				[1,2]);
			if ans = 1 then rr[p] := R;
			else return true; fi;
		fi;
	fi;
	PrintTo(
		Filename(DirectoryFusion(Fusion(R)),StructureDescription(Trgp(R):short)),
		Concatenation( "return [\n",
			JoinStringsWithSeparator(List(rr,PrintString),",\n\n"),"\n];")
	);
	end
	);
	InstallMethod( WriteAxialRep,
	[IsAxialRep],
	function(R)
	WriteAxialRep(R,false);
	end
);



#	WriteMajoranaAlgebra := function( arg )
#	# alg|list[alg](, bool) ->
#		local L, overwrite, a;
#		if IsList(arg[1]) and IsEmpty(arg[1]) then return; fi;
#		if not IsList( arg[1] ) then
#			arg[1] := [arg[1]];
#			CallFuncList(WriteMajoranaAlgebra,arg);
#			return; fi;
#		L := arg[1];
#		if not IsPermGroup(L[1].Group)
#			or ForAny(L, X-> IsomorphismGroups(X.Group,L[1].Group) = fail)
#		then Error("annoying"); fi;
#		if IsBound(arg[2]) then overwrite := arg[2];
#		else overwrite := false; fi;
#		if not overwrite then
#			for a in ReadMajoranaAlgebra(L[1].Group) do
#				if ForAll(L,X -> IsEmpty(AllShapeIsomClasses(a,X)))
#				then Add(L,a); fi; od; fi;
#		PrintTo(
#			Concatenation("./library/",StructureDescription(L[1].Group:short)),
#			Concatenation(
#				"return [",
#				Concatenation(List(L, l ->
#					Concatenation("\n",PrintStringMajoranaAlgebra(l),",\n") )),
#				"];" )
#		);
#	end;
#	UpdateMajoranaAlgebras := function( fn )
#		local gp;
#		for gp in ReadMajoranaAlgebra() do
#			WriteMajoranaAlgebra(List(ReadMajoranaAlgebra(gp),fn),true); od;
#		end;
#	DeleteMajoranaAlgebra := function( S )
#		local L, p;
#		L := ReadMajoranaAlgebra(S.Group);
#		p := FirstPosition(L,x->not IsEmpty(AllShapeIsomClasses(S,x)));
#		if p <> fail then
#			Remove(L,p);
#			WriteMajoranaAlgebra( L, true );
#			return true;
#		else return false; fi;
#	end;
#	DeleteMajoranaAlgebraAndUp := function( S )
#		local g,A;
#		Info(Mai,3,"deleting:");
#		for g in ReadMajoranaAlgebra() do
#			for A in ReadMajoranaAlgebra(g) do
#				if HasSubshape(A,S) then DeleteMajoranaAlgebra(A);
#				DisplayMajAlg(A); fi; od; od;
#	end;
#	ForAllMajoranaAlgebras := test ->
#		ForAll(ReadMajoranaAlgebra(), g -> ForAll(LoadMajoranaAlgebra(g),test));
#	ForAllMajoranaAlgebras := test ->
#		All(List(ReadMajoranaAlgebra(), g ->
#			All(List(LoadMajoranaAlgebra(g),function(m)
#				if test(m) then return true;
#				else Print("false: "); DisplayMajAlg(m); return false; fi; end)) ));
#	UnknownMajoranaAlgebras := function( arg )
#		local kn, as, ff, txt;
#		kn := ReadMajoranaAlgebra(arg[1]);
#		if kn = fail then kn := []; fi;
#		as := CallFuncList(AllShapes,arg);
#		ff := Filtered(as,S -> ForAll(kn,K ->IsEmpty(AllShapeIsomClasses(S,K))) );
#		txt := Concatenation(
#			String(Length(ff)), " unknown Majorana algebras",
#			" (& ",String(Length(kn))," known)",
#			" for ",StructureDescription(as[1].Group:short) );
#		if not IsEmpty(ff) then
#			txt := Concatenation(txt,
#				", viz:\n   ", ConcatBy(List(ff,f->ShapeStr(f.Shape)),"\n   ")); fi;
#		Info(Mai,2,txt);
#		return ff;
#		end;
#	RebootForm := function( R )
#		local l, i;
#		l := Length(R.SymbolicSS[1]);
#		R.FT := List([1..l],i->List([1..l],j->[]));
#		for i in Concatenation(List(R.Reps.Transpositions,t->
#			List(t^R.Group,R.WordPos))) do
#			R.FT[i][i] := 1; od;
#		CompleteForm(R);
#		return FindForm(R);
#		end;
#	miyamoto := function( A, a, i )
#		local B;
#		B := Basis(First(
#			Eigenspaces(Rationals,
#				List(Basis(A.V),b->Coefficients(Basis(A.V),A.mult(b,a))) ),
#			es->A.mult(Basis(es)[1],a)=MajEV[i]*Basis(es)[1]));
#		return List(Basis(A.V),b->2*SiftedVector(B,b)-b); end;
#	sigma := function( A, a ) return miyamoto(A,a,3); end;
#	tau := function( A, a ) return miyamoto(A,a,4); end;
#
####
## ouput
#	BriefShapeStr := function(shape)
#		local part;
#		part := SortedBy(PartitionBy(shape,IdFunc),x->x[1]);
#		return Concatenation("(",ConcatBy(List([1..Length(part)],i->
#			Concatenation(String(part[i][1]),"^{",String(Length(part[i][2])),"}")
#		),","),")");
#		end;
#	LatexGroupName := function(G)
#		local p,y;
#		y := ShallowCopy(StructureDescription(G:short));
#		for p in [
#			["A","A_"],
#			["C","C_"],
#			["D","D_"],
#			["Q","Q_"],
#			["S","S_"],
#			["_10","_{10}"],
#			["_12","_{12}"],
#			["_20","_{20}"],
#			["x","\\times "],
#			["_L","L"] ]
#		do y := ReplacedString(y,p[1],p[2]); od;
#		return Concatenation("$",y,"$"); end;
#	MinimalCount := function(G)
#		return Concatenation(
#			String(Count(LoadMajoranaAlgebra(G),IsMinmlTrgp)),
#			" / ", String(Length(AllShapes(G,true))), " min'l shapes" );
#	end;
#	GreatSuccessReport := function(gpSchema,algSchema)
#		local path, story, s, i;
#		path := "./success.txt";
#		story := List(ReadMajoranaAlgebra(),function(g)
#			local mm;
#			mm := LoadMajoranaAlgebra(g);
#			Info(Pro,1,"just doing ",StructureDescription(mm[1].Group:short));
#			return rec(
#				Group := mm[1].Group,
#				GroupDetails := RecordBySchema(gpSchema)(mm[1].Group),
#				Algebras := List(mm,RecordBySchema(algSchema)) );
#		end );
#		SortBy(story,x->Size(x.Group));
#
#		PrintTo(path,Concatenation(
#			"\\begin{longtable}{|c|",
#			ConcatBy(List(algSchema,f->"c"),"|"),
#			"|}\n",
#			"\t\\hline\n",
#			"\t\t$G$ & "));
#		AppendTo(path,ConcatBy(List(algSchema,s->s[1])," & "));
#		AppendTo(path,"\\\\\n");
#		for s in story do
#			AppendTo(path,"\t\\hline");
#			for i in [1..Maximum(Length(gpSchema),Length(s.Algebras))] do
#				if IsBound(gpSchema[i])
#				then AppendTo(path,"\t\t ",s.GroupDetails.(gpSchema[i][1])," & ");
#				else AppendTo(path,"\t\t & "); fi;
#				if IsBound(s.Algebras[i])
#				then AppendTo(path,ConcatBy(List(algSchema,x->s.Algebras[i].(x[1]))," & "));
#				else AppendTo(path,ConcatBy(List(algSchema,x->"")," & ")); fi;
#				AppendTo(path," \\\\\n");
#			od;
#		od;
#		AppendTo(path,Concatenation(
#			"\t\\hline\n",
#			"\t\\caption{}\n",
#			"\t\\label{tbl ?}\n",
#			"\\end{longtable}"));
#	end;
#	#GreatSuccessReport(PrintTrpoClasses,ReportShape,ReportAlgdim);
#
#	DisplayMajAlgSundry := function( A )
#		local txt;
#		txt := [];
#		if IsAll1Sp1dim(A)
#		then txt[1] := "1-diml 1-eigenspaces";
#		else txt[1] := "1-eigenspaces not 1-diml"; fi;
#		if IsTrivial(A.V) or RankMat(A.FT) > 0
#		then txt[2] := "nondegenerate form";
#		else txt[2] := "degenerate form"; fi;
#		if IsNortonInequality(A)
#		then txt[3] := "Norton inequality holds";
#		else txt[3] := "Norton inequality does not hold"; fi;
#		Print("   ",ConcatBy(txt,",  "),"\n");
#	end;
#
####
## quest
#	MajoranaAlgebras := function( list )
#		local M, i;
#		for i in [1..Length(list)] do
#			Info(Mai,3,Length(list)-i+1," Majorana algebras left to find");
#			M := MajoranaAlgebra(list[i]);
#			if not IsAll1Sp1dim(M) then Error("non-1-diml 1-eigenspaces"); fi;
#			if not IsRationals(M.Ring) then Error("form not completed"); fi;
#			WriteMajoranaAlgebra(M);
#		od;
#	end;
#	MajoranaAlgebraQuest := function( list )
#		local g;
#		for g in list do
#			MajoranaAlgebras(UnknownMajoranaAlgebras(SmallGroup(g),true)); od;
#	end;
