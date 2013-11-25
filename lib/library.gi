
#
#	library implementation
#

InstallValue( LibHelper@,
	rec(
		sanitize := t -> ReplacedString(t,":",".")
	, dirfus := fus -> Directory(Filename(DirectoriesPackageLibrary("axials","data"),Tag(fus)))
	, filename := function( fus, name )
			local str;
			if IsGroup( name ) then str := StructureDescription(name:short);
			else str := name; fi;
			return Filename( LibHelper@.dirfus( fus ),
				LibHelper@.sanitize( str ) );
			end
	, writer := function( rr )
			PrintTo(
				LibHelper@.filename( Fusion(rr[1]), Trgp(rr[1]) ),
				Concatenation( "return [\n",
					JoinStringsWithSeparator(List(rr,PrintString),",\n\n"),"\n];")
			);
			return true;
			end
	)
);

InstallMethod( GetAxialRep,
	[IsFusion],
	function( th )
	return Filtered(
		DirectoryContents(LibHelper@.dirfus(th)),
		s -> s[1]<>'.');
	end 			## to do: how to create directories
	);
	InstallMethod( GetAxialRep,
	[IsFusion,IsObject],
	function( th, G )
	local file, res, ff;
	file := LibHelper@.filename( th, G );
	if IsReadableFile(file)
	then res := ReadAsFunction(file)();
	else res := []; fi;
	if IsGroup(G) then
		if HasShape(G) then
			ff :=  Filtered( res, R -> AreIsomorphicShapes(Trgp(R),G) );
			if Length(ff)>1 then Error("handle more than one alg, same shape");
			elif Length(ff)=1 then return ff[1];
			else return ff; fi;
		elif HasTranspositions(G) then
			return Filtered( res, R ->   AreIsomorphicTrgp(Trgp(R),G) );
		fi;
	fi;
	return res;
	end
);

InstallMethod( WriteAxialRep,
	[IsAxialRep],
	function(R)
	local rr, p, ans;
	if ValueOption("dontwrite") = true then return; fi;
	if Symmetries( R ) <> Trgp( R )
	then Error("WARNINGWARNIWAR... extra symmetries"); fi;

	rr := GetAxialRep( Fusion(R), StructureDescription(Trgp(R):short) );
	p := FirstPosition(rr,r->AreIsomorphicShapes(Trgp(r),Trgp(R)));
	if p = fail then Add(rr,R);
	else
		if ValueOption("overwrite") = true
		or ( Characteristic(Alg(R)) = 0 and Characteristic(Alg(rr[p])) > 0
			and Dimension(Alg(R)) = Dimension(Alg(rr[p])) )
		then rr[p] := R;
		elif ValueOption("overwrite") = fail then
			ans := UserChoice("such a rep already exists, overwrite? 1 = yes, 2 = no",
				[1,2]);
			if ans = 1 then rr[p] := R;
			else return true; fi;
		elif ValueOption("overwrite") <> false then
			Error("you gave me garbled parameters. ~_~");
		fi;
	fi;
	return LibHelper@.writer( rr );
	end
);

InstallMethod( DeleteAxialRep,
	[IsFusion,IsTrgp and HasShape],
	function( fus, S )
		local RR, p;
		RR := GetAxialRep( fus, StructureDescription(S:short) );
		p := FirstPosition(RR,R -> AreIsomorphicShapes(Trgp(R),S));
		if p = fail then return false; fi;
		return LibHelper@.writer(RR{FilteredNot([1..Length(RR)],q->q=p)});
	end
	);
	InstallMethod( DeleteAxialRep,
	[IsAxialRep],
	function( R )
	return DeleteAxialRep( Fusion( R ), Trgp( R ) );
	end
);

