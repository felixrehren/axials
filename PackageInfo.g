SetPackageInfo( rec(
	PackageName := "axials",
		Version := "1.0",
	PackageDoc := rec(
			BookName := "axials",
			SixFile	:= "doc/manual.six",
			Autoload := true ),
	PackageWWWHome :=
		Concatenation( "https://github.com/felixrehren/",~.PackageName ),
	Persons := [
		rec( 
			FirstNames    := "Felix",
			LastName      := "Rehren",
			IsAuthor      := true,
			IsMaintainer  := true,
			Email         := "rehrenf@maths.bham.ac.uk",
			WWWHome       := "http://web.mat.bham.ac.uk/~rehrenf/",
			Institution   := "Birmingham")
	],
	BannerString := "Axial algebras and representations package, by Felix Rehren\n",
	Dependencies := rec(
			GAP := "4.5",
			NeededOtherPackages := [ ["GAPDoc", "1.3"],
				["trgps", "1.0"] ],
			SuggestedOtherPackages := [ ] ),
	Status := "dev",
	AvailabilityTest := ReturnTrue,
	TestFile := "tst/all.gt",
) );
