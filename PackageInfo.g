SetPackageInfo( rec(
	PackageName := "m-calculator",
		Version := "1.0",
	PackageDoc := rec(
			BookName := "m-calculator",
			SixFile	:= "doc/manual.six",
			Autoload := true ),
	PackageWWWHome :=
		Concatenation( "http://www.internet.com/",~.PackageName,"/" ),
	Persons := [
		rec( 
			LastName      := "Rehren",
			FirstNames    := "Felix",
			IsAuthor      := true,
			IsMaintainer  := true,
			Email         := "rehrenf@maths.bham.ac.uk",
			WWWHome       := "http://web.mat.bham.ac.uk/~rehrenf/",
			Institution   := "Birmingham")
	],
	BannerString := "M-algebras package, by Felix Rehren\n",
	Dependencies := rec(
			GAP := "4.5",
			NeededOtherPackages := [ ["GAPDoc", "1.3"],
				["trgps", "1.0"] ],
			SuggestedOtherPackages := [ ] ),
	Status := "dev",
	AvailabilityTest := ReturnTrue,
	TestFile := "tst/all.gt",
) );
