#
# UGALY: Universal Groups Acting LocallY
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#

SetPackageInfo( rec(

PackageName := "UGALY",
Subtitle := "Universal Groups Acting LocallY",
Version := "4.1.3",
Date := "07/07/2023", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

Persons := [ rec(
		FirstNames := "Khalil",
		LastName := "Hannouch",
		WWWHome := "https://www.newcastle.edu.au/profile/khalil-hannouch",
		Email := "khalil.hannouch@newcastle.edu.au",
		IsAuthor := true,
		IsMaintainer := false,
		PostalAddress := Concatenation( [
			"Khalil Hannouch\n",
			"The University of Newcastle\n",
			"School of Information and Physical Sciences\n",
			"University Drive\n",
			"2308 Callaghan NSW\n",
			"Australia" ] ),
		Place := "Newcastle",
		Institution := "The University of Newcastle",
	),
	rec(
		FirstNames := "Stephan",
		LastName := "Tornier",
		WWWHome := "https://www.newcastle.edu.au/profile/stephan-tornier",
		Email := "stephan.tornier@newcastle.edu.au",
		IsAuthor := true,
		IsMaintainer := true,
		PostalAddress := Concatenation( [
			"Stephan Tornier\n",
			"The University of Newcastle\n",
			"School of Information and Physical Sciences\n",			
			"University Drive\n",
			"2308 Callaghan NSW\n",
			"Australia" ] ),
		Place := "Newcastle",
		Institution := "The University of Newcastle",
	),	
	# Contributors:
	rec(
		FirstNames := "Tasman",
		LastName := "Fell",
		IsAuthor := false,
		IsMaintainer := false,
	)
],

SourceRepository := rec(
	Type := "git",
	URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "accepted",
CommunicatedBy := "Laurent Bartholdi (Göttingen)",
AcceptDate := "07/2021", # 21/07/2021
AbstractHTML   :=  "<span class=\"pkgname\">UGALY</span> (Universal Groups Acting LocallY) is a <span class=\"pkgname\">GAP</span> package that provides methods to create, analyse and find local actions of generalised universal groups acting on locally finite regular trees, following Burger-Mozes and Tornier.",

PackageDoc := rec(
	BookName  := "UGALY",
	ArchiveURLSubset := ["doc"],
	HTMLStart := "doc/chap0_mj.html",
	PDFFile   := "doc/manual.pdf",
	SixFile   := "doc/manual.six",
	LongTitle := "Universal Groups Acting LocallY. Methods to create, analyse and find local actions of universal groups acting on locally finite regular trees",
),

Dependencies := rec(
	GAP := ">= 4.10.2",
	NeededOtherPackages := [ ["fga", ">= 1.0"] ],
	SuggestedOtherPackages := [ ],
	ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

BannerString := Concatenation( 
	"\nVersion ", ~.Version,
	"\n __  __     ______     ______     __         __  __",
	"\n/\\ \\/\\ \\   /\\  ___\\   /\\  __ \\   /\\ \\       /\\ \\_\\ \\    by Khalil Hannouch",
	"\n\\ \\ \\_\\ \\  \\ \\ \\__ \\  \\ \\  __ \\  \\ \\ \\____  \\ \\____ \\    and Stephan Tornier",
	"\n \\ \\_____\\  \\ \\_____\\  \\ \\_\\ \\_\\  \\ \\_____\\  \\/\\_____\\  with contributions by",
	"\n  \\/_____/   \\/_____/   \\/_/\\/_/   \\/_____/   \\/_____/   Tasman Fell",
	"\n                                                       ",
	"\n Universal      Groups      Acting        LocallY    \n"
),

TestFile := "tst/testall.g",

Keywords := [ "universal group", "local action", "regular tree", "groups acting on trees", "locally compact group", "totally disconnected" ],

));
