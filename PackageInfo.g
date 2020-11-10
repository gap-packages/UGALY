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
Version := "1.0",
Date := "10/11/2020", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

Persons := [
  rec(
    FirstNames := "Khalil",
    LastName := "Hannouch",
    WWWHome := "https://www.newcastle.edu.au/profile/khalil-hannouch",
    Email := "khalil.hannouch@newcastle.edu.au",
    IsAuthor := true,
    IsMaintainer := false,
    #PostalAddress := TODO,
    #Place := TODO,
    Institution := "The University of Newcastle",
  ),
  rec(
    FirstNames := "Stephan",
    LastName := "Tornier",
    WWWHome := "https://www.newcastle.edu.au/profile/stephan-tornier",
    Email := "stephan.tornier@newcastle.edu.au",
    IsAuthor := true,
    IsMaintainer := true,
    #PostalAddress := TODO,
    #Place := TODO,
    Institution := "The University of Newcastle",
  ),
],

#SourceRepository := rec( Type := "TODO", URL := "URL" ),
#IssueTrackerURL := "TODO",
PackageWWWHome := "https://TODO/",
PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL     := Concatenation( ~.PackageWWWHome,
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
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "UGALY",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Universal Groups Acting LocallY. Methods to create, analyse and find local actions of universal groups acting on locally finite regular trees",
),

Dependencies := rec(
  GAP := ">= 4.10.2",
  NeededOtherPackages := [ ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

BannerString := Concatenation( 
"\nVersion ", ~.Version,
"\n __  __     ______     ______     __         __  __    ",
"\n/\\ \\/\\ \\   /\\  ___\\   /\\  __ \\   /\\ \\       /\\ \\_\\ \\   ",
"\n\\ \\ \\_\\ \\  \\ \\ \\__ \\  \\ \\  __ \\  \\ \\ \\____  \\ \\____ \\  by Khalil Hannouch",
"\n \\ \\_____\\  \\ \\_____\\  \\ \\_\\ \\_\\  \\ \\_____\\  \\/\\_____\\   and Stephan Tornier",
"\n  \\/_____/   \\/_____/   \\/_/\\/_/   \\/_____/   \\/_____/ ",
"\n                                                       ",
"\n Universal      Groups      Acting        LocallY    \n"),

TestFile := "tst/testall.g",

Keywords := [ "universal group", "local action", "regular tree", "groups acting on trees", "locally compact group", "totally disconnected" ],

));


