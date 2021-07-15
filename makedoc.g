#
# Ugaly: Universal Groups Acting LocallY
#
# This file is a script which compiles the package manual.
#
# To change working directory to the package director, use:
#
# gap> ChangeDirectoryCurrent(“path_to_package_folder/package_name”);
#
# Otherwise, run:
#
# gap> AutoDoc( rec( scaffold := true ) );
# 
# directly from the GAP command line and the effect will be the same
#  
# gap> Read("makedoc.g");  # when working directory is the package folder
#

if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;

AutoDoc( rec( scaffold := true, autodoc := true, extract_examples := true ) );
