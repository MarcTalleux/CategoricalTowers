#
# Toposes: Elementary toposes
#
# Reading the implementation part of the package.
#

if IsBound( WriteFileForMonoidalStructure ) then
ReadPackage( "Toposes", "gap/Tools.gi");
fi;

## Cartesian
ReadPackage( "Toposes", "gap/CartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/CartesianCategories.gi" );

ReadPackage( "Toposes", "gap/DistributiveCartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/DistributiveCartesianCategories.gi" );

ReadPackage( "Toposes", "gap/BraidedCartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/BraidedCartesianCategories.gi" );

ReadPackage( "Toposes", "gap/CartesianClosedCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/CartesianClosedCategories.gi" );

## Cocartesian
ReadPackage( "Toposes", "gap/CocartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/CocartesianCategories.gi" );

ReadPackage( "Toposes", "gap/DistributiveCocartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/DistributiveCocartesianCategories.gi" );

ReadPackage( "Toposes", "gap/BraidedCocartesianCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/BraidedCocartesianCategories.gi" );

ReadPackage( "Toposes", "gap/CocartesianCoclosedCategoriesMethodRecord.gi" );
ReadPackage( "Toposes", "gap/CocartesianCoclosedCategories.gi" );

## Derived methods
ReadPackage( "Toposes", "gap/CartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/DistributiveCartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/BraidedCartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/SymmetricCartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/CartesianClosedCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/SymmetricCartesianClosedCategoriesDerivedMethods.gi" );

ReadPackage( "Toposes", "gap/CocartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/DistributiveCocartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/BraidedCocartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/SymmetricCocartesianCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/CocartesianCoclosedCategoriesDerivedMethods.gi" );
ReadPackage( "Toposes", "gap/SymmetricCocartesianCoclosedCategoriesDerivedMethods.gi" );

## Topos
ReadPackage( "Toposes", "gap/MethodRecord.gi");
ReadPackage( "Toposes", "gap/Topos.gi");

ReadPackage( "Toposes", "gap/DerivedMethods.gi" );
