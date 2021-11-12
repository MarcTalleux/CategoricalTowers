# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Reading the declaration part of the package.
#

if IsBound( WriteFileForMonoidalStructure ) then
ReadPackage( "Toposes", "gap/Tools.gd");
fi;

## Cartesian
ReadPackage( "Toposes", "gap/CartesianCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/CartesianCategories.gd" );

ReadPackage( "Toposes", "gap/DistributiveCartesianCategories.gd" );

ReadPackage( "Toposes", "gap/BraidedCartesianCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/BraidedCartesianCategories.gd" );

ReadPackage( "Toposes", "gap/SymmetricCartesianCategoriesDoc.gd" );

## Cartesian Closed
ReadPackage( "Toposes", "gap/CartesianClosedCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/CartesianClosedCategories.gd" );

ReadPackage( "Toposes", "gap/SymmetricCartesianClosedCategoriesDoc.gd" );

## Cocartesian
ReadPackage( "Toposes", "gap/CocartesianCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/CocartesianCategories.gd" );

ReadPackage( "Toposes", "gap/DistributiveCocartesianCategories.gd" );

ReadPackage( "Toposes", "gap/BraidedCocartesianCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/BraidedCocartesianCategories.gd" );

ReadPackage( "Toposes", "gap/SymmetricCocartesianCategoriesDoc.gd" );

## Cocartesian Coclosed
ReadPackage( "Toposes", "gap/CocartesianCoclosedCategoriesDoc.gd" );
ReadPackage( "Toposes", "gap/CocartesianCoclosedCategories.gd" );

ReadPackage( "Toposes", "gap/SymmetricCocartesianCoclosedCategoriesDoc.gd" );

## Topos
ReadPackage( "Toposes", "gap/Topos.gd");
ReadPackage( "Toposes", "gap/Topos.autogen.gd");
