# SPDX-License-Identifier: GPL-2.0-or-later
# ZariskiFrames: (Co)frames/Locales of Zariski closed/open subsets of affine, projective, or toric varieties
#
# Declarations
#

#! @Chapter Affine algebras

####################################
##
#! @Section GAP Categories
##
####################################

## categories

#!
DeclareCategory( "IsCategoryOfAffineAlgebras", IsCapCategory );

#!
DeclareCategory( "IsObjectInCategoryOfAffineAlgebras", IsCapCategoryObject );

#!
DeclareCategory( "IsMorphismInCategoryOfAffineAlgebras", IsCapCategoryMorphism );

####################################
##
#! @Section Attributes
##
####################################

#!
DeclareAttribute( "CoefficientsRing", IsCategoryOfAffineAlgebras );

CapJitAddTypeSignature( "CoefficientsRing", [ IsCategoryOfAffineAlgebras ],
  function ( input_types )
    
    return CapJitDataTypeOfRing( CoefficientsRing( input_types[1].category ) );
    
end );

#!
DeclareAttribute( "DefiningSextupleOfAffineAlgebra",
        IsObjectInCategoryOfAffineAlgebras );

#!
DeclareAttribute( "AmbientAlgebra",
        IsObjectInCategoryOfAffineAlgebras );

#!
DeclareAttribute( "MatrixOfImages",
        IsMorphismInCategoryOfAffineAlgebras );

DeclareAttribute( "AssociatedHomalgRing",
        IsObjectInCategoryOfAffineAlgebras );

DeclareAttribute( "AssociatedHomalgRingMap",
        IsMorphismInCategoryOfAffineAlgebras );

DeclareOperation( "AssociatedHomalgRingOfCoproduct",
        [ IsObjectInCategoryOfAffineAlgebras, IsObjectInCategoryOfAffineAlgebras ] );

DeclareAttribute( "CoordinateAlgebraOfGraph",
        IsMorphismInCategoryOfAffineAlgebras );

#!
DeclareAttribute( "Dimension",
        IsObjectInCategoryOfAffineAlgebras );

####################################
##
# @Section Operations
##
####################################

DeclareOperation( "IsomorphismsToStandardizedAlgebra",
        [ IsCategoryOfAffineAlgebras, IsObjectInCategoryOfAffineAlgebras, IsInt ] );

DeclareOperation( "IsomorphismsToStandardizedAlgebraMorphism",
        [ IsCategoryOfAffineAlgebras, IsMorphismInCategoryOfAffineAlgebras ] );

####################################
##
#! @Section Constructors
##
####################################

#!
DeclareAttribute( "CategoryOfAffineAlgebras", IsHomalgRing );
#! @InsertChunk CategoryOfAffineAlgebras

CapJitAddTypeSignature( "CategoryOfAffineAlgebras", [ IsHomalgRing ], function ( input_types )
    
    return CapJitDataTypeOfCategory( CategoryOfAffineAlgebras( input_types[1].category ) );
    
end );

####################################
##
## Tools
##
####################################

DeclareOperation( "CreateAmbientPolynomialAlgebraOfAffineAlgebra",
        [ IsHomalgRing, IsList ] );
