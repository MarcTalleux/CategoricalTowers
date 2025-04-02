#! @Chunk LeftCartesianDistributivityFactoring_PathCategory

#! @Example
LoadPackage( "FiniteCocompletions", false );
#! true
q := FinQuiver( "Q(a,b,c)[]" );
#! FinQuiver( "Q(a,b,c)[]" )
C := PathCategory( q );
#! PathCategory( FinQuiver( "Q(a,b,c)[]" ) )
DC := FreeDistributiveCategoryWithStrictProductAndCoproducts( C );
#! FreeDistributiveCategoryWithStrictProductAndCoproducts(
#! PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )
a := DC.a;
#! <An object in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>
b := DC.b;
#! <An object in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>
c := DC.c;
#! <An object in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>

axb_u_axc := Coproduct( DirectProduct( a, b ), DirectProduct( a, c ) );
#! <An object in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>

a_x_buc := DirectProduct( a, Coproduct( b, c ) );
#! <An object in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>

hom_axb_u_axc_a_x_buc := MorphismsOfExternalHom( axb_u_axc, a_x_buc );;

Length( hom_axb_u_axc_a_x_buc ) = 1;
#! true

lfactor := hom_axb_u_axc_a_x_buc[1];
#! <A morphism in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>

IsOne( lfactor );
#! true

hom_a_x_buc_axb_u_axc := MorphismsOfExternalHom( a_x_buc, axb_u_axc );;

Length( hom_a_x_buc_axb_u_axc ) = 1;
#! true

lexpand := hom_a_x_buc_axb_u_axc[1];
#! <A morphism in FreeDistributiveCategoryWithStrictProductAndCoproducts(
#!  PathCategory( FinQuiver( "Q(a,b,c)[]" ) ) )>

IsOne( lexpand );
#! true

Inverse( lfactor ) = lexpand;
#! true

S := SyntacticCategoryInDoctrines( "IsDistributiveCategory" : name := "S", category := C );
#! S

F := EmbeddingOfUnderlyingCategory( S );
DF := ExtendFunctorToFreeDistributiveCategoryWithStrictProductAndCoproducts( F );

slfactor := DF( lfactor );

arguments := [ S, S.a, S.b, S.c ];

program := LambdaAbstraction( slfactor, arguments );

Assert( 0, slfactor = CallFuncList( EvalString( program ), arguments ) );

#! @EndExample
