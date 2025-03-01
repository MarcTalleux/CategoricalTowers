# SPDX-License-Identifier: GPL-2.0-or-later
# ToolsForCategoricalTowers: Tools for CategoricalTowers
#
# Implementations
#

##
InstallMethod( IsEqualForSyntacticCells,
        "for two syntactic categories",
        [ IsSyntacticCategory, IsSyntacticCategory ],

  IsIdenticalObj );

##
InstallMethod( IsEqualForSyntacticCells,
        "for two CAP objects",
        [ IsCapCategoryObject, IsCapCategoryObject ],

  function( obj1, obj2 )
    
    return IsIdenticalObj( obj1, obj2 ) or IsEqualForSyntacticCells( ObjectDatum( obj1 ), ObjectDatum( obj2 ) );
    
end );

##
InstallMethod( IsEqualForSyntacticCells,
        "for two CAP morphisms",
        [ IsCapCategoryMorphism, IsCapCategoryMorphism ],

  function( obj1, obj2 )
    
    return IsIdenticalObj( obj1, obj2 ) or IsEqualForSyntacticCells( MorphismDatum( obj1 ), MorphismDatum( obj2 ) );
    
end );

##
InstallMethod( IsEqualForSyntacticCells,
        "for two lists",
        [ IsList, IsList ],

  function( L1, L2 )
    local l;

    l := Length( L1 );
    
    return l = Length( L2 ) and
           ForAll( [ 1 .. l ], i -> IsEqualForSyntacticCells( L1[i], L2[i] ) );
    
end );

##
InstallMethod( IsEqualForSyntacticCells,
        "for two strings",
        [ IsStringRep, IsStringRep ],

  \= );

##
InstallMethod( IsEqualForSyntacticCells,
        "for two ring elements",
        [ IsRingElement, IsRingElement ],
        
  \= );

##
InstallGlobalFunction( AreEqualForSyntacticCells,
  function( a, b )
    local length;
    
    if IsList( a ) and not IsList( b ) then
        return false;
    elif not IsList( a ) and IsList( b ) then
        return false;
    elif IsList( a ) and IsList( b ) then
        length := Length( a );
        if not length = Length( b ) then
            return false;
        fi;
        return ForAll( [ 1 .. length ], i -> AreEqualForSyntacticCells( a[i], b[i] ) );
    elif not IsIdenticalObj( CapCategory( a ), CapCategory( b ) ) then
        return false;
    elif not ( ( IsCapCategoryObject( a ) and IsCapCategoryObject( b ) ) or ( IsCapCategoryMorphism( a ) and IsCapCategoryMorphism( b ) ) ) then
        return false;
    fi;
    
    return IsEqualForSyntacticCells( a, b );
    
end );

##
InstallMethod( SyntacticCategory,
        "for a record of options",
        [ IsRecord ],
        
  FunctionWithNamedArguments(
  [ [ "FinalizeCategory", true ],
    [ "quiver", fail, ],
    [ "category", fail, ],
    [ "optimize", 1 ],
  ],
  function( CAP_NAMED_ARGUMENTS, options )
    local list_of_operations_to_install, skip, operation_name, pos, category_constructor_options, syntactic_cat;
    
    list_of_operations_to_install := ShallowCopy( options.list_of_operations_to_install );
    
    skip := [ "IsEqualForObjects",
              "IsEqualForMorphisms",
              "IsCongruentForMorphisms",
              ];
    
    if CAP_NAMED_ARGUMENTS.optimize >= 1 then
        
        Append( skip,
                [ "PreCompose",
                  ] );
        
    fi;
    
    for operation_name in skip do
        pos := Position( list_of_operations_to_install, operation_name );
        if IsPosInt( pos ) then
            Remove( list_of_operations_to_install, pos );
        fi;
    od;
    
    options.list_of_operations_to_install := list_of_operations_to_install;
    
    category_constructor_options := ShallowCopy( options );
    category_constructor_options.category_filter := IsSyntacticCategory;
    category_constructor_options.category_object_filter := IsObjectInSyntacticCategory;
    category_constructor_options.category_morphism_filter := IsMorphismInSyntacticCategory;
    category_constructor_options.is_computable := true;
    category_constructor_options.supports_empty_limits := true;
    
    if "ObjectConstructor" in options.list_of_operations_to_install then
        
        category_constructor_options.object_constructor := function ( cat, object_datum )
            
            Assert( 0, IsList( object_datum ) and Length( object_datum ) = 2 and IsStringRep( object_datum[1] ) and IsList( object_datum[2] ) );
            
            return CreateCapCategoryObjectWithAttributes( cat,
                           PairOfOperationNameAndArguments, object_datum );
            
        end;
        
    fi;
    
    if "MorphismConstructor" in options.list_of_operations_to_install then
        
        category_constructor_options.morphism_constructor := function ( cat, source, morphism_datum, target )
            
            Assert( 0, IsList( morphism_datum ) and Length( morphism_datum ) = 2 and IsStringRep( morphism_datum[1] ) and IsList( morphism_datum[2] ) );
            
            return CreateCapCategoryMorphismWithAttributes( cat,
                           source,
                           target,
                           PairOfOperationNameAndArguments, morphism_datum );
            
        end;
        
    fi;
    
    if "ObjectDatum" in options.list_of_operations_to_install then
        
        category_constructor_options.object_datum := function ( cat, object )
            
            return PairOfOperationNameAndArguments( object );
            
        end;
        
    fi;
    
    if "MorphismDatum" in options.list_of_operations_to_install then
        
        category_constructor_options.morphism_datum := function ( cat, morphism )
            
            return PairOfOperationNameAndArguments( morphism );
            
        end;
        
    fi;
    
    category_constructor_options.create_func_bool :=
      function( name, cat )
        
        return Pair( """
          function ( input_arguments... )
            
            Error( "this is a syntactic category without actual implementation for boolean operations\n" );
            
          end
          """, 1 );
          
        end;
    
    category_constructor_options.create_func_object :=
      function( name, cat )
            
            return Pair( """
                function( input_arguments... )
                  local args, pair_of_op_name_and_args;
                  
                  args := [ input_arguments... ];
                  
                  pair_of_op_name_and_args := Pair( "operation_name", args );
                  
                  return top_object_getter( cat, pair_of_op_name_and_args );
                  
                end
            """, 1 );
            
        end;
    
    category_constructor_options.create_func_morphism :=
      function( name, cat )
            
            return Pair( """
                function( input_arguments... )
                  local args, pair_of_op_name_and_args;
                  
                  args := [ input_arguments... ];
                  
                  pair_of_op_name_and_args := Pair( "operation_name", args );
                  
                  return top_morphism_getter( cat, top_source, pair_of_op_name_and_args, top_range );
                  
                end
            """, 1 );
            
        end;
    
    category_constructor_options.top_object_getter_string := "ObjectConstructor";
    category_constructor_options.top_morphism_getter_string := "MorphismConstructor";
    
    syntactic_cat := CategoryConstructor( category_constructor_options );
    
    if not CAP_NAMED_ARGUMENTS.quiver = fail then
        SetUnderlyingQuiver( syntactic_cat, CAP_NAMED_ARGUMENTS.quiver );
    fi;
    
    if not CAP_NAMED_ARGUMENTS.category = fail then
        SetUnderlyingCategory( syntactic_cat, CAP_NAMED_ARGUMENTS.category );
    fi;
    
    AddIsEqualForObjects( syntactic_cat,
      function( syntactic_cat, obj1, obj2 )
        
        return AreEqualForSyntacticCells( obj1, obj2 );
        
    end );
    
    AddIsEqualForMorphisms( syntactic_cat,
      function( syntactic_cat, mor1, mor2 )
        
        return AreEqualForSyntacticCells( mor1, mor2 );
        
    end );
    
    AddIsCongruentForMorphisms( syntactic_cat,
      function( syntactic_cat, mor1, mor2 )
        local bool;
        
        bool := IsEqualForMorphisms( syntactic_cat, mor1, mor2 );
        
        if bool then
            return true;
        fi;
        
        Error( "this is a syntactic category without actual implementation for boolean operations\n" );
        
    end, OperationWeight( syntactic_cat, "IsEqualForMorphisms" ) );
    
    if CAP_NAMED_ARGUMENTS.optimize >= 1 then
        
        AddPreCompose( syntactic_cat,
          function( syntactic_cat, pre_mor, post_mor )
            local composition;
            
            if IsEqualToIdentityMorphism( syntactic_cat, pre_mor ) then
                
                return post_mor;
                
            fi;
            
            if IsEqualToIdentityMorphism( syntactic_cat, post_mor ) then
                
                return pre_mor;
                
            fi;
            
            if CanCompute( syntactic_cat, "IsEqualToZeroMorphism" ) then
                
                if IsEqualToZeroMorphism( syntactic_cat, pre_mor ) or IsEqualToZeroMorphism( syntactic_cat, post_mor ) then
                    
                    return ZeroMorphism( syntactic_cat, Source( pre_mor ), Target( post_mor ) );
                    
                fi;
                
            fi;
            
            return MorphismConstructor( syntactic_cat, Source( pre_mor ), Pair( "PreCompose", [ syntactic_cat, pre_mor, post_mor ] ), Target( post_mor ) );
            
        end );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( syntactic_cat );
        
    fi;
    
    for operation_name in options.list_of_operations_to_install do
        
        if not CanCompute( syntactic_cat, operation_name ) then
            
            Print( "WARNING: The synactic category cannot compute ", operation_name, ", probably because the operation is not supported by CategoryConstructor yet.\n" );
            
        fi;
        
    od;
    
    return syntactic_cat;
    
end ) );

##
InstallMethod( \/,
        "for a string and a syntactic category",
        [ IsStringRep, IsSyntacticCategory ],
        
  function( object_name, syntactic_cat )
    
    return Pair( "ObjectConstructor", [ object_name ] ) / syntactic_cat;
    
end );

##
InstallMethod( PositionsOfParentsOfASyntacticCell,
        [ IsList, IsCellInSyntacticCategory ],
        
  function( nodes, node )
    local parents;
    
    if PairOfOperationNameAndArguments( node )[1] in [ "ObjectConstructor", "MorphismConstructor" ] then
        return [ ];
    fi;
    
    parents := PairOfOperationNameAndArguments( node )[2];
    
    parents := Filtered( parents, parent -> IsCellInSyntacticCategory( parent ) or IsList( parent ) );
    
    return List( parents, parent -> PositionProperty( nodes, a -> AreEqualForSyntacticCells( parent, a ) ) );
    
end );

##
InstallMethod( PositionsOfParentsOfASyntacticCell,
        [ IsList, IsList ],
        
  function( nodes, node )
    
    return List( node, parent -> PositionProperty( nodes, a -> AreEqualForSyntacticCells( parent, a ) ) );
    
end );

##
InstallMethod( LinesOfLambdaAbstraction,
        "for a cell in a syntactic category and a list",
        [ IsCellInSyntacticCategory, IsList ],
        
  function( cell, list_of_arguments )
    local variable_name, var, cat, list_of_nodes, pos_in_list_of_nodes, positions_of_arguments, n, d, fixed_length_digit,
          arg_func, positions_of_morphisms, list_of_morphisms, list_of_sources, list_of_targets,
          pos_in_list_of_sources, pos_in_list_of_targets, obj_func, func, program, line;
    
    Assert( 0, Length( list_of_arguments ) > 0 and IsCapCategory( list_of_arguments[1] ) );
    
    variable_name := "deduped_";
    
    cat := list_of_arguments[1];
    
    list_of_arguments := list_of_arguments{[ 2 .. Length( list_of_arguments ) ]};
    
    list_of_nodes := ListOfEvaluationNodes( cell );
    
    pos_in_list_of_nodes := cell -> SafeUniquePositionProperty( list_of_nodes, node -> AreEqualForSyntacticCells( node, cell ) );
    
    positions_of_arguments := List( list_of_arguments, pos_in_list_of_nodes );
    
    Assert( 0, ForAll( positions_of_arguments, IsPosInt ) );
    
    n := Length( list_of_nodes );
    
    d := 1 + Int( Log10( Float( n ) ) );
    
    fixed_length_digit :=
      function( i )
        local l;
        
        l := 1 + Int( Log10( Float( i ) ) );
        
        return Concatenation( List( Concatenation( ListWithIdenticalEntries( d - l, 0 ), [ String( i ) ] ), String ) );
        
    end;
    
    arg_func :=
      function( argument )
        if IsCapCategory( argument ) then
            Assert( 0, IsIdenticalObj( argument, cat ) );
            return "cat";
        elif IsPosInt( argument ) then
            return argument;
        fi;
        return Concatenation( variable_name, fixed_length_digit( pos_in_list_of_nodes( argument ) ) );
    end;
    
    positions_of_morphisms := Filtered( [ 1 .. Length( list_of_arguments ) ], i -> IsMorphismInSyntacticCategory( list_of_arguments[i] ) );
    list_of_morphisms := list_of_arguments{positions_of_morphisms};
    list_of_sources := List( list_of_morphisms, Source );
    list_of_targets := List( list_of_morphisms, Target );
    
    pos_in_list_of_sources := cell -> PositionProperty( list_of_sources, node -> AreEqualForSyntacticCells( node, cell ) );
    pos_in_list_of_targets := cell -> PositionProperty( list_of_targets, node -> AreEqualForSyntacticCells( node, cell ) );
    
    obj_func :=
      function( primitive_node )
        local pos;
        
        pos := pos_in_list_of_sources( primitive_node );
        
        if IsPosInt( pos ) then
            return Concatenation( "Source( ", PairOfOperationNameAndArguments( list_of_morphisms[pos] )[2][1], " )" );
        fi;
        
        pos := pos_in_list_of_targets( primitive_node );
        
        Assert( 0, IsPosInt( pos ) );
        
        return Concatenation( "Target( ", PairOfOperationNameAndArguments( list_of_morphisms[pos] )[2][1], " )" );
        
    end;
    
    func :=
      function( i )
        local node, positions, line, datum;
        
        node := list_of_nodes[i];
        
        if IsList( node ) then
            positions := List( node, pos_in_list_of_nodes );
            line := JoinStringsWithSeparator( List( positions, p -> Concatenation( variable_name, fixed_length_digit( p ) ) ), ", " );
            line := Concatenation( "[ ", line, " ]" );
        else
            datum := PairOfOperationNameAndArguments( node );
            if i in positions_of_arguments then
                line := datum[2][1];
            elif datum[1] = "ObjectConstructor" then
                line := obj_func( node );
            else
                line := List( datum[2], arg_func );
                line := JoinStringsWithSeparator( line, ", " );
                line := Concatenation( datum[1], "( ", line, " )" );
            fi;
        fi;
        
        return Concatenation( "  ", variable_name, fixed_length_digit( i ), " := ", line, ";\n" );
        
    end;
    
    program := List( list_of_arguments, cell -> PairOfOperationNameAndArguments( cell )[2][1] );
    
    program := JoinStringsWithSeparator( program, ", " );
    
    program := [ Concatenation( "function ( cat, ", program, " )\n" ) ];
    
    line := List( [ 1 .. n ], i -> Concatenation( variable_name, fixed_length_digit( i ) ) );
    
    line := JoinStringsWithSeparator( line, ", " );
    
    line := [ Concatenation( "  local ", line, ";\n" ) ];
    
    program := Concatenation( program, line );
    
    program := Concatenation( program, List( [ 1 .. n ], func ) );
    
    program := Concatenation( program, [ Concatenation( "  return ", variable_name, fixed_length_digit( n ), ";\n" ) ] );
    
    program := Concatenation( program, [ "end\n" ] );
    
    return program;
    
end );

##
InstallMethod( LambdaAbstraction,
        "for a cell in a syntactic category and a list",
        [ IsCellInSyntacticCategory, IsList ],
        
  function( cell, list_of_arguments )
    local program;
    
    program := LinesOfLambdaAbstraction( cell, list_of_arguments );
    
    program := Concatenation( program );
    
    program := EvalString( program );
    
    return DisplayString( program );
    
end );

##################################
##
## View & Display
##
##################################

##
InstallMethod( String,
        "for an object in a syntactic category",
        [ IsObjectInSyntacticCategory ],
        
  function( a )
    local cat_name, datum;
    
    cat_name := Name( CapCategory( a ) );
    
    datum := ObjectDatum( a );
    
    if datum[1] = "ObjectConstructor" then
        
        return Concatenation( datum[1], "( ",
                       cat_name, ", Pair( \"ObjectConstructor\", [ \"", datum[2][1], "\" ] ) )" );
        
    elif IsEmpty( datum[2] ) then
        
        return Concatenation( datum[1], "( ", cat_name, " )" );
        
    fi;
    
    return Concatenation( datum[1], "( ", JoinStringsWithSeparator( List( datum[2], String ), ", " ), " )" );
    
end );

##
InstallMethod( String,
        "for an morphism in a syntactic category",
        [ IsMorphismInSyntacticCategory ],
        
  function( phi )
    local cat_name, datum;
    
    cat_name := Name( CapCategory( phi ) );
    
    datum := MorphismDatum( phi );
    
    if datum[1] = "MorphismConstructor" then
        
        return Concatenation( datum[1], "( ",
                       cat_name, ", ",
                       String( Source( phi ) ), ", Pair( \"MorphismConstructor\", [ \"",
                       datum[2][1], "\" ] ), ",
                       String( Target( phi ) ), " )" );
        
    fi;
    
    return Concatenation( datum[1], "( ",
                   cat_name, ", ",
                   JoinStringsWithSeparator( List( datum[2], String ), ", " ), " )" );
    
end );

##
InstallMethod( DisplayString,
        "for an object in a syntactic category",
        [ IsObjectInSyntacticCategory ],
        
  function( a )
    
    return Concatenation( String( a ), "\n" );
    
end );

##
InstallMethod( DisplayString,
        "for a morphism in a syntactic category",
        [ IsMorphismInSyntacticCategory ],
        
  function( phi )
    
    return Concatenation( String( phi ), "\n" );
    
end );
