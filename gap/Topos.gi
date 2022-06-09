# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Implementations
#

InstallTrueMethod( IsFiniteCompleteCategory, IsElementaryTopos );
InstallTrueMethod( IsFiniteCocompleteCategory, IsElementaryTopos );
InstallTrueMethod( IsBicartesianClosedCategory, IsElementaryTopos );

##
InstallMethod( AddSubobjectClassifier,
               [ IsCapCategory, IsFunction, IsInt ],
               
  function( category, func, weight )
    local wrapped_func;
    
    if IsBound( category!.category_as_first_argument ) and category!.category_as_first_argument = true then
        
        TryNextMethod( );
        
    fi;
    
    wrapped_func := function( cat ) return func(); end;
    
    AddSubobjectClassifier( category, [ [ wrapped_func, [ ] ] ], weight );
    
end );
