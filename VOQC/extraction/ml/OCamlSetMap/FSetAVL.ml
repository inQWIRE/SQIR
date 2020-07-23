module Make = 
  functor (X:Set.OrderedType) ->
  Set.Make(X)
