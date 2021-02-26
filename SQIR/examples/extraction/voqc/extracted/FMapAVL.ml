module Map = struct
  include (Map : module type of Map with module Make := Map.Make)
  module Make = functor (X:Map.OrderedType) ->
    struct 
      include Map.Make(X)
      let find = find_opt (* Coq map find returns an option type *)
    end
  end

module Make = 
  functor (X:Map.OrderedType) ->
  Map.Make(X)
