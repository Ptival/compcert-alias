Require Export AliasPTSet.

Module Type PTMap.

  Parameter k : Type.

  Parameter t : Type.

  Parameter top : t.

  Parameter bot : t.

  Parameter get : k -> t -> PTSet.t.

  Parameter add : k -> PTSet.t -> t -> t.

End PTMap.