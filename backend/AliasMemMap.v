Require Import AliasAbstract.
Require Export AliasPTMap.

Module MemMap <: PTMap.

  Definition k := aloc.

  Axiom t : Type.

  Axiom top : t.

  Axiom get : aloc -> t -> PTSet.t.

  Axiom add : aloc -> PTSet.t -> t -> t.

End MemMap.