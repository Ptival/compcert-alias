Require Import Registers.

Require Export AliasPTMap.

Module RegMap <: PTMap.

  Definition k := reg.

  Axiom t : Type.

  Axiom top : t.

  Axiom bot : t.

  Axiom get : k -> t -> PTSet.t.

  Axiom add : k -> PTSet.t -> t -> t.

End RegMap.