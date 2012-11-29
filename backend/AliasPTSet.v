Require Import AliasAbstract.

Module Type PTSetT.

  Parameter t : Set.

  Parameter bot : t.

  Parameter top : t.

  Parameter add : aloc -> t -> t.

  Parameter singleton : aloc -> t.

  Parameter fold : forall {x}, (aloc -> x -> x) -> t -> x -> x.

  Parameter join : t -> t -> t.

End PTSetT.

Module PTSet <: PTSetT.

  Axiom t : Set.

  Axiom bot : t.

  Axiom top : t.

  Axiom add : aloc -> t -> t.

  Definition singleton x := add x bot.

  Axiom fold : forall {x}, (aloc -> x -> x) -> t -> x -> x.

  Axiom join : t -> t -> t.

End PTSet.
