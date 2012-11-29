Require Import AST.
Require Import Integers.
Require Import List.
Require Import Maps.
Require Import Op.
Require Import RTL.

Require Import AliasAbstract.
Require Import AliasMemMap.
Require Import AliasRegMap.

Definition result := (RegMap.t * MemMap.t)%type.

Definition image_of_ptset (s: PTSet.t) (m: MemMap.t): PTSet.t :=
  PTSet.fold (fun p saccu => PTSet.join (MemMap.get p m) saccu) s PTSet.bot.

Definition add_ptset_to_image (sadd: PTSet.t) (smod: PTSet.t) (m: MemMap.t) : MemMap.t :=
  PTSet.fold (fun k maccu => MemMap.add k sadd maccu) smod m.

Definition shift_offset (s: PTSet.t) (o: Int.int): PTSet.t :=
  let f x saccu :=
    match x with
    | Blk _    => PTSet.add x saccu
    | Loc b o' => PTSet.add (Loc b (Int.add o o')) saccu
    end
  in
  PTSet.fold f s PTSet.bot.

Definition unknown_offset (s: PTSet.t): PTSet.t :=
  let f x saccu :=
    match x with
    | Blk _   => PTSet.add x saccu
    | Loc b o => PTSet.add (Blk b) saccu
    end
  in
  PTSet.fold f s PTSet.bot.

Definition addr_image addr args rmap :=
  match addr, args with
  | Aindexed o, r::nil             =>
    Some (shift_offset (RegMap.get r rmap) o)
  | Aindexed2 _, r1::r2::nil       =>
    Some (
      PTSet.join
        (unknown_offset (RegMap.get r1 rmap))
        (unknown_offset (RegMap.get r2 rmap))
    )
  | Ascaled _ _, _::nil            => Some PTSet.bot
  | Aindexed2scaled _ _, r::_::nil =>
    Some (unknown_offset (RegMap.get r rmap))
  | Aglobal i o, nil               =>
    Some (PTSet.singleton (Loc (Global i) o))
  | Abased i _, _::nil
  | Abasedscaled _ i _, _::nil     =>
    Some (PTSet.singleton (Blk (Global i)))
  | Ainstack o, nil                =>
    Some (PTSet.singleton (Loc Stack o))
  | _, _                           => None
  end.

Definition transf_op op args dst rmap :=
  match op with
    | Oindirectsymbol i =>
      RegMap.add dst (PTSet.singleton (Loc (Global i) Int.zero)) rmap
    | Olea addr =>
      match addr_image addr args rmap with
        | None   => rmap (*!*)
        | Some s => RegMap.add dst s rmap
      end
    | Omove =>
      match args with
        | r::nil => RegMap.add dst (RegMap.get r rmap) rmap
        | _      => rmap (*!*)
      end
    | Osub =>
      match args with
        | r::_::nil => RegMap.add dst (unknown_offset (RegMap.get r rmap)) rmap
        | _         => rmap (*!*)
      end
    | _ => rmap
  end.

Definition transf_builtin ef args dst n (res : result) :=
  let (rmap, mmap) := res in
  match ef with
  | EF_external _ _ =>
    (RegMap.add dst (PTSet.singleton (Blk Globals)) rmap, mmap)
  | EF_builtin _ _  =>
    (RegMap.add dst (PTSet.singleton (Blk Globals)) rmap, mmap)
    (*TODO: to do better things on vload/vstore global, we would first need
       to have strong updates, since Globals start at top anyway. *)
  | EF_vload _ | EF_vload_global _ _ _ => (RegMap.add dst PTSet.top rmap, mmap)
  | EF_vstore _ =>
    match args with
    | r1 :: r2 :: nil =>
      (rmap, add_ptset_to_image (RegMap.get r2 rmap) (RegMap.get r1 rmap) mmap)
    | _               => res
    end
  | EF_vstore_global _ i o =>
    match args with
    | r :: nil =>
      (rmap, MemMap.add (Loc (Global i) o) (RegMap.get r rmap) mmap)
    | _               => res
    end
  | EF_malloc        =>
    (RegMap.add dst
      (PTSet.singleton (Loc (Alloc n) Int.zero)) rmap,
      mmap)
  | EF_free          => res
  | EF_memcpy _ _    =>
    match args with
    | rdst :: rsrc :: nil =>
      (rmap,
        add_ptset_to_image PTSet.top
        (unknown_offset (RegMap.get rdst rmap)) mmap
      )
    | _                   => res (*!*)
    end
  | EF_annot _ _     => res
  | EF_annot_val _ _ =>
    match args with
    | r1 :: nil => (RegMap.add dst (RegMap.get r1 rmap) rmap, mmap)
    | _       => res (*!*)
    end
  end.

Definition transf c n (res : result) :=
  let (rmap, mmap) := res in
  match c!n with
  | Some instr =>
    match instr with
    | Inop _                         => res
    | Iop op args dst succ           => (transf_op op args dst rmap, mmap)
    | Iload chunk addr args dst succ =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None   => res (*!*)
        | Some s => (RegMap.add dst (image_of_ptset s mmap) rmap, mmap)
        end
      | _ => (RegMap.add dst PTSet.bot rmap, mmap)
      end
    | Istore chunk addr args src succ =>
      match chunk with
      | Mint32 =>
        match addr_image addr args rmap with
        | None      => res (*!*)
        | Some sdst =>
          (rmap, add_ptset_to_image (RegMap.get src rmap) sdst mmap)
        end
      | _ => res
      end
    | Icall sign fn args dst succ => (RegMap.add dst PTSet.top rmap, MemMap.top)
    | Itailcall sign fn args      => (rmap, MemMap.top)
    | Ibuiltin ef args dst succ   => transf_builtin ef args dst n res
    | Icond cond args ifso ifnot  => res
    | Ijumptable arg tbl          => res
    | Ireturn _                   => res
    end
  | None       => res
  end.
