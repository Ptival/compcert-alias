open AliasAnalysis
open AST
open BinInt
open BinPos
open Datatypes
open Maps
open Op
open RTL

let rec int_of_pos p =
  match p with
  | Coq_xH   -> 1
  | Coq_xO q -> 2 * int_of_pos q
  | Coq_xI q -> 2 * int_of_pos q + 1

let string_of_pos p = string_of_int (int_of_pos p)

let string_of_coq_Z z =
  match z with
  | Z0 -> "0"
  | Zpos p -> string_of_pos p
  | Zneg p -> "-" ^ string_of_pos p

let string_of_node = string_of_pos
let string_of_ident = string_of_pos
let string_of_offset = string_of_coq_Z
let string_of_reg = string_of_pos

let string_of_absb' b =
  match b with
  | Allocs(Some n)  -> "Alloc" ^ string_of_node n
  | Allocs(None)    -> "Allocs"
  | Globals(Some i) -> "Global" ^ string_of_ident i
  | Globals(None)   -> "Globals"
  | Other           -> "Other"
  | Stack           -> "Stack"

let string_of_absb b =
  match b with
  | None     -> "All"
  | Some(b') -> string_of_absb' b'

let string_of_absp p =
  match p with
  | Blk(b)    -> "Blk(" ^ string_of_absb b ^ ")"
  | Loc(b, o) -> "Loc(" ^ string_of_absb b ^ ", " ^ string_of_coq_Z o ^ ")"

let string_of_reg r = "R" ^ string_of_reg r

let string_of_set set_fold string_of_elt s =
  let folder elt accu =
    match accu with
    | "" -> string_of_elt elt
    | _  -> accu ^ ", " ^ string_of_elt elt
  in "{" ^ set_fold folder s "" ^ "}"

let string_of_ptset s =
  if PTSet.beq s PTSet.top
  then "⊤"
  else if PTSet.beq s PTSet.bot
  then "⊥"
  else string_of_set PTSet.AbsPSet.fold string_of_absp s

let string_of_rmap (rmap: RegMap.t) =
  match rmap with
  | None -> "⊤"
  | Some rmap' ->
      "{"
      ^ RegMapWithoutTop.M.fold
        (fun k v accu ->
          if PTSet.beq v PTSet.bot
          then accu
          else
            (if accu = "" then "" else accu ^ ", ")
            ^ string_of_reg k ^ " -> " ^ string_of_ptset v
        )
        rmap'
        ""
      ^ "}"

let string_of_mmap (mmap: MemMap.t) =
  match mmap with
  | None -> "⊤"
  | Some mmap' ->
      "{"
      ^ MemMap.Raw.MSL.M.fold
        (fun k v accu ->
          (if accu = "" then "" else accu ^ ", ")
          ^ string_of_absp k ^ " -> " ^ string_of_ptset v
        )
        mmap'
        ""
      ^ "}"

let string_of_list string_of_elt l =
  let rec string_of_list_aux l =
    match l with
    | []      -> ""
    | h::rest -> ", " ^ string_of_elt h ^ string_of_list_aux rest
  in match l with
  | []      -> "[]"
  | h::rest -> "[" ^ string_of_elt h ^ string_of_list_aux rest ^ "]"

let string_of_reglist = string_of_list string_of_reg

let string_of_sum string_of_left string_of_right s =
  match s with
  | Coq_inl l -> string_of_left l
  | Coq_inr r -> string_of_right r

let string_of_reg_ident_sum = string_of_sum string_of_reg string_of_ident

let string_of_option string_of_elt o =
  match o with
  | None   -> "None"
  | Some e -> "Some " ^ string_of_elt e

let string_of_reg_option = string_of_option string_of_reg

let string_of_addr a =
  match a with
  | Aindexed o             -> "Aindexed " ^ string_of_coq_Z o
  | Aindexed2 o            -> "Aindexed2 " ^ string_of_coq_Z o
  | Ascaled (s, o)         ->
      "Ascaled (" ^ string_of_coq_Z s ^ ", " ^ string_of_coq_Z o ^ ")"
  | Aindexed2scaled (s, o) ->
      "Aindexed2scaled (" ^ string_of_coq_Z s ^ ", " ^ string_of_coq_Z o ^
      ")"
  | Aglobal (i, o)         ->
      "Aglobal (" ^ string_of_ident i ^ ", " ^ string_of_coq_Z o ^ ")"
  | Abased (i, o)          ->
      "Abased (" ^ string_of_ident i ^ ", " ^ string_of_coq_Z o ^ ")"
  | Abasedscaled (o, i, s) ->
      "Abasedscaled (" ^ string_of_coq_Z o ^ ", " ^ string_of_ident i ^
      ", " ^ string_of_coq_Z s ^ ")"
  | Ainstack o             -> "Ainstack " ^ string_of_coq_Z o

let string_of_op o =
  match o with
  | Omove           -> "Omove"
  | Ointconst i     -> "Ointconst " ^ string_of_coq_Z i
  | Ofloatconst f   -> "Ofloatconst "
  | Ocast8signed    -> "Ocast8signed"
  | Ocast8unsigned  -> "Ocast8unsigned"
  | Ocast16signed   -> "Ocast16signed"
  | Ocast16unsigned -> "Ocast16unsigned"
  | Oneg            -> "Oneg"
  | Osub            -> "Osub"
  | Omul            -> "Omul"
  | Omulimm i       -> "Omulimm " ^ string_of_coq_Z i
  | Odiv            -> "Odiv"
  | Odivu           -> "Odivu"
  | Omod            -> "Omod"
  | Omodu           -> "Omodu"
  | Oand            -> "Oand"
  | Oandimm i       -> "Oandimm " ^ string_of_coq_Z i
  | Oor             -> "Oor"
  | Oorimm i        -> "Oorimm " ^ string_of_coq_Z i
  | Oxor            -> "Oxor"
  | Oxorimm i       -> "Oxorimm " ^ string_of_coq_Z i
  | Oshl            -> "Oshl"
  | Oshlimm i       -> "Oshlimm " ^ string_of_coq_Z i
  | Oshr            -> "Oshr"
  | Oshrimm i       -> "Oshrimm " ^ string_of_coq_Z i
  | Oshrximm i      -> "Oshrximm " ^ string_of_coq_Z i
  | Oshru           -> "Oshru"
  | Oshruimm i      -> "Oshruimm " ^ string_of_coq_Z i
  | Ororimm i       -> "Ororimm " ^ string_of_coq_Z i
  | Olea a          -> "Olea " ^ string_of_addr a
  | Onegf           -> "Onegf"
  | Oabsf           -> "Oabsf"
  | Oaddf           -> "Oaddf"
  | Osubf           -> "Osubf"
  | Omulf           -> "Omulf"
  | Odivf           -> "Odivf"
  | Osingleoffloat  -> "Osingleoffloat"
  | Ointoffloat     -> "Ointoffloat"
  | Ofloatofint     -> "Ofloatofint"
  | Ocmp c          -> "Ocmp "

let string_of_chunk c =
  match c with
  | Mint8signed    -> "Mint8signed"
  | Mint8unsigned  -> "Mint8unsigned"
  | Mint16signed   -> "Mint16signed"
  | Mint16unsigned -> "Mint16unsigned"
  | Mint32         -> "Mint32"
  | Mfloat32       -> "Mfloat32"
  | Mfloat64       -> "Mfloat64"

let string_of_external ef =
  match ef with
  | EF_external (i, _)        -> "External " ^ string_of_ident i
  | EF_builtin (i, _)         -> "Builtin " ^ string_of_ident i
  | EF_vload _                -> "VLoad"
  | EF_vstore _               -> "VStore"
  | EF_vload_global(_, i, _)  -> "VLoadGlobal " ^ string_of_ident i
  | EF_vstore_global(_, i, _) -> "VStoreGlobal " ^ string_of_ident i
  | EF_malloc                 -> "Malloc"
  | EF_free                   -> "Free"
  | EF_memcpy (_, _)          -> "Memcpy"
  | EF_annot (_, _)           -> "Annotation"
  | EF_annot_val (_, _)       -> "Annotation"

let string_of_instr i =
  match i with
  | Inop succ                             ->
      "Inop {succ: " ^ string_of_node succ ^ "}"
  | Iop (op, args, dest, succ)            ->
      "Iop {op: " ^ string_of_op op ^ "} {args: " ^ string_of_reglist args ^
      "} {dest: " ^ string_of_reg dest ^ "} {succ: " ^ string_of_node succ ^ "}"
  | Iload (chunk, addr, args, dest, succ) ->
      "Iload {chunk: " ^ string_of_chunk chunk ^ "} {addr: " ^
      string_of_addr addr ^ "} {args: " ^ string_of_reglist args ^
      "} {dest:" ^ string_of_reg dest ^ "} {succ: " ^ string_of_node succ ^ "}"
  | Istore (chunk, addr, args, src, succ) ->
      "Istore {chunk: " ^ string_of_chunk chunk ^ "} {addr: " ^
      string_of_addr addr ^ "} {args: " ^ string_of_reglist args ^ "} {src: " ^
      string_of_reg src ^ "} {succ: " ^ string_of_node succ ^ "}"
  | Icall (sign, fn, args, dest, succ)    ->
      "Icall {fn: " ^ string_of_reg_ident_sum fn ^ "} {args: " ^
      string_of_reglist args ^ "} {dest: " ^ string_of_reg dest ^ "} {succ: " ^
      string_of_node succ ^ "}"
  | Itailcall (sign, fn, args)            ->
      "Itailcall {fn: " ^ string_of_reg_ident_sum fn ^ "} {args: " ^
      string_of_reglist args ^ "}"
  | Ibuiltin (ef, args, dest, succ)       ->
      "Ibuiltin {ef: " ^ string_of_external ef ^ "} {args: " ^
      string_of_reglist args ^ "} {dest: " ^ string_of_reg dest ^ "} {succ: " ^
      string_of_node succ ^ "}"
  | Icond (cond, args, ifso, ifnot)       ->
      "Icond {args: " ^ string_of_reglist args ^ "} {ifso: " ^
      string_of_node ifso ^ "} {ifnot: " ^ string_of_node ifnot ^ "}"
  | Ijumptable (arg, tbl)                 ->
      "Ijumptable {}"
  | Ireturn r                             ->
      "Ireturn {r: " ^ string_of_reg_option r ^ "}"
