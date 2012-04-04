open Asm
open AST
open BinInt
open BinPos
open Library

let rec int_of_pos = function
  | Coq_xH   -> 1
  | Coq_xO q -> 2 * int_of_pos q
  | Coq_xI q -> 2 * int_of_pos q + 1

let string_of_pos p = string_of_int (int_of_pos p)

let string_of_coq_Z = function
  | Z0 -> "0"
  | Zpos p -> string_of_pos p
  | Zneg p -> "-" ^ string_of_pos p

let string_of_ident = string_of_pos
let string_of_label = string_of_pos
let string_of_iint = string_of_coq_Z

let string_of_ireg = function
| GPR0      -> "GPR0"
| GPR1      -> "GPR1"
| GPR2      -> "GPR2"
| GPR3      -> "GPR3"
| GPR4      -> "GPR4"
| GPR5      -> "GPR5"
| GPR6      -> "GPR6"
| GPR7      -> "GPR7"
| GPR8      -> "GPR8"
| GPR9      -> "GPR9"
| GPR10     -> "GPR10"
| GPR11     -> "GPR11"
| GPR12     -> "GPR12"
| GPR13     -> "GPR13"
| GPR14     -> "GPR14"
| GPR15     -> "GPR15"
| GPR16     -> "GPR16"
| GPR17     -> "GPR17"
| GPR18     -> "GPR18"
| GPR19     -> "GPR19"
| GPR20     -> "GPR20"
| GPR21     -> "GPR21"
| GPR22     -> "GPR22"
| GPR23     -> "GPR23"
| GPR24     -> "GPR24"
| GPR25     -> "GPR25"
| GPR26     -> "GPR26"
| GPR27     -> "GPR27"
| GPR28     -> "GPR28"
| GPR29     -> "GPR29"
| GPR30     -> "GPR30"
| GPR31     -> "GPR31"

let string_of_freg = function
| FPR0      -> "FPR0"
| FPR1      -> "FPR1"
| FPR2      -> "FPR2"
| FPR3      -> "FPR3"
| FPR4      -> "FPR4"
| FPR5      -> "FPR5"
| FPR6      -> "FPR6"
| FPR7      -> "FPR7"
| FPR8      -> "FPR8"
| FPR9      -> "FPR9"
| FPR10     -> "FPR10"
| FPR11     -> "FPR11"
| FPR12     -> "FPR12"
| FPR13     -> "FPR13"
| FPR14     -> "FPR14"
| FPR15     -> "FPR15"
| FPR16     -> "FPR16"
| FPR17     -> "FPR17"
| FPR18     -> "FPR18"
| FPR19     -> "FPR19"
| FPR20     -> "FPR20"
| FPR21     -> "FPR21"
| FPR22     -> "FPR22"
| FPR23     -> "FPR23"
| FPR24     -> "FPR24"
| FPR25     -> "FPR25"
| FPR26     -> "FPR26"
| FPR27     -> "FPR27"
| FPR28     -> "FPR28"
| FPR29     -> "FPR29"
| FPR30     -> "FPR30"
| FPR31     -> "FPR31"

let string_of_preg = function
| IR    (i0)    -> "IR(" ^ string_of_ireg i0 ^ ")"
| FR    (f0)    -> "FR(" ^ string_of_freg f0 ^ ")"
| PC            -> "PC"
| LR            -> "LR"
| CTR           -> "CTR"
| CARRY         -> "CARRY"
| CR0_0         -> "CR0_0"
| CR0_1         -> "CR0_1"
| CR0_2         -> "CR0_2"
| CR0_3         -> "CR0_3"

let string_of_external_function e =
  match e with
    | EF_builtin(name, sg) -> "EF_builtin"
    | EF_vload(chunk) -> "EF_vload"
    | EF_vstore(chunk) -> "EF_vstore"
    | EF_vload_global(_, _, _) -> "EF_vload_global"
    | EF_vstore_global(_, _, _) -> "EF_vstore_global"
    | EF_malloc -> "EF_malloc"
    | EF_free -> "EF_free"
    | EF_memcpy(sz, al) ->
      "EF_memcpy(" ^ string_of_z sz ^ ", " ^ string_of_z al ^ ")"
    | EF_annot(_, _) -> "EF_annot"
    | EF_annot_val(txt, targ) -> "EF_annot_val"
    | _ -> "UNKNOWN"

let string_of_constant = function
| Cint          (i0)        -> "Cint(" ^ string_of_iint i0 ^ ")"
| Csymbol_low   (i0, i1)    -> "Csymbol_low(" ^ string_of_ident i0 ^ ", " ^ string_of_iint i1 ^ ")"
| Csymbol_high  (i0, i1)    -> "Csymbol_high(" ^ string_of_ident i0 ^ ", " ^ string_of_iint i1 ^ ")"
| Csymbol_sda   (i0, i1)    -> "Csymbol_sda(" ^ string_of_ident i0 ^ ", " ^ string_of_iint i1 ^ ")"

let string_of_crbit = function
| CRbit_0    -> "CRbit_0"
| CRbit_1    -> "CRbit_1"
| CRbit_2    -> "CRbit_2"
| CRbit_3    -> "CRbit_3"

let string_of_memory_chunk mc = "MEMORY_CHUNK"

let string_of_annot_param = function
| APreg (p0)-> "APreg(" ^ string_of_preg p0 ^ ")"
| APstack(m0, c1)-> "APstack(" ^ string_of_memory_chunk m0 ^ ", " ^ string_of_coq_Z c1 ^ ")"

let string_of_instruction = function
| Padd      (i0, i1, i2)        -> "Padd(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Padde     (i0, i1, i2)        -> "Padde(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Paddi     (i0, i1, c2)        -> "Paddi(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Paddic    (i0, i1, c2)        -> "Paddic(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Paddis    (i0, i1, c2)        -> "Paddis(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Paddze    (i0, i1)            -> "Paddze(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pallocframe(c0, i1)            -> "Pallocframe(" ^ string_of_coq_Z c0 ^ ", " ^ string_of_iint i1 ^ ")"
| Pand_     (i0, i1, i2)        -> "Pand_(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pandc     (i0, i1, i2)        -> "Pandc(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pandi_    (i0, i1, c2)        -> "Pandi_(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Pandis_   (i0, i1, c2)        -> "Pandis_(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Pb        (l0)                -> "Pb(" ^ string_of_label l0 ^ ")"
| Pbctr                         -> "Pbctr"
| Pbctrl                        -> "Pbctrl"
| Pbf       (c0, l1)            -> "Pbf(" ^ string_of_crbit c0 ^ ", " ^ string_of_label l1 ^ ")"
| Pbl       (i0)                -> "Pbl(" ^ string_of_ident i0 ^ ")"
| Pbs       (i0)                -> "Pbs(" ^ string_of_ident i0 ^ ")"
| Pblr                          -> "Pblr"
| Pbt       (c0, l1)            -> "Pbt(" ^ string_of_crbit c0 ^ ", " ^ string_of_label l1 ^ ")"
| Pbtbl     (i0, l1)            -> "Pbtbl(" ^ string_of_ireg i0 ^ ", " ^ string_of_list string_of_label ", " l1 ^ ")"
| Pcmplw    (i0, i1)            -> "Pcmplw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pcmplwi   (i0, c1)            -> "Pcmplwi(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ")"
| Pcmpw     (i0, i1)            -> "Pcmpw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pcmpwi    (i0, c1)            -> "Pcmpwi(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ")"
| Pcror     (c0, c1, c2)        -> "Pcror(" ^ string_of_crbit c0 ^ ", " ^ string_of_crbit c1 ^ ", " ^ string_of_crbit c2 ^ ")"
| Pdivw     (i0, i1, i2)        -> "Pdivw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pdivwu    (i0, i1, i2)        -> "Pdivwu(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Peqv      (i0, i1, i2)        -> "Peqv(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pextsb    (i0, i1)            -> "Pextsb(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pextsh    (i0, i1)            -> "Pextsh(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pfreeframe(c0, i1)            -> "Pfreeframe(" ^ string_of_coq_Z c0 ^ ", " ^ string_of_iint i1 ^ ")"
| Pfabs     (f0, f1)            -> "Pfabs(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfadd     (f0, f1, f2)        -> "Pfadd(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ", " ^ string_of_freg f2 ^ ")"
| Pfcmpu    (f0, f1)            -> "Pfcmpu(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfcti     (i0, f1)            -> "Pfcti(" ^ string_of_ireg i0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfdiv     (f0, f1, f2)        -> "Pfdiv(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ", " ^ string_of_freg f2 ^ ")"
| Pfmake    (f0, i1, i2)        -> "Pfmake(" ^ string_of_freg f0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pfmr      (f0, f1)            -> "Pfmr(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfmul     (f0, f1, f2)        -> "Pfmul(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ", " ^ string_of_freg f2 ^ ")"
| Pfneg     (f0, f1)            -> "Pfneg(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfrsp     (f0, f1)            -> "Pfrsp(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ")"
| Pfsub     (f0, f1, f2)        -> "Pfsub(" ^ string_of_freg f0 ^ ", " ^ string_of_freg f1 ^ ", " ^ string_of_freg f2 ^ ")"
| Plbz      (i0, c1, i2)        -> "Plbz(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plbzx     (i0, i1, i2)        -> "Plbzx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plfd      (f0, c1, i2)        -> "Plfd(" ^ string_of_freg f0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plfdx     (f0, i1, i2)        -> "Plfdx(" ^ string_of_freg f0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plfs      (f0, c1, i2)        -> "Plfs(" ^ string_of_freg f0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plfsx     (f0, i1, i2)        -> "Plfsx(" ^ string_of_freg f0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plha      (i0, c1, i2)        -> "Plha(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plhax     (i0, i1, i2)        -> "Plhax(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plhz      (i0, c1, i2)        -> "Plhz(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plhzx     (i0, i1, i2)        -> "Plhzx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plfi      (f0, f1)            -> "Plfi(" ^ string_of_freg f0 ^ ", " ^ string_of_float f1 ^ ")"
| Plwz      (i0, c1, i2)        -> "Plwz(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Plwzx     (i0, i1, i2)        -> "Plwzx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pmfcrbit  (i0, c1)            -> "Pmfcrbit(" ^ string_of_ireg i0 ^ ", " ^ string_of_crbit c1 ^ ")"
| Pmflr     (i0)                -> "Pmflr(" ^ string_of_ireg i0 ^ ")"
| Pmr       (i0, i1)            -> "Pmr(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ")"
| Pmtctr    (i0)                -> "Pmtctr(" ^ string_of_ireg i0 ^ ")"
| Pmtlr     (i0)                -> "Pmtlr(" ^ string_of_ireg i0 ^ ")"
| Pmulli    (i0, i1, c2)        -> "Pmulli(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Pmullw    (i0, i1, i2)        -> "Pmullw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pnand     (i0, i1, i2)        -> "Pnand(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pnor      (i0, i1, i2)        -> "Pnor(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Por       (i0, i1, i2)        -> "Por(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Porc      (i0, i1, i2)        -> "Porc(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pori      (i0, i1, c2)        -> "Pori(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Poris     (i0, i1, c2)        -> "Poris(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Prlwinm   (i0, i1, i2, i3)    -> "Prlwinm(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_iint i2 ^ ", " ^ string_of_iint i3 ^ ")"
| Prlwimi   (i0, i1, i2, i3)    -> "Prlwimi(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_iint i2 ^ ", " ^ string_of_iint i3 ^ ")"
| Pslw      (i0, i1, i2)        -> "Pslw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psraw     (i0, i1, i2)        -> "Psraw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psrawi    (i0, i1, i2)        -> "Psrawi(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_iint i2 ^ ")"
| Psrw      (i0, i1, i2)        -> "Psrw(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstb      (i0, c1, i2)        -> "Pstb(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstbx     (i0, i1, i2)        -> "Pstbx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstfd     (f0, c1, i2)        -> "Pstfd(" ^ string_of_freg f0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstfdx    (f0, i1, i2)        -> "Pstfdx(" ^ string_of_freg f0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstfs     (f0, c1, i2)        -> "Pstfs(" ^ string_of_freg f0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstfsx    (f0, i1, i2)        -> "Pstfsx(" ^ string_of_freg f0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psth      (i0, c1, i2)        -> "Psth(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psthx     (i0, i1, i2)        -> "Psthx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstw      (i0, c1, i2)        -> "Pstw(" ^ string_of_ireg i0 ^ ", " ^ string_of_constant c1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pstwx     (i0, i1, i2)        -> "Pstwx(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psubfc    (i0, i1, i2)        -> "Psubfc(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psubfe    (i0, i1, i2)        -> "Psubfe(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Psubfic   (i0, i1, c2)        -> "Psubfic(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Pxor      (i0, i1, i2)        -> "Pxor(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_ireg i2 ^ ")"
| Pxori     (i0, i1, c2)        -> "Pxori(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Pxoris    (i0, i1, c2)        -> "Pxoris(" ^ string_of_ireg i0 ^ ", " ^ string_of_ireg i1 ^ ", " ^ string_of_constant c2 ^ ")"
| Plabel    (l0)                -> "Plabel(" ^ string_of_label l0 ^ ")"
| Pbuiltin  (e0, p1, p2)        -> "Pbuiltin(" ^ string_of_external_function e0 ^ ", " ^ string_of_list string_of_preg ", " p1 ^ ", " ^ string_of_preg p2 ^ ")"
| Pannot    (e0, a1)            -> "Pannot(" ^ string_of_external_function e0 ^ ", " ^ string_of_list string_of_annot_param ", " a1 ^ ")"

let string_of_init_data = function
| Init_int8(i)    -> "Init_int8("    ^ string_of_int (z_int_lax i)  ^ ")"
| Init_int16(i)   -> "Init_int16("   ^ string_of_int (z_int_lax i)  ^ ")"
| Init_int32(i)   -> "Init_int32("   ^ string_of_int32i (z_int32 i) ^ ")"
| Init_float32(f) -> "Init_float32(" ^ string_of_float f            ^ ")"
| Init_float64(f) -> "Init_float64(" ^ string_of_float f            ^ ")"
| Init_space(z)   -> "Init_space("   ^ string_of_int (z_int z)      ^ ")"
| Init_addrof(ident, ofs) ->
    "Init_addrof(" ^ string_of_pos ident ^ ", " ^ string_of_int32i (z_int32 ofs) ^ ")"
