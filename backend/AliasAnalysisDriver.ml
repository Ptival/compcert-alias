open AST
open BinPos
open Camlcoq
open Datatypes
open Maps
open Op
open AliasAnalysis
open AliasAnalysisPrinters
open RTL

let cmp_keys x y =
  match x, y with
  | (a, _), (b, _) -> compare (int_of_pos b) (int_of_pos a)

(*let printer (k, v) =
  print_endline (string_of_pos k ^ ": " ^
                   (string_of_ptmap (coerce_solver v) ^ "\n"))*)

let sorted_map f t =
  let nodes = PTree.elements t in
  let sorted_nodes = List.sort cmp_keys nodes in
  List.map f sorted_nodes

let biprint tnode tres key =
  match PTree.get key tnode, PTree.get key tres with
  | None, None   -> assert false
  | Some n, None -> print_endline ("NO RESULT FOR NODE: " ^ string_of_instr n)
  | None, Some _ -> assert false
  | Some node, Some res ->
      let (rmap, mmap) = coerce_solver res in
      print_endline (
        "RMAP: " ^ string_of_rmap rmap ^ "\n"
               ^ "MMAP: " ^ string_of_mmap mmap ^ "\n"
               ^ string_of_pos key ^ ": " ^ string_of_instr node
      )

(* Assuming tnode and tres share the same keys *)
let sorted_biprint tnode tres =
  let keys = PTree.xkeys tnode Coq_xH in
  let sorted_keys =
    List.sort (fun x y -> compare (int_of_pos y) (int_of_pos x)) keys in
  List.map (biprint tnode tres) sorted_keys

let alias_analysis fd =
  match fd with
  | Internal f ->
      print_endline ("--------------------");
      let res = funanalysis f in
      begin match res with
      | None            -> print_endline "KILDALL FAILED"
      | Some (_, ptree) ->
          let _ = sorted_biprint (fn_code f) ptree in
          ()
      end
  | External _ -> ()
