open Camlp4.PreCast
open Elaborator
open Monad
open Grammar

let parsetype s = Gram.parse_string mtype Ast.Loc.ghost s
let parsexpr s = Gram.parse_string mexpr Ast.Loc.ghost s

let display s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborate (parsexpr s) _loc$>>

let displays s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborates (parsexpr s) _loc$>>

let display_ast t = 
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $t$>>

let test_scheck env term tp =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let term = parsexpr term in
  let tp = parsetype tp in
  match scheck env term tp with
  | Ok e -> display_ast (e "C" "U" "Dsl" Loc.ghost)
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_ssynth env term =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let term = parsexpr term in
  match ssynth env term with
  | Ok (e,tp) -> display_ast (e "C" "U" "Dsl" Loc.ghost); tp
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_scheck_shrink env env' term tp =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let env' = List.map (fun (x, tstr) -> (x, parsetype tstr)) env' in
  let term = parsexpr term in
  let tp = parsetype tp in
  match scheck_shrink env env' term tp with
  | Ok e -> display_ast (e "C" "U" "Dsl" Loc.ghost)
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_ssynth_shrink env env' term =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let env' = List.map (fun (x, tstr) -> (x, parsetype tstr)) env' in
  let term = parsexpr term in
  match ssynth_shrink env env' term with
  | Ok (e,tp) -> display_ast (e "C" "U" "Dsl" Loc.ghost); tp
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_ucheck env uenv term tp =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let uenv = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv in
  let term = parsexpr term in
  let tp = parsetype tp in
  match ucheck env uenv term tp with
  | Ok e -> display_ast (e "U" "C" "Dsl" Loc.ghost)
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_usynth env uenv term =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let uenv = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv in
  let term = parsexpr term in
  match usynth env uenv term with
  | Ok (e,tp) -> display_ast (e "U" "C" "Dsl" Loc.ghost); tp
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_ucheck_shrink env uenv uenv' term tp =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let uenv = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv in
  let uenv' = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv' in
  let term = parsexpr term in
  let tp = parsetype tp in
  match ucheck_shrink env uenv uenv' term tp with
  | Ok e -> display_ast (e "U" "C" "Dsl" Loc.ghost)
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)

let test_usynth_shrink env uenv uenv' term =
  let env = List.map (fun (x, tstr) -> (x, parsetype tstr)) env in
  let uenv = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv in
  let uenv' = List.map (fun (x, tstr) -> (x, parsetype tstr)) uenv' in
  let term = parsexpr term in
  match usynth_shrink env uenv uenv' term with
  | Ok (e,tp) -> display_ast (e "U" "C" "Dsl" Loc.ghost); tp
  | Error(loc, msg) -> failwith (Printf.sprintf "%s: %s" (Loc.to_string loc) msg)
