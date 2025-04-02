 type tp =
 | TNat
 | TFloat
 | TRec of (string * tp) list
 | TTop
 | TFun of tp * tp
 | TBool

 
let rec subtype t1 t2 = 
 match t1, t2 with
 | TNat, TFloat -> true  (* int <: float *)
 | TBool, TBool -> true
 | TNat, TNat -> true
 | TFloat, TFloat -> true
 | TFun (s1, t1), TFun (s2, t2) -> subtype s2 s1 && subtype t1 t2
 | _ , TTop-> true
 (* Width and depth subtyping and permutation *)
 | TRec fields1, TRec fields2 ->
     List.for_all
       (fun (label2, tp2) ->
          match List.assoc_opt label2 fields1 with
          | Some tp1 -> subtype tp1 tp2
          | None -> false)
       fields2
 | _ -> false


type tm =
 (* x *)
 | Var    of int
 (* λ x . t *)
 | Lam   of tp * tm
 (* t1 t2 *)
 | App    of tm * tm
 (* true *)
 | True
 (* false *)
 | False
 (* if t1 then t2 else t3 *)
 | ITE    of tm * tm * tm
 (* z *)
 | Zero
 (* succ t *)
 | Succ   of tm
 (* iszero t *)
 | Iszero of tm
 (* pred t *)
 | Pred   of tm
 | Record of (string * tm) list (* record literal *)
 | Proj   of tm * string      (* record projection *)
 
(* Type checker *)
exception TypeError

let rec typeof ctx =
  function
  | Var n -> 
    (try List.nth ctx n
     with Failure _ ->
       raise TypeError)
  | Lam (ann, body) ->
      let body_type = typeof (ann :: ctx) body in
      TFun (ann, body_type)
  | App (t1, t2) ->
     (match typeof ctx t1, typeof ctx t2 with
      | TFun (arg, ret), t when subtype t arg -> ret
      | _ -> raise TypeError)
  | True | False -> TBool
  | Zero -> TNat
  | Succ t | Pred t ->
      if subtype (typeof ctx t) TNat then TNat
      else raise TypeError
  | Iszero t ->
      if subtype (typeof ctx t) TNat then TBool
      else raise TypeError
  | ITE (t1, t2, t3) ->
    let ty1 = typeof ctx t1 in
    if not (subtype ty1 TBool) then
      raise TypeError
    else
      let ty2 = typeof ctx t2 in
      let ty3 = typeof ctx t3 in
      if subtype ty2 ty3 then ty3
      else if subtype ty3 ty2 then ty2
      else
        raise TypeError

  | Record fields ->
    let field_types = List.map (fun (label, term) -> (label, typeof ctx term)) fields in
      TRec field_types
    
  | Proj (t1, label) ->
    (match typeof ctx t1 with
      | TRec fields ->
        (match List.assoc_opt label fields with
          | Some ty -> ty
          | None -> raise TypeError)
          | _ -> raise TypeError)

(*
************************************************************
Testing 
************************************************************
*)

(* Record literal *)
let test_record () =
  (* record: { x = 0; y = true } *)
  let rec_term = Record [("x", Zero); ("y", True)] in
  let rec_type = typeof [] rec_term in
  match rec_type with
  | TRec fields ->
      Printf.printf "Record literal type: {%s}\n"
        (String.concat "; " (List.map (fun (lbl, tp) ->
            match tp with
            | TNat -> lbl ^ ": TNat"
            | TBool -> lbl ^ ": TBool"
            | _ -> lbl ^ ": (other)"
          ) fields))
  | _ ->
      Printf.printf "Record literal did not typecheck as a record.\n"

(* record projection *)
let test_projection () =
  (* project the "x" field *)
  let rec_term = Record [("x", Zero); ("y", True)] in
  let proj_term = Proj (rec_term, "x") in
  let proj_type = typeof [] proj_term in
  match proj_type with
  | TNat ->
      Printf.printf "Projection of field 'x' has type TNat as expected.\n"
  | _ ->
      Printf.printf "Projection of field 'x' has unexpected type.\n"

(* 3. record subtyping *)
let test_subtyping () =
  (* two record types:
     r_full : { x: TNat; y: TBool }
     r_partial : { x: TNat } *)
  let r_full = TRec [("x", TNat); ("y", TBool)] in
  let r_partial = TRec [("x", TNat)] in
  if subtype r_full r_partial then
    Printf.printf "Subtyping holds: r_full <: r_partial (width subtyping)\n"
  else
    Printf.printf "Subtyping fails: r_full is not a subtype of r_partial\n"

let () =
  test_record ();
  test_projection ();
  test_subtyping ()


(*
 ************************************************************
debruijnify
 ************************************************************
 *)

type name = string
type ctx = name list

exception IllScoped

(* a helper function to get the debruijn index of named variable *)
let lookup s =
  let rec helper n =
    function
    | []                     -> raise IllScoped
    | s' :: _    when s = s' -> n
    | _  :: ctx'             -> helper (n + 1) ctx'
  in
  helper 0

(*
 ************************************************************
shift
 ************************************************************
 *)
 let rec shift c d t =
  match t with
  | Var n when n >= c -> Var (n + d)
  | Var _ | True | False | Zero -> t
  | Lam (ann, body) -> Lam (ann, shift (c+1) d body)
  | App (t1, t2) -> App (shift c d t1, shift c d t2)
  | ITE (t1, t2, t3) -> ITE (shift c d t1, shift c d t2, shift c d t3)
  | Succ t1 -> Succ (shift c d t1)
  | Iszero t1 -> Iszero (shift c d t1)
  | Pred t1 -> Pred (shift c d t1)
  | Record fields ->
      Record (List.map (fun (label, term) -> (label, shift c d term)) fields)
  | Proj (t1, label) -> Proj (shift c d t1, label)

(*
************************************************************
substitution
************************************************************
*)
let rec subst s j t =
  match t with
  | Var n when n = j -> s
  | Var _ | True | False | Zero -> t
  | Lam (ann, body) -> Lam (ann, subst (shift 0 1 s) (j+1) body)
  | App (t1, t2) -> App (subst s j t1, subst s j t2)
  | ITE (t1, t2, t3) -> ITE (subst s j t1, subst s j t2, subst s j t3)
  | Succ t1 -> Succ (subst s j t1)
  | Iszero t1 -> Iszero (subst s j t1)
  | Pred t1 -> Pred (subst s j t1)
  | Record fields ->
      Record (List.map (fun (label, term) -> (label, subst s j term)) fields)
  | Proj (t1, label) -> Proj (subst s j t1, label)

(*
************************************************************
small-step semantics
************************************************************
*)
type progress = IsValue | Step of tm

exception Stuck

let rec step t =
  match t with
  | Var n -> raise IllScoped
  | Lam _ | True | False | Zero -> IsValue
  | App (t1, t2) ->
      begin
        match step t1 with
        | Step t1' -> Step (App (t1', t2))
        | IsValue  ->
            (match t1, step t2 with
             | _, Step t2' -> Step (App (t1, t2'))
             | Lam (_, body), IsValue -> Step (shift 0 (-1) (subst (shift 0 1 t2) 0 body))
             | _ -> raise Stuck)
      end
  | ITE (t1, t2, t3) ->
      begin
        match t1, step t1 with
        | _, Step t1' -> Step (ITE (t1', t2, t3))
        | True, IsValue -> Step t2
        | False, IsValue -> Step t3
        | _ -> raise Stuck
      end
  | Succ t1 ->
      begin
        match step t1 with
        | Step t' -> Step (Succ t')
        | IsValue -> IsValue
      end
  | Iszero t1 ->
      begin
        match t1, step t1 with
        | _, Step t' -> Step (Iszero t')
        | Zero, IsValue -> Step True
        | Succ _, IsValue -> Step False
        | _ -> raise Stuck
      end
  | Pred t1 ->
      begin
        match t1, step t1 with
        | _, Step t' -> Step (Pred t')
        | Zero, IsValue -> Step Zero
        | Succ t', IsValue -> Step t'
        | _ -> raise Stuck
      end
  | Record fields ->
      (* Evaluate record fields left-to-right *)
      let rec step_fields acc = function
        | [] -> IsValue
        | (label, term)::rest ->
            (match step term with
             | Step term' -> Step (Record (List.rev acc @ ((label, term')::rest)))
             | IsValue -> step_fields ((label, term)::acc) rest)
      in step_fields [] fields
  | Proj (t1, label) ->
      begin
        match step t1 with
        | Step t1' -> Step (Proj (t1', label))
        | IsValue ->
            (match t1 with
             | Record fields ->
                 (match List.assoc_opt label fields with
                  | Some v -> Step v
                  | None -> raise Stuck)
             | _ -> raise Stuck)
      end

(*
************************************************************
Eval
************************************************************
*)
let rec big_eval t =
  match t with
  | Var n -> raise IllScoped
  | Lam _ | True | False | Zero -> t
  | App (t1, t2) ->
      begin
        match big_eval t1 with
        | Lam (_, body) ->
            let arg = shift 0 1 (big_eval t2) in
            big_eval (shift 0 (-1) (subst arg 0 body))
        | _ -> raise Stuck
      end
  | ITE (t1, t2, t3) ->
      begin
        match big_eval t1 with
        | True  -> big_eval t2
        | False -> big_eval t3
        | _     -> raise Stuck
      end
  | Succ t1 -> Succ (big_eval t1)
  | Iszero t1 ->
      begin
        match big_eval t1 with
        | Zero   -> True
        | Succ _ -> False
        | _      -> raise Stuck
      end
  | Pred t1 ->
      begin
        match big_eval t1 with
        | Zero   -> Zero
        | Succ v -> v
        | _      -> raise Stuck
      end
  | Record fields ->
      let eval_fields = List.map (fun (l, t) -> (l, big_eval t)) fields in
      Record eval_fields
  | Proj (t1, label) ->
      let t1' = big_eval t1 in
      (match t1' with
       | Record fields ->
           (match List.assoc_opt label fields with
            | Some v -> v
            | None -> raise Stuck)
       | _ -> raise Stuck)

(*
************************************************************
Testing 
************************************************************
*)

(* lambda evaluation *)
let test_lambda () =
  (* (λ x:TNat. Succ x) 0 *)
  let term = App (Lam (TNat, Succ (Var 0)), Zero) in
  let result = big_eval term in
  match result with
  | Succ Zero -> Printf.printf "Lambda test succeeded: (λx. Succ x) 0 evaluated to Succ 0\n"
  | _ -> Printf.printf "Lambda test failed\n"


(* lambda with record subtyping *)
let test_lambda_subtyping () =
  (* lambda that expects a record with a single field "x" of type TNat, and returns the "x" field.*)
  let lam = Lam (TRec [("x", TNat)], Proj (Var 0, "x")) in

  (* record with two fields:
         "x" with value Zero and "y" with value True.
          Its type is TRec [("x", TNat); ("y", TBool)].
     By width subtyping, this record is a subtype of TRec [("x", TNat)].
  *)
  let arg = Record [("x", Zero); ("y", True)] in

  let app = App (lam, arg) in
  let t = typeof [] app in
  match t with
  | TNat ->
      Printf.printf "Lambda subtyping test succeeded: application typed as TNat\n"
  | _ ->
      Printf.printf "Lambda subtyping test failed: unexpected type\n"

let () =
  test_lambda ();
  test_lambda_subtyping ();
