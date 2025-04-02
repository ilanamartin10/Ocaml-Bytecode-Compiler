
(*
 ************************************************************
 1. Implementing the small-step semantics
 ************************************************************
 *)

(*
 ************************************************************
 1.1. name-based syntax
 ************************************************************
 *)

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

 (* 

let const : named_tm = NLam ("x", NLam ("y", NVar "x"))
let omega : named_tm = NLam ("x", NApp (NVar "x", NVar "x"))
let ycomb : named_tm =
 NLam
   ("f",
    NApp
      (omega,
       NLam
         ("x",
          NApp
            (NVar "f",
             NLam ("y", NApp (NApp (NVar "x", NVar "x"), NVar "y"))))))
let add   : named_tm =
 NApp
   (ycomb,
    NLam
      ("add",
       NLam
         ("x",
          NLam
            ("y",
             NITE
               (NIszero (NVar "x"),
                NVar "y",
                NSucc (NApp (NApp (NVar "add", NPred (NVar "x")), NVar "y")))))))
let sum   : named_tm =
 NApp
   (ycomb,
    NLam
      ("sum",
       NLam
         ("n",
          NITE
            (NIszero (NVar "n"),
             NZero,
             NApp (NApp (add, NVar "n"), NApp (NVar "sum", NPred (NVar "n"))))))) *)

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
         
(* (*
************************************************************
1.3. debruijnify
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

let rec debruijnify (ctx : ctx) =
 function
 | NVar s            -> Var (lookup s ctx)
 | NLam (s, t)       -> Lam (debruijnify (s :: ctx) t)
 | NApp (t1, t2)     -> App (debruijnify ctx t1, debruijnify ctx t2)
 | NTrue             -> True
 | NFalse            -> False
 | NITE (t1, t2, t3) -> ITE (debruijnify ctx t1, debruijnify ctx t2, debruijnify ctx t3)
 | NZero             -> Zero
 | NSucc t           -> Succ (debruijnify ctx t)
 | NIszero t         -> Iszero (debruijnify ctx t)
 | NPred t           -> Pred (debruijnify ctx t)

(*
************************************************************
1.4. shift
************************************************************
*)

let rec shift c d =
 function
 | Var n when n >= c                  -> Var (n + d)
 | (Var _ | True | False | Zero) as t -> t
 | Lam t                              -> Lam (shift (c + 1) d t)
 | App (t1, t2)                       -> App (shift c d t1, shift c d t2)
 | ITE (t1, t2, t3)                   -> ITE (shift c d t1, shift c d t2, shift c d t3)
 | Succ t                             -> Succ (shift c d t)
 | Iszero t                           -> Iszero (shift c d t)
 | Pred t                             -> Pred (shift c d t)

(*
************************************************************
1.5. Substitution
************************************************************
*)

let rec subst s j =
 function
 | Var n when n = j                   -> s
 | (Var _ | True | False | Zero) as t -> t
 | Lam t                              -> Lam (subst (shift 0 1 s) (j + 1) t)
 | App (t1, t2)                       -> App (subst s j t1, subst s j t2)
 | ITE (t1, t2, t3)                   -> ITE (subst s j t1, subst s j t2, subst s j t3)
 | Succ t                             -> Succ (subst s j t)
 | Iszero t                           -> Iszero (subst s j t)
 | Pred t                             -> Pred (subst s j t)

(*
************************************************************
1.6. Step
************************************************************
*)

type progress = IsValue | Step of tm

exception Stuck

let rec step =
 function
 | Var n -> raise IllScoped
 | Lam _ | True | False | Zero -> IsValue
 | App (t1, t2) ->
    begin
      match step t1 with
      | Step t1' -> Step (App (t1', t2))
      | IsValue  ->
         match t1, step t2 with
         | _,       Step t2' -> Step (App (t1, t2'))
         | Lam t1', IsValue  -> Step (shift 0 (-1) (subst (shift 0 1 t2) 0 t1'))
         | _                 -> raise Stuck
    end
 | ITE (t1, t2, t3) ->
    begin
      match t1, step t1 with
      | _,     Step t1' -> Step (ITE (t1', t2, t3))
      | True,  IsValue  -> Step t2
      | False, IsValue  -> Step t3
      | _               -> raise Stuck
    end
 | Succ t ->
    begin
      match step t with
      | Step t' -> Step (Succ t')
      | IsValue -> IsValue
    end
 | Iszero t ->
    begin
      match t, step t with
      | _,      Step t' -> Step (Succ t')
      | Zero,   IsValue -> Step True
      | Succ _, IsValue -> Step False
      | _               -> raise Stuck
    end
 | Pred t ->
    begin
      match t, step t with
      | _,       Step t' -> Step (Succ t')
      | Zero,    IsValue -> Step Zero
      | Succ t', IsValue -> Step t'
      | _                -> raise Stuck
    end

(*
************************************************************
1.7. Eval
************************************************************
*)

let rec eval t =
 match step t with
 | Step t' -> eval t'
 | IsValue -> t

(*
************************************************************
1.8. Fifteen
************************************************************
*)

let five = NSucc (NSucc (NSucc (NSucc (NSucc NZero))))

let fifteen = eval (debruijnify [] (NApp (sum, five)))

(*
************************************************************
2. Implementing the big-step semantics
************************************************************
*)

let rec big_eval =
 function
 | Var n -> raise IllScoped
 | (Lam _ | True | False | Zero) as t -> t
 | App (t1, t2) ->
    begin
      match big_eval t1 with
      | Lam t1' ->
         let arg = shift 0 1 (big_eval t2) in
         big_eval (shift 0 (-1) (subst arg 0 t1'))
      | _ -> raise Stuck
    end
 | ITE (t1, t2, t3) ->
    begin
      match big_eval t1 with
      | True  -> big_eval t2
      | False -> big_eval t3
      | _     -> raise Stuck
    end
 | Succ t -> Succ (big_eval t)
 | Iszero t ->
    begin
      match big_eval t with
      | Zero   -> True
      | Succ _ -> False
      | _      -> raise Stuck
    end
 | Pred t ->
    begin
      match big_eval t with
      | Zero   -> Zero
      | Succ v -> v
      | _      -> raise Stuck
    end *)
