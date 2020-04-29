(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import LLIR.Aliasing.
Require Import LLIR.LLIR.
Require Import LLIR.Maps.
Require Import LLIR.State.
Require Import LLIR.Values.
Require Import LLIR.Verify.
Require Import LLIR.ReachingStores.

Import ListNotations.


Definition Object := (positive * positive)%type.

Definition get_load_addr (aa: points_to_set) (addr: reg): option Object :=
  match PTrie.get aa addr with
  | Some addrs => 
    match addrs with
    | [PTOffset object offset] =>
      Some (object, offset)
    | _ => None
    end
  | _ => None
  end.


Definition get_store_to (stores: reaching_stores) (k: node) (obj: Object): option reg :=
  match PTrie.get stores k with
  | Some objects =>
    match obj with
    | (object, offset) =>
      match PTrie.get objects object with
      | Some object' =>
        match PTrie.get object' offset with
        | Some write => Some write
        | _ => None
        end
      | _ => None
      end
    end
  | _ => None
  end.

Definition get_propagated_loads (f: func) (stores: reaching_stores) (aa: points_to_set): list (reg * reg) :=
  PTrie.values (reg * reg) (PTrie.map_opt inst (reg * reg) 
    (fun k inst =>
      match inst with
      | LLLd addr dst next =>
        match get_load_addr aa addr with
        | Some obj => 
          match get_store_to stores k obj with
          | Some src => Some (dst, src)
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    ) f.(fn_insts)).

Theorem src_dominates_dst:
  forall (f: func) (stores: reaching_stores) (aa: points_to_set) (loads: list (reg * reg)),
    loads = get_propagated_loads f stores aa ->
    forall (src: reg) (dst: reg),
      In (dst, src) loads -> Dominates f dst src.
Proof.
  intros f stores aa loads.
  intros Hdef.
  intros src dst.
  intros Helem.
  rewrite Hdef in Helem.
  unfold get_propagated_loads in Helem.
  
  

Definition propagate_store_to_load (f: func): func :=
  let aa := local_pta f in
  let stores := analyse_reaching_stores f aa in
  let loads := get_propagated_loads f stores aa in
  mkfunc f.(fn_args) f.(fn_stack) f.(fn_insts) f.(fn_phis) f.(fn_entry).

Theorem propagate_store_to_load_validity:
  forall (f: func),
    is_valid f -> is_valid (propagate_store_to_load f).
Proof.
Qed.

Theorem store_to_load_propagation :
  forall
    (p: prog) (p': prog)
    (f: func) (f': func)
    (s: state) (s': state)
    (pc_st: node) (pc_ld: node)
    (st_addr: reg) (st_val: reg) (st_next: node)
    (ld_addr: reg) (ld_dst: reg) (ld_next: node)
    (pts: points_to_set)
    (object: positive) (offset: positive)
    (id: name),
    Some f =  p ! id /\ Some f' = p' ! id
    /\
    Some (LLSt st_addr st_val st_next) = f.(fn_insts) ! pc_st
    /\
    Some (LLLd ld_addr ld_dst ld_next) = f.(fn_insts) ! pc_ld
    /\
    Some f' = rewrite f ld_dst st_val
    /\
    pts = local_pta f
    /\
    Some [PTOffset object offset] = pts ! ld_addr
  ->
    True
  .
Admitted.
