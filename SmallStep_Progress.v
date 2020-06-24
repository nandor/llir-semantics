(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import LLIR.Values.
Require Import LLIR.Maps.
Require Import LLIR.LLIR.
Require Import LLIR.Dom.
Require Import LLIR.Eval.
Require Import LLIR.SSA.
Require Import LLIR.Block.
Require Import LLIR.Typing.
Require Import LLIR.Signal.
Require Import LLIR.Liveness.
Require Import LLIR.Syscall.
Require Import LLIR.Frame.
Require Import LLIR.State.
Require Import LLIR.SmallStep.

Import ListNotations.



Theorem small_step_progress:
  forall (p: prog) (st: estate),
    WellTypedProg p ->
    valid_prog p ->
    Normal p st ->
    ~Final st ->
    exists (tr: trace) (st': estate),
      step p st tr st'.
Proof.
  intros p st Hwty Hvp Hv Hnf; destruct st.
  {
    generalize (valid_state_can_execute p h stk Hv);
    intros [fr [f [pc [i Hexec]]]]; subst.
    inversion Hv as [
        p' stk_fr stk_frs stk_next stk_frames stk_init
        h' Hvalid Hvalid_top Hvalid_mid Hp' Hstk
    ]; subst p' h'.
    inversion Hexec as [
        p'' stk_fr' stk_frs' stk_next' stk_frames'' stk_init''
        func' frame' i''
        FRAME' FUNC' INST' Hp'' Hstk' Hinst Hfunc' Epc Hi''
    ]; subst i'' func' frame' p''.
    assert (H_f_valid: valid_func f).
    { unfold valid_prog in Hvp. apply Hvp with (n := fr_func fr); auto. }
    assert (Hwtf: WellTypedFunc f).
    { inversion Hwty; apply FUNCS with (n := fr_func fr); auto. }
    assert (Hwti: WellTypedInst (ty_env f) i).
    {
      inversion Hwtf; inversion INSTS;
      apply INSTS0 with (n := (fr_pc fr)); auto.
    }
    inversion Hvalid_top; inversion VALID; subst fr_id frames p0 p1 fr1.
    generalize (uses_are_defined p h stk f fr pc i Hv Hexec); intros Hval.
    rewrite <- Hstk in Hstk'; inversion Hstk'; clear Hstk';
    subst stk_fr' stk_frs' stk_frames'' stk_init'' stk_next'.
    rewrite <- FRAME in FRAME'; inversion FRAME'; subst fr0.
    rewrite <- FUNC in FUNC'; inversion FUNC'; subst f0.
    rewrite Hstk.

    Ltac used_value f fr pc i sym sym_val Hsym Hreg :=
      match goal with
      | [ Hval: forall (r: reg), UsedAt f pc r -> _ |- _ ] =>
        let H := fresh in
        assert (H: UsedAt f pc sym);
        [ constructor; apply inst_used_at with i; subst i pc; auto; constructor
        |];
        apply Hval in H;
        destruct H as [sym_val Hreg];
        assert (Hsym: Some sym_val = fr.(fr_regs) ! sym);
        [ rewrite Hreg; reflexivity |]
      end.

    Ltac step_state :=
      match goal with
      | [ |- context [ step _ _ ?tr ?state ] ] => exists tr; exists state; auto
      end.

    Ltac used_args pc i args0 values Hvalues :=
      match goal with
      | [ REGS: context [ LiveAt ?f _ _ -> _ ]
        , FUNC: Some ?f = ?p ! (fr_func ?fr)
        |- _ ] =>
          let H := fresh in
          assert (H: forall arg, In arg args0 -> LiveAt f arg (fr_pc fr));
            [ intros arg Hin;
              apply live_at with (use := pc) (p := [pc]);
              [ subst pc; constructor; auto
              | intros def Hne Hin'; inversion Hin'; subst; contradiction
              | apply used_at_inst; apply inst_used_at with i; subst i pc;
                auto; constructor; auto
              ]
            |];
          destruct (call_args p f fr args0 FUNC REGS H) as [values Hvalues]
      end.

    Ltac used_callee h callee callee_value Hcallee_reg args0 :=
      match goal with
      | [ Hexec: Executing ?p ?stk ?fr ?f ?pc ?inst |- _ ] =>
        destruct (Function_dec callee_value) as [Eq|Ne];
          [|
            assert (Hc: Callee inst callee); [constructor|];
            symmetry in Hcallee_reg;
            generalize (eval_call_broken
              p stk h fr f pc inst callee callee_value
              Hexec Hc Hcallee_reg Ne
            ); step_state
          ]
      end.

    destruct i eqn:Ei;
      try match goal with
      | [ dst: ty * reg |- _ ] => destruct dst as [t dst]
      end.
    {
      used_value f fr pc i addr addr_value Haddr Haddr_reg.
      destruct (load_value_or_signal stk h t addr_value) as [Hload|Hsig].
      {
        destruct Hload as [dst_value Hload].
        generalize (eval_ld_value
          p stk h fr f pc dst t next addr
          addr_value dst_value Hexec Haddr Hload
        ); step_state.
      }
      {
        destruct Hsig as [sig Hsig].
        generalize (eval_ld_sig
          p stk h fr f pc dst t next addr
          addr_value sig Hexec Haddr Hsig
        ); step_state.
      }
    }
    {
      generalize (arg_complete fr index t); intros [dst_value Harg].
      generalize (eval_arg
        p stk h fr f pc dst t next index dst_value
        Hexec Harg
      ); step_state.
    }
    {
      generalize (eval_int p stk h fr f pc dst next value Hexec).
      step_state.
    }
    {
      used_value f fr pc i cond cond_value Hcond Hcond_reg.
      destruct (value_is_true_or_false cond_value) as [Eq|Ne].
      {
        used_value f fr pc i vt vt_value Hvt Hvt_reg.
        generalize (eval_select_true
          p stk h fr f pc dst t next cond vt vf
          cond_value vt_value Hexec Hcond Hvt Eq
        ); step_state.
      }
      {
        used_value f fr pc i vf vf_value Hvf Hvf_reg.
        generalize (eval_select_false
          p stk h fr f pc dst t next cond vt vf
          cond_value vf_value Hexec Hcond Hvf Ne
        ); step_state.
      }
    }
    {
      generalize (eval_frame
        p stk h fr f pc dst next object offset
        Hexec
      ); step_state.
    }
    {
      generalize (eval_global
        p stk h fr f pc dst next segment object offset
        Hexec
      ); step_state.
    }
    { generalize (eval_func p stk h fr f pc dst next func Hexec); step_state. }
    { generalize (eval_und p stk h fr f pc t dst next Hexec); step_state. }
    {
      used_value f fr pc i arg arg_value Harg Harg_reg.
      inversion Hwti; subst t0 dst0 next0 op0 arg0.
      unfold well_typed_reg in ARG_TY;
      destruct (VALS arg arg_value Harg) as [arg_ty [Harg_ty Harg_type_of]];
      rewrite ARG_TY in Harg_ty; inversion Harg_ty; subst argt.
      destruct (unary_value_or_signal op arg_value arg_ty t OP Harg_type_of) as
        [ [dst_value [_ Hdst]]
        | [sig Hsig]
        ].
      {
        generalize (eval_unary_value
          p stk h fr f pc dst t next op arg dst_value arg_value
          Hexec Harg Hdst
        ); step_state.
      }
      {
        generalize (eval_unary_signal
          p stk h fr f pc dst t next op arg arg_value sig
          Hexec Harg Hsig
        ); step_state.
      }
    }
    {
      used_value f fr pc i lhs lhs_value Hlhs Hlhs_reg.
      used_value f fr pc i rhs rhs_value Hrhs Hrhs_reg.
      inversion Hwti; subst t0 dst0 next0 op0 l r.
      unfold well_typed_reg in LHS_TY;
      destruct (VALS lhs lhs_value Hlhs) as [lhs_ty [Hlhs_ty Hlhs_type_of]];
      rewrite LHS_TY in Hlhs_ty; inversion Hlhs_ty; subst tl.
      unfold well_typed_reg in RHS_TY;
      destruct (VALS rhs rhs_value Hrhs) as [rhs_ty [Hrhs_ty Hrhs_type_of]];
      rewrite RHS_TY in Hrhs_ty; inversion Hrhs_ty; subst tr.
      destruct (binary_value_or_signal
        op lhs_value rhs_value lhs_ty rhs_ty t
        OP Hlhs_type_of Hrhs_type_of) as [[dst_value [_ Hdst]]|[sig Hsig]].
      {
        generalize (eval_binary_value
          p stk h fr f pc dst t op lhs rhs next lhs_value rhs_value dst_value
          Hexec Hlhs Hrhs Hdst
        ); step_state.
      }
      {
        generalize (eval_binary_signal
          p stk h fr f pc dst t op lhs rhs next lhs_value rhs_value sig
          Hexec Hlhs Hrhs Hsig
        ); step_state.
      }
    }
    {
      used_value f fr pc i src src_value Hsrc Hsrc_reg.
      generalize (eval_mov
        p stk h fr f pc dst t next src src_value
        Hexec Hsrc
      ); step_state.
    }
    {
      used_value f fr pc i sno sno_value Hsno Hsno_reg.
      symmetry in Hsno_reg.
      generalize (VALS sno sno_value Hsno_reg); intros [ty [Hty Hty_of]].
      inversion Hwti; subst next0 dst0 sno0 args0.
      unfold well_typed_reg in SNO_TY.
      rewrite <- Hty in SNO_TY; inversion SNO_TY; subst ty.
      assert (Hargs_live: forall arg, In arg args -> LiveAt f arg (fr_pc fr)).
      {
        intros arg Hin'.
        apply live_at with (use := pc) (p := [pc]).
        - subst pc; constructor; apply REACH.
        - intros def contra Hin; inversion Hin; subst; contradiction.
        - apply used_at_inst; apply inst_used_at with i; subst; try constructor; auto.
      }
      generalize (syscall_args
        p f fr args (ty_env f)
        FUNC ARG_TY REGS Hargs_live VALS
      ); intros [sys_values Hsys_args].
      destruct (syscall_number_complete sno_value Hty_of) as [[s Esys]|[ENoSys|EUnd]].
      {
        destruct (syscall_ret_or_sig s sys_values stk h) as
          [ [tr [stk'' [h'' [dst_value Eret]]]]
          | [sig [tr Esig]]
          ].
        {
          generalize (eval_syscall_ret
            p stk h fr f pc dst next tr args sys_values sno s sno_value
            dst_value stk'' h''
            Hsys_args Hsno_reg Esys Hexec Eret
          ); step_state.
        }
        {
          generalize (eval_syscall_sig
            p stk h fr f pc dst next tr args sys_values sno s sno_value sig
            Hsys_args Hsno_reg Esys Hexec Esig
          ); step_state.
        }
      }
      {
        generalize (eval_syscall_nosys
          p stk h fr f pc dst next [] args sys_values sno sno_value
          Hsys_args Hsno_reg ENoSys Hexec
        ); step_state.
      }
      {
        generalize (eval_syscall_und_enosys
          p stk h fr f pc dst next [] args sys_values sno sno_value
        ); step_state.
      }
    }
    {
      used_value f fr pc i callee callee_value Hcallee Hcallee_reg.
      used_callee h callee callee_value Hcallee_reg args0.
      used_args pc i args values Hvalues.
      inversion Eq as [func Hfunc]; subst callee_value.
      generalize (FN_VALS callee func Hcallee); intros Hsome_func.
      destruct (p ! func) as [callee_fn|] eqn:Efunc; try contradiction.
      symmetry in Efunc.
      generalize (eval_call
        p stk h stk_fr stk_frs stk_next stk_frames stk_init
        fr f pc callee next dst func callee_fn args values
        Hexec Hcallee Efunc Hvalues
      ); rewrite Hstk; step_state.
    }
    {
      used_value f fr pc i callee callee_value Hcallee Hcallee_reg.
      used_callee h callee callee_value Hcallee_reg args.
      used_args pc i args values Hvalues.
      inversion Eq as [func Hfunc]; subst callee_value.
      generalize (FN_VALS callee func Hcallee); intros Hsome_func.
      destruct (p ! func) as [callee_fn|] eqn:Efunc; try contradiction.
      symmetry in Efunc.
      generalize (eval_invoke
        p stk h stk_fr stk_frs stk_next stk_frames stk_init
        fr f pc callee next dst exn func callee_fn args values
        Hexec Hcallee Efunc Hvalues
      ); rewrite Hstk; step_state.
    }
    {
      used_value f fr pc i callee callee_value Hcallee Hcallee_reg.
      used_callee h callee callee_value Hcallee_reg args.
      used_args pc i args values Hvalues.
      inversion Eq as [fn Hfn]. rewrite <- Hfn in Hcallee.
      generalize (FN_VALS callee fn Hcallee); intros Hfn_not_none.
      destruct (p ! fn) as [func|] eqn:Efunc; try contradiction.
      symmetry in Efunc.
      generalize (eval_tcall
        p stk h stk_fr stk_frs stk_next stk_frames stk_init fr f
        pc callee fn func args values Hexec Hcallee Efunc Hvalues).
      rewrite Hstk.
      step_state.
    }
    {
      used_value f fr pc i callee callee_value Hcallee Hcallee_reg.
      used_callee h callee callee_value Hcallee_reg args.
      used_args pc i args values Hvalues.
      inversion Eq as [fn Hfn]. rewrite <- Hfn in Hcallee.
      generalize (FN_VALS callee fn Hcallee); intros Hfn_not_none.
      destruct (p ! fn) as [func|] eqn:Efunc; try contradiction.
      symmetry in Efunc.
      generalize (eval_tinvoke
        p stk h stk_fr stk_frs stk_next stk_frames stk_init fr f
        pc callee exn fn func args values Hexec Hcallee Efunc Hvalues).
      rewrite Hstk.
      step_state.
    }
    {
      used_value f fr pc i addr addr_value Haddr Haddr_reg.
      used_value f fr pc i value value_value Hvalue Hvalue_reg.
      destruct (store_value_signal_break stk h addr_value value_value) as
        [ [h'' Evalue]
        | [ [s Esig]| Ebreak]
        ].
      {
        generalize (eval_st_value
          p stk h fr f pc next addr value addr_value value_value h''
          Hexec Haddr Hvalue Evalue
        ); step_state.
      }
      {
        generalize (eval_st_sig
          p stk h fr f pc next addr value addr_value s
          Hexec Haddr Esig
        ); step_state.
      }
      {
        generalize (eval_st_break
          p stk h fr f pc next addr value addr_value
          Hexec Haddr Ebreak
        ); step_state.
      }
    }
    {
      destruct (top_or_return stk) as [Htop|[vr [vrs Hret]]].
      {
        generalize (eval_ret_top p stk h fr f pc value Hexec Htop); step_state.
      }
      {
        inversion Hret as [next frames init top ret frs H']; subst ret frs.
        rewrite <- Hstk in H'; inversion H'; subst top frames init next.
        assert (Hmvr: In vr stk_frs). { subst; left; auto. }
        generalize (Hvalid_mid vr Hmvr); intros Hmid.
        inversion Hmid. subst p0 fr_id frames.
        rewrite H'; rewrite Hstk.
        assert (Hret_addr: exists (ret_pc: node), ReturnAddress i1 ret_pc).
        {
           destruct RETURN as [H''|[tr [dstr H'']]];
           inversion H''; exists next; constructor.
        }
        destruct Hret_addr as [ret_pc Hret_pc].
        assert (Hret_to_frame: ReturnToFrame p stk vr vrs i1 ret_pc).
        {
          subst stk stk_frs; apply return_to_frame with fr0 f0; auto.
        }
        destruct RETURN as [Hvoid|[tr [dstr Hcall]]].
        {
          generalize (eval_ret_void
            p stk h fr f pc value vrs i1 vr ret_pc
            Hexec Hret_to_frame Hvoid
          ); step_state.
        }
        {
          assert (Hrv: exists v, ReturnValue fr value tr v).
          {
            destruct value as [arg|] eqn:Evalue.
            {
              used_value f fr pc i arg arg_value Harg Harg_reg.
              destruct (TypeOfValue_dec arg_value tr).
              { exists arg_value; constructor; auto. }
              { exists VUnd; apply return_some_und with arg_value; auto. }
            }
            {
              exists VUnd; constructor.
            }
          }
          destruct Hrv as [ret_value Hret_value].
          generalize (eval_ret_value
            p stk h fr f pc value vrs i1 vr tr dstr ret_pc ret_value
            Hexec Hret_to_frame Hcall Hret_value
          ); step_state.
        }
      }
    }
    {
      used_value f fr pc i cond cond_value Hcond Hcond_reg.
      destruct (value_is_true_or_false cond_value) as [Et|Ef].
      {
        generalize (eval_jcc_true
          p stk h fr f pc cond bt bf cond_value
          Hexec Hcond Et
        ); step_state.
      }
      {
        generalize (eval_jcc_false
          p stk h fr f pc cond bt bf cond_value
          Hexec Hcond Ef
        ); step_state.
      }
    }
    {
      generalize (eval_jmp p stk h fr f pc target); step_state.
    }
    {
      generalize (eval_trap p stk h fr f pc Hexec); step_state.
    }
  }
  { inversion Hv. }
  { inversion Hv. }
  { inversion Hv. }
Qed.

