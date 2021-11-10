Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.grad.
Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

Section Archimedes_cantor_dedekind.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Inductive cX A C (Alpha Beta : Tpoint -> Prop) : nat -> Tpoint -> Prop :=
| cX_init : cX A C Alpha Beta O A
| cX_same : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> 中点 M X Y ->
                Beta M -> cX A C Alpha Beta (S n) X
| cX_other : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> 中点 M X Y ->
                Alpha M -> cX A C Alpha Beta (S n) M
with cY A C (Alpha Beta : Tpoint -> Prop) : nat -> Tpoint -> Prop :=
| cY_init : cY A C Alpha Beta O C
| cY_same : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> 中点 M X Y ->
                Alpha M -> cY A C Alpha Beta (S n) Y
| cY_other : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> 中点 M X Y ->
                Beta M -> cY A C Alpha Beta (S n) M.

Scheme cX_cY_ind := Induction for cX Sort Prop
with cY_cX_ind := Induction for cY Sort Prop.

Combined Scheme cXY_ind from cX_cY_ind, cY_cX_ind.

Lemma archimedes_cantor__dedekind_variant : archimedes_axiom -> cantor_s_axiom -> dedekind_variant.
Proof.
  intros archi cantor Alpha Beta A C HA HC Hdis Hcut.
  assert (Hnab : forall P, Alpha P -> Beta P -> False) by (intros; eapply Hcut; eauto).
  assert (A <> C) by (apply Hcut; assumption).
  pose (Alpha' := cX A C Alpha Beta).
  pose (Beta' := cY A C Alpha Beta).
  assert (Haux : forall X Y M, Alpha X -> Out A Y C -> 中点 M X Y -> Out A M C).
  { intros X Y M HX HY HM.
    destruct (Hcut X C HX HC).
    apply l6_7 with Y; trivial.
    destruct (两点重合的决定性 A X).
      subst; 统计不重合点; apply l6_7 with Y; Out.
    apply out_bet_out_2 with X; [|Between].
    apply l6_7 with C; Out.
  }
  assert (Ha'a : forall n X, Alpha' n X -> Alpha X) by (induction 1; assumption).
  assert (Hb'b : forall n Y, Beta' n Y -> Beta Y) by (induction 1; assumption).
  assert (Hb'out : forall n Y, Beta' n Y -> Out A Y C) by (induction 1; eauto with out).
  destruct (cantor Alpha' Beta') as [B HB].
  { split.
    { induction n.
        exists A, C; split; constructor.
      destruct IHn as [X [Y [HX HY]]].
      destruct (中点的存在性 X Y) as [M].
      destruct (Hdis M); [apply (Haux X Y); eauto|..].
        exists M, Y; split; [apply cX_other with X Y|apply cY_same with X M]; auto.
        exists X, M; split; [apply cX_same with Y M|apply cY_other with X Y]; auto.
    }
    assert (Hunique : (forall n X, Alpha' n X -> forall X', Alpha' n X' -> X = X')
                   /\ (forall n Y, Beta' n Y -> forall Y', Beta' n Y' -> Y = Y')).
    { apply cXY_ind; [inversion_clear 1; reflexivity| | |inversion_clear 1; reflexivity|..];
       intros n X Y M HX HXind HY HYind HM1 HM2; inversion_clear 1;
       first [assert (X = X') by (apply HXind; assumption)|assert (X = X0) by (apply HXind; assumption)];
       first [assert (Y = Y') by (apply HYind; assumption)|assert (Y = Y0) by (apply HYind; assumption)];
       treat_equalities; try reflexivity; exfalso; eauto.
    }
    destruct Hunique as [Hunia Hunib].
    intros n X X' Y' Y HX HX' HY' HY.
    specialize (Ha'a n).
    specialize (Hb'b n).
    specialize (Hunia n).
    specialize (Hunib n).
    inversion_clear HX'; inversion_clear HY';
     assert (X = X0) by (apply Hunia; assumption); assert (Y = Y0) by (apply Hunib; assumption);
     first [assert (X = X1) by (apply Hunia; assumption)|assert (X = X') by (apply Hunia; assumption)];
     first [assert (Y = Y1) by (apply Hunib; assumption)|assert (Y = Y') by (apply Hunib; assumption)];
     treat_equalities; repeat split; Between; apply Hcut; auto.
  }

  exists B.
  assert (Hdecr : forall P, P <> B -> exists n Xn Yn, Alpha' n Xn /\ Beta' n Yn /\ Lt Xn Yn P B).
  { intros P HP.
    (** Archimedes' axiom is used here *)
    destruct (reach__ex_gradexp_lt A C P B) as [P' [HP' HLt]]; auto.
    cut (exists n X Y, Alpha' n X /\ Beta' n Y /\ Cong X Y A P').
    { intros [n [X [Y [HX [HY]]]]].
      exists n, X, Y; split; [|split]; trivial.
      apply (等长保持小于关系 A P' P B); Cong.
    }
    clear P HP HLt.
    rewrite gradexp__gradexpinv in HP'; induction HP'.
      exists O, A, B0; repeat split; [constructor..|Cong].
    destruct IHHP' as [n [X [Y [HX [HY HXY]]]]]; [assumption..|].
    exists (S n).
    destruct (中点的存在性 X Y) as [M HM].
    destruct (Hdis M); [apply (Haux X Y); eauto|..].
    - exists M, Y; repeat split; [apply cX_other with X Y|apply cY_same with X M|]; auto.
      apply 等长的左交换性, 两中点组全段等长则前半段等长 with X B0; [|split|Cong]; 中点.
    - exists X, M; repeat split; [apply cX_same with Y M|apply cY_other with X Y|]; auto.
      apply 两中点组全段等长则前半段等长 with Y B0; [|split|]; assumption.
  }
  intros X Y HX HY.
  apply (中间性的交换传递性1 A).
  - clear Y HY.
    destruct (l5_3 A X B C).
      apply Hcut; assumption.
      apply (HB O); constructor.
      assumption.
    destruct (两点重合的决定性 X B) as [|HXB]; [subst; Between|].
    destruct (两点重合的决定性 X A); [subst; Between|].
    exfalso.
    destruct (Hdecr X HXB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
    destruct (Hcut X Yn); [eauto..|].
    apply (小于推出反向不小于等于 Xn Yn X B HLt).
    apply 长度小于等于的传递性 with B Yn.
      apply 长度小于等于的左交换性, bet__le1213, (中间性的交换传递性1 A); assumption.
      apply bet__le2313, (HB n); assumption.

  - clear X HX.
    destruct (两点重合的决定性 A B) as [|HAB]; [subst; Between|].
    assert (HOut : Out A B Y).
    { apply l6_7 with C.
        apply bet_out, (HB O); [auto|constructor..].
      destruct (Hdecr A HAB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
      assert (Bet Xn B Yn) by (apply (HB n); assumption).
      assert (Xn <> A) by (intro; treat_equalities; apply (小于推出反向不小于等于 Xn Yn Xn B); Le).
      assert (Alpha Xn) by eauto.
      destruct (Hcut Xn Y); trivial.
      destruct (Hcut Xn C); trivial.
      apply l6_7 with Xn; Out.
    }
    destruct HOut as [_ [_ [|]]]; trivial.
    destruct (两点重合的决定性 Y B) as [|HYB]; [subst; Between|].
    exfalso.
    destruct (Hdecr Y HYB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
    destruct (Hcut Xn Y); [eauto..|].
    apply (小于推出反向不小于等于 Xn Yn Y B HLt).
    apply 长度小于等于的传递性 with Xn B.
      apply bet__le2313, (中间性的交换传递性1 A); assumption.
      apply bet__le1213, (HB n); assumption.
Qed.

End Archimedes_cantor_dedekind.