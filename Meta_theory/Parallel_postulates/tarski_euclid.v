Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section tarski_euclid.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma tarski_s_euclid_implies_euclid_5 :
  tarski_s_parallel_postulate ->
  euclid_5.
Proof.
intros HT P Q R S T U HPTQ HRTS HQUR HNC HCong1 HCong2.
destruct (构造对称点 R P) as [V HMid].
assert (Hc1 : Bet V P R) by (unfold 中点 in *; 分离合取式; Between).
assert (Hc2 : Bet Q U R) by (unfold BetS in *; 分离合取式; Between).
destruct (帕施公理 V Q R P U) as [W [HPWQ HUWV]]; Col; clear Hc1; clear Hc2.
assert (HPW : P <> W).
  {
  intro; treat_equalities.
  assert (P <> V).
    {
    intro; treat_equalities; apply HNC; unfold BetS in *; 分离合取式; ColR.
    }
  apply HNC; unfold BetS in *; 分离合取式; ColR.
  }
destruct (HT P V U W Q) as [X [Y [HPVX [HPUY HXQY]]]]; Between.
assert (HPar : 严格平行 Q S P R).
  {
  apply par_not_col_strict with P; Col.
  统计不重合点; unfold BetS in *; 分离合取式;
  apply l12_17 with T; [auto|split; Cong; Between..].
  }
assert (HTS : TS Q S P Y).
  {
  apply l9_8_2 with X.

    {
    统计不重合点.
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; 分离合取式; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; 分离合取式; Col).
    assert (~ Col X Q S).
      {
      apply par_strict_not_col_2 with P.
      apply par_strict_symmetry; apply par_strict_col_par_strict with R; Col.
      unfold BetS in *; 分离合取式; ColR.
      }
    repeat split; [..|exists Q]; Col.
    intro HCol.
    assert (Q = Y)
      by (apply l6_21_两线交点的唯一性 with Q S X Q; try (intro; treat_equalities); Col).
    treat_equalities.
    assert (Q = U).
      {
      apply 严格中间性的等价 in HPTQ; apply 严格中间性的等价 in HRTS; apply 严格中间性的等价 in HQUR;
      分离合取式; apply l6_21_两线交点的唯一性 with Q P R Q; Col.
      apply par_strict_not_col_2 with S; Par.
      }
    treat_equalities; unfold BetS in *; 分离合取式; Col.
    }

    {
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; 分离合取式; Col).
    assert (P <> V)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; 分离合取式; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; 分离合取式; Col).
    apply l12_6, par_strict_right_comm, par_strict_col_par_strict with R; ColR.
    }
  }
destruct HTS as [Hc1 [Hc2 [I [HCol HBet]]]];
clear Hc1; clear Hc2; exists I.
assert (HPUI : BetS P U I).
 {
  assert (P <> Y)  by (intro; treat_equalities; Col).
  assert (HPUI : Col P U I) by ColR.
  split.

    {
    elim HPUI; clear HPUI; intro HPUI; Col.
    elim HPUI; clear HPUI; intro HPUI; exfalso.

      {
      assert (HFalse : OS Q S P U).
        {
        apply one_side_transitivity with R; [Side|].
        apply 严格中间性的等价 in HPTQ; apply 严格中间性的等价 in HRTS; apply 严格中间性的等价 in HQUR;
        分离合取式; apply l9_19 with Q; Col.
        split; [Out|].
        apply par_strict_not_col_1 with P; Par.
        }
      apply (l9_19 Q S P U I) in HFalse; Col.
      分离合取式.
      apply (not_bet_and_out U I P); split; Out.
      }

      {
      assert (HFalse : OS P R I U).
        {
        apply one_side_transitivity with Q.
          {
          apply l12_6; apply par_strict_right_comm;
          apply par_strict_col_par_strict with S; Par; Col.
          intro; treat_equalities;
          unfold BetS in *; 分离合取式;
          apply HNC; ColR.
          }

          {
          assert (HPar':= HPar); apply par_strict_distinct in HPar.
          unfold BetS in *; 分离合取式; apply l9_19 with R; Col.
          split; [Out|apply par_strict_not_col_3 with S; Par].
          }
        }
        apply col_one_side_out in HFalse.
          apply (not_bet_and_out I P U); auto.
        Col.
      }
    }

    {
    apply par_strict_not_col_3 in HPar;
    apply 严格中间性的等价 in HPTQ; apply 严格中间性的等价 in HRTS; apply 严格中间性的等价 in HQUR; 分离合取式.
    split; intro; treat_equalities; [apply HPar; Col|].
    assert (Q = U).
      {
      apply l6_21_两线交点的唯一性 with S Q R Q; Col.
      intro; apply HNC; ColR.
      }
    treat_equalities; auto.
    }
 }
split; Col.
assert (HTS : TS Q R S I).
  {
  apply l9_8_2 with P.

    {
    unfold BetS in *; 分离合取式.
    repeat split; [..|exists U; split; Col].
    intro; apply HNC; ColR.
    intro; apply par_strict_not_col_4 in HPar; apply HPar; ColR.
    }

    {
    apply l12_6.
    apply par_not_col_strict with P; Col; [|intro; apply par_strict_not_col_3 in HPar; Col].
    apply 严格中间性的等价 in HPTQ; apply 严格中间性的等价 in HRTS; apply 严格中间性的等价 in HQUR; 分离合取式;
    apply l12_17 with T; try split; Cong; Between.
    }
  }
split.

  {
  elim HCol; intro HSQI; Between.
  assert (HFalse := HTS).
  apply l9_9 in HFalse; exfalso; apply HFalse.
  apply l9_19 with Q; Col.
  apply par_strict_not_col_4 in HPar; split; [|Col].
  统计不重合点; repeat split; auto; elim HSQI; Between.
  }

  {
  统计不重合点; split; auto.
  }
Qed.

End tarski_euclid.