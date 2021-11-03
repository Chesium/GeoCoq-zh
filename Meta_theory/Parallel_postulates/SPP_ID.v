Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section SPP_ID.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma strong_parallel_postulate_implies_inter_dec :
  strong_parallel_postulate ->
  decidability_of_intersection.
Proof.
intros HSPP S Q P U.
elim (共线的决定性 P Q S); intro HPQS; [left; exists P; Col|].
elim (两点重合的决定性 P U); intro HPU; treat_equalities; [left; exists Q; Col|].
assert (H := midpoint_existence P Q); destruct H as [T [HPTQ HCong1]].
assert (H := 构造对称点 S T); destruct H as [R [HRTS HCong2]].
elim (共线的决定性 P R U); intro HPRU.

  {
  assert (HPar : 严格平行 Q S P U).
    {
    apply par_strict_col_par_strict with R; Col.
    apply par_not_col_strict with P; Col.
    apply l12_17 with T; [assert_diffs; auto|split; Between; Cong..].
    }
  destruct HPar as [H1 H].
  right; intro HI; apply H.
  destruct HI as [I [HCol1 HCol2]]; exists I; Col.
  }

  {
  elim (cop_dec P Q S U); intro HCop.

    {
    assert (H : BetS R T S); [|clear HRTS; rename H into HRTS].
      {
      split; Between.
      assert_cols.
      split; intro; treat_equalities; Col.
      }
     assert (H : BetS P T Q); [|clear HPTQ; rename H into HPTQ].
      {
      split; auto.
      split; intro; treat_equalities; Col.
      }
    assert (HI := HSPP P Q R S T U); destruct HI as [I [HCol1 HCol2]]; Cong;
    [|left; exists I; Col].
    unfold BetS in *; spliter.
    apply coplanar_trans_1 with S; [Col|exists T; right; right; split; Col|Cop].
    }

    {
    right; intros [I []].
    apply HCop.
    exists I; right; right; split; Col.
    }
  }
Qed.

End SPP_ID.