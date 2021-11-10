Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section posidonius_postulate_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma posidonius_postulate__rah : posidonius_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
intro H.
assert (HF : exists A1 A2 B1 B2,
             Per A2 A1 B1 /\ Per A1 A2 B2 /\
             Cong A1 B1 A2 B2 /\ OS A1 A2 B1 B2 /\
             forall A3 B3,
               Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
               Cong A3 B3 A1 B1).
  {
  destruct H as [A1' [A2' [B1 [B2 [HNC [HNE [HCop HF]]]]]]].
  destruct (l8_18_过一点垂线之垂点的存在性 _ _ _ HNC) as [A1 [HC1 HPerp1]].
  统计不重合点.
  assert (HPar : 严格平行 A1' A2' B1 B2).
    {
    split; trivial.
    intros [I [HI1 HI2]].
    assert (HNE' : B1 <> I) by (intro; subst; apply HNC; Col).
    destruct (中点的存在性 B1 I) as [B3 HB3].
    assert (HNE'' : B1 <> B3) by (apply 严格中点组推论1 in HB3; spliter; auto).
    destruct (l8_18_过一点垂线之垂点的存在性 A1' A2' B3) as [A3 [HC4 HPerp3]].
      intro; apply HNC; ColR.
    assert (HCong : Cong A1 B1 A3 B3)
      by (apply HF; Perp; ColR).
    assert (HCong' : Cong B1 I B3 I).
      {
      assert (HNE''' : A3 <> I).
        {
        intro; assert (A1 = A3); treat_equalities.
          {
          apply l8_18_过一点垂线之垂点的唯一性 with A1' A2' B1; Col.
          apply 与垂线共线之线也为垂线1 with A3 B3; Col; Perp.
          }
        assert (HFalse : B3 <> B1) by auto.
        apply HFalse, between_cong with A1; [Between|Cong].
        }
      assert (HNE'''' : B3 <> I).
        {
        apply 严格中点组推论1 with B1; auto.
        }
      assert (HNE''''' : A1 <> I).
        {
        intro; treat_equalities; apply HNE'''.
        apply l8_18_过一点垂线之垂点的唯一性 with A1' A2' B3; Col; Perp.
          intro; apply HNC; ColR.
        apply 与垂线共线之线也为垂线3 with B1 A1; Col.
        }
      destruct (l11_50_2 B1 A1 I B3 A3 I); Cong.

        {
        intro H.
        apply HNE'''.
        apply 垂直的对称性 in HPerp1.
        destruct (垂直推出不共线 _ _ _ _ HPerp1);
        [apply l6_21_两线交点的唯一性 with A1 B1 A1' A2'|apply l6_21_两线交点的唯一性 with A1 B1 A2' A1']; ColR.
        }

        {
        apply out2__conga; [|Out].
        repeat split; auto.
        left; apply col_two_sides_bet with B3; [ColR|].
        assert (~ Col A3 B3 B1) by (intro; apply HNE'''; apply l6_21_两线交点的唯一性 with A1' A2' B1 B3; Col).
        apply l9_2, l9_8_2 with B1.

          {
          apply invert_two_sides, bet__ts; Between; Col.
          }

          {
          apply l12_6; apply par_not_col_strict with B1; Col.
          apply l12_9 with A1' A2'; Perp; Cop.
          exists I; left; split; Col.
          }
        }

        {
        统计不重合点; apply l11_16_直角相等; auto;
        apply L形垂直转直角1, 与垂线共线之线也为垂线1 with A1' A2'; Perp; Col.
        }
      }
    assert (HFalse : B3 <> B1) by auto.
    apply HFalse, between_cong with I; Between; Cong.
    }
  destruct (l8_18_过一点垂线之垂点的存在性 A1' A2' B2) as [A2 [HC2 HPerp2]].
    apply par_strict_not_col_4 with B1, HPar.
  assert (HNE' : A1 <> A2).
    {
    intro; treat_equalities.
    apply HPar; exists A1; split; Col.
    apply cop_perp2__col with A1' A2'; Perp.
    }
  apply 垂直的右交换性 in HPerp1.
  apply 垂直的右交换性 in HPerp2.
  exists A1, A2, B1, B2.
  repeat split; [apply 直角的对称性, L形垂直转直角2, 与垂线共线之线也为垂线1 with A1' A2'; auto..|apply HF; Col| |].
    apply (col2_os__os A1' A2'); Side.
  intros A3 B3 HC4 HC5 HPerp3.
  apply HF; Col; [ColR|].
  apply 与垂线共线之线也为垂线2 with A1 A2; auto; ColR.
  }
destruct HF as [A [D [B [C [HPer1 [HPer2 [HCong [HOS posid]]]]]]]].
assert (HSac : 萨凯里四边形 A B C D) by (repeat split; Perp; Cong).
apply (per_sac__rah A B C D); auto.
destruct (中点的存在性 B C) as [M HM].
destruct (中点的存在性 A D) as [N HN].
assert(HPerp := mid2_sac__perp_lower A B C D M N HSac HM HN).
统计不重合点.
assert(Hdiff := sac_distincts A B C D HSac).
spliter.
统计不重合点.
apply (t22_7__per _ _ _ D M N); Between.
  apply L形垂直转直角1, (垂线共线点也构成垂直2 _ _ _ D); Col; Perp.
apply 等长的左交换性, posid; Col; Perp.
Qed.

End posidonius_postulate_rah.