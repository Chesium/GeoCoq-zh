Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_bis_proclus.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma proclus_bis__proclus : alternative_proclus_postulate -> proclus_postulate.
Proof.
  intros proclus_bis A B C D P Q HPar HInter HNCol HCop.
  elim(共线的决定性 C D P).
    intro; exists P; Col.
  intro HNCol1.
  apply par_symmetry in HPar.
  apply (par_not_col_strict _ _ _ _ P) in HPar; auto.
  assert(HC0 := l8_18_过一点垂线之垂点的存在性 C D P).
  destruct HC0 as [C0 []]; auto.
  assert(HNCol2 : ~ Col C0 A B) by (apply (par_not_col C D); Col).
  统计不重合点.
  assert(HA0 : exists A0, Col A B A0 /\ ~ Col C0 P A0).
  { elim(共线的决定性 C0 P A).
    - intro.
      assert(~ Col C0 P B) by (intro; apply HNCol2; ColR).
      exists B.
      split; Col.

    - intro.
      exists A.
      split; Col.
  }
  destruct HA0 as [A0 []].
  assert(HA' := l10_15 C0 P P A0).
  destruct HA' as [A' []]; Col.
  统计不重合点.
  assert (共面 C D P A0) by (apply col2_cop__cop with A B; Col; Cop).
  elim(共线的决定性 A0 P A').
  - intro.
    apply (proclus_bis A0 P); Col; [|CopR|intro; apply HNCol; ColR].
    exists C0.
    exists P.
    split; Col.
    split; [|Perp].
    apply 垂直的右交换性.
    apply (垂线共线点也构成垂直2 _ _ _ A'); Perp; Col.

  - intro.
    exfalso.
    assert(HY := proclus_bis A' P C D P A0).
    destruct HY as [Y []]; Col.

      {
      exists C0; exists P; repeat split; Col; Perp.
      }

      {
      CopR.
      }

      {
      apply (par_not_col C D A B Y); ColR.
      }
Qed.

End proclus_bis_proclus.