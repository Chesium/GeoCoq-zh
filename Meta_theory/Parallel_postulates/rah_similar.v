Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_similar.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__similar : postulate_of_right_saccheri_quadrilaterals -> postulate_of_existence_of_similar_triangles.
Proof.
  intro rah.
  destruct 防降维公理_老版本 as [A [B0 [C]]].
  assert(~ Col A B0 C) by (unfold Col; assumption).
  destruct (l10_15 C A C B0) as [B []]; Col.
  assert(HNCol1 : ~ Col C A B) by (apply (one_side_not_col123 _ _ _ B0); Side).
  assert(Per A C B) by Perp.
  destruct (构造对称点 A B) as [B'].
  assert_diffs.
  assert(HNCol2 : ~ Col A C B') by (intro; apply HNCol1; ColR).
  assert(HNCol3 : ~ Col B B' C) by (intro; apply HNCol2; ColR).
  destruct (l8_18_过一点垂线之垂点的存在性 A C B') as [C' []]; auto.
  exists A, B, C, A, B', C'.
  assert(严格平行 B C B' C').
    apply (par_not_col_strict _ _ _ _ B'); Col; apply (l12_9 _ _ _ _ A C); Perp; Cop.
  assert(HNCol4 : ~ Col B C C') by (apply (par_strict_not_col_4 _ _ B'); auto).
  assert_diffs.
  assert(Bet A C C').
  { apply (col_two_sides_bet _ B); Col.
    apply l9_2.
    apply (l9_8_2 _ _ B').
      repeat split; Col; exists B; split; Col; Between.
      apply l12_6; Par.
  }
  assert(A <> C') by (intro; treat_equalities; auto).
  assert(Per B' C' A) by (apply L形垂直转直角1, (垂线共线点也构成垂直2 _ _ _ C); Col; Perp).
  assert(等角 B C A B' C' A) by (apply l11_16_直角相等; Perp).
  assert(等角 C A B C' A B').
    apply out2__conga; apply l6_6, bet_out; Between.
  split; Col; split.

    {
    intro.
    absurd(B = B'); auto.
    apply (between_cong A); Between.
    }

    {
    split; [|split; auto].
    apply (sams2_suma2__conga456 C A B _ _ _ _ _ _ B C A).
      和角.
      apply (conga2_sams__sams C' A B' A B' C'); 等角; 和角.
      apply t22_12__rah; Perp.
      apply (等角保持和角 C' A B' A B' C' B' C' A); 等角; apply t22_12__rah; auto.
    }
Qed.

End rah_similar.