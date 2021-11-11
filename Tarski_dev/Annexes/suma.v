Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section Suma_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 和角推出不重合 : forall A B C D E F G H I, 和角 A B C D E F G H I ->
   A<>B /\ B<>C /\ D<>E /\ E<>F /\ G<>H /\ H<>I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J HJ].
  分离合取式.
  统计不重合点.
  repeat split; auto.
Qed.

Lemma 三角形内角和推出不重合 : forall A B C D E F, 三角形内角和 A B C D E F ->
  A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
  intros A B C D E F HTri.
  destruct HTri as [G [H [I [HSuma HSuma1]]]].
  apply 和角推出不重合 in HSuma.
  apply 和角推出不重合 in HSuma1.
  分离合取式; repeat split; auto.
Qed.

Lemma 和角的存在性 : forall A B C D E F, A<>B -> B<>C -> D<>E -> E<>F ->
   exists G H I, 和角 A B C D E F G H I.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  exists A.
  exists B.
  elim (共线的决定性 A B C).
  { intro HColB.
    destruct (给定角一边可作出共面等角 D E F C B A) as [J [HConga HCop]]; auto.
    统计不重合点.
    exists J.
    exists J.
    repeat (split; 等角); Cop.
    apply (col123__nos); Col.
  }
  intro HNColB.
  elim (共线的决定性 D E F).
  { intro HColE.
    elim (中间性的决定性 D E F).
    { intro HEBet.
      assert (HJ : exists J, 中点 B C J) by (apply 构造对称点).
      destruct HJ as [J HMid].
      统计不重合点.
      destruct HMid as [HJBet HCong].
      exists J, J.
      split.
        等角.
      split.
        apply col124__nos; Col.
      split; 等角; Cop.
    }
    intro HENBet.
    assert (HEOut : Out E D F) by (apply l6_4_2; auto).
    exists C.
    exists C.
    split.
    apply l11_21_b; [apply out_trivial|]; auto.
    split.
      apply col124__nos; Col.
    split; 等角; Cop.
  }
  intro HNColE.
  assert (HJ : exists J, 等角 D E F C B J /\ TS C B J A) by (apply 给定角一边可作出与给定点异侧一点构成等角_非平角; Col).
  destruct HJ as [J [HConga HTwo]].
  统计不重合点.
  exists J, J.
  repeat (split; 等角); [Side|Cop].
Qed.

(** Unicity of the sum. *)

Lemma 和角的唯一性 : forall A B C D E F G H I G' H' I',
   和角 A B C D E F G H I -> 和角 A B C D E F G' H' I' -> 等角 G H I G' H' I'.
Proof.
  intros A B C D E F G H I G' H' I' Hsuma Hsuma'.
  destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HCop]]]].
  destruct Hsuma' as [J' [HJ'1 [HJ'2 [HJ'3 HCop']]]].
  统计不重合点.
  assert (HcongaC : 等角 C B J C B J') by (apply (角等的传递性 C B J D E F); auto; apply 等角的对称性; auto).
  assert (HcongaA : 等角 A B J A B J').
  { elim (共线的决定性 A B C).
    { intro HColB.
      elim (中间性的决定性 A B C).
      { intro HBBet.
        apply (l11_13 C B J C B J'); Between.
      }
      intro HBNBet.
      assert (HBOut : Out B A C) by (apply l6_4_2; auto).
      apply (l11_10 C B J C B J'); try (apply out_trivial); auto.
    }
    intro HNColB.
    elim (共线的决定性 D E F).
    { intro HColE.
      apply out2__conga; [apply out_trivial|]; auto.
      elim (中间性的决定性 D E F).
      { intro HEBet.
        apply l6_3_2; repeat split; auto.
        exists C.
        split; auto; split; apply (零角的等角是零角 D E F); 等角.
      }
      intro HENBet.
      assert (HEOut : Out E D F) by (apply l6_4_2; auto).
      apply l6_7 with C; apply (l11_21_a D E F); 等角.
    }
    intro HNColE.
    apply (l11_22a A B J C A B J' C); auto.
    repeat (split; try (apply cop_nos__ts); 等角); Cop;
    apply (不共线三点构成的角的等角三点也不共线 D E F); 等角.
  }
  apply (角等的传递性 G H I A B J).
    等角.
  apply (角等的传递性 A B J A B J'); auto.
Qed.

(** Commutativity of the sum. *)

Lemma 和角的对称性 : forall A B C D E F G H I, 和角 A B C D E F G H I -> 和角 D E F A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J [HCongaBCJ [HNOne [HCongaABJ HCop]]]].
  统计不重合点.
  elim (共线的决定性 A B C).
  { intro HColB.
    elim (中间性的决定性 A B C).
    { intro HBBet.
      assert (HK : exists K, 中点 E F K) by (apply 构造对称点).
      destruct HK as [K [HKBet HCong]].
      统计不重合点.
      exists K.
      split; 等角.
      split.
        apply col124__nos; Col.
      split; Cop.
      apply (角等的传递性 D E K A B J); auto.
      apply 等角的左交换性; apply (l11_13 F E D C B J); Between; 等角.
    }
    intro HBNBet.
    assert (HBOut : Out B A C) by (apply l6_4_2; auto).
    exists F.
    split.
      apply l11_21_b; Out.
    split.
      apply col124__nos; Col.
    split; Cop.
    apply (角等的传递性 D E F A B J); auto.
    apply 等角的对称性.
    apply (l11_10 C B J D E F); try (apply out_trivial); auto.
  }

  intro HNColB.
  elim (共线的决定性 D E F).
  { intro HColE.
    assert (HK : exists K, 等角 A B C F E K) by (apply 给定角一边可作出等角; auto).
    destruct HK as [K HConga].
    统计不重合点.
    exists K.
    split; 等角.
    split.
      apply col123__nos; Col.
    split; Cop.
    apply (角等的传递性 D E K A B J); auto.
    elim (中间性的决定性 D E F).
    { intro HEBet.
      apply 等角的对称性; apply 等角的左交换性.
      apply (l11_13 C B A F); 等角; Between.
      apply (零角的等角是零角 D E F); 等角.
    }
    intro HENBet.
    assert (HEOut : Out E D F) by (apply l6_4_2; auto).
    apply 等角的对称性.
    apply (l11_10 A B C F E K); try (apply out_trivial); auto.
    apply (l11_21_a D E F); 等角.
  }

  intro HNColE.
  assert (HK : exists K, 等角 A B C F E K /\ TS F E K D) by (apply 给定角一边可作出与给定点异侧一点构成等角_非平角; Col).
  destruct HK as [K [HConga HTwo]].
  exists K.
  split; 等角.
  split.
    apply l9_9; apply l9_2; apply invert_two_sides; auto.
  split; Cop.
  apply (角等的传递性 D E K A B J); auto.
  apply 等角的对称性; apply 等角的右交换性.
  apply (l11_22a A B J C K E D F).
  split.
    apply cop_nos__ts; Col; Cop.
    intro; apply HNColE; apply (共线三点构成的角的等角三点也共线 C B J D E F); Col.
  split.
    apply invert_two_sides; auto.
  split; 等角.
Qed.

(** 等角 preserves 和角. *)

Lemma 等角保持和角性质 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   和角 A B C D E F G H I ->
   等角 A B C A' B' C' ->
   等角 D E F D' E' F' ->
   等角 G H I G' H' I' ->
   和角 A' B' C' D' E' F' G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' Hsuma HCongaB HCongaE HCongaH.
  assert (Hsuma' : 和角 D' E' F' A B C G' H' I').
  { apply 和角的对称性.
    destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HCop]]]].
    exists J.
    split.
    apply (角等的传递性 C B J D E F); auto.
    split; auto.
    split; auto.
    apply (角等的传递性 A B J G H I); auto.
  }
  apply 和角的对称性.
  destruct Hsuma' as [J [HJ1 [HJ2 [HJ3 HCop]]]].
  exists J.
  split.
    apply (角等的传递性 F' E' J A B C); auto.
  repeat (split; trivial).
Qed.

(** Out preserves 和角. *)
(* 无用 *)
Lemma out6_suma__suma : forall A B C D E F G H I A' C' D' F' G' I',
   和角 A B C D E F G H I -> Out B A A' -> Out B C C' -> Out E D D' ->
   Out E F F' -> Out H G G' -> Out H I I' -> 和角 A' B C' D' E F' G' H I'.
Proof.
  intros.
  统计不重合点.
  apply (等角保持和角性质 A B C D E F G H I); auto; apply 等角的对称性; apply out2__conga; assumption.
Qed.

(** ABC + 0 =  ABC (two lemmas) *)

Lemma 任何角加上零角大小不变 : forall A B C D E F G H I, 和角 A B C D E F G H I ->
   Out E D F -> 等角 A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  assert(A<>B/\B<>C/\D<>E/\E<>F/\G<>H/\H<>I) by (apply 和角推出不重合; auto).
  分离合取式.
  apply (和角的唯一性 A B C D E F A B C); auto.
  exists C.
  split.
  apply l11_21_b; try (apply out_trivial); auto.
  split.
    apply col124__nos; Col.
  split; Cop; 等角.
Qed.

Lemma 任何角加上零角还是本身 : forall A B C D E F, A <> B -> B <> C -> Out E D F -> 和角 A B C D E F A B C.
Proof.
  intros A B C D E F HAB HBC Hout.
  统计不重合点.
  destruct (和角的存在性 A B C D E F) as [G [H [I Hsuma]]]; auto.
  apply (等角保持和角性质 A B C D E F G H I); try (apply 同角相等); auto.
  apply 等角的对称性, 任何角加上零角大小不变 with D E F; auto.
Qed.

(** 0 + DEF = DEF (two lemmas) *)

Lemma 零角加上任何角后者大小不变 : forall A B C D E F G H I, 和角 A B C D E F G H I ->
   Out B A C -> 等角 D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  apply (任何角加上零角大小不变 D E F A B C); auto.
  apply 和角的对称性; auto.
Qed.

Lemma 零角加上任何角即为该角 : forall A B C D E F, D <> E -> E <> F -> Out B A C -> 和角 A B C D E F D E F.
Proof.
  intros; apply 和角的对称性, 任何角加上零角还是本身; auto.
Qed.

(** Some permutation properties:*)

Lemma 和角的左交换性 : forall A B C D E F G H I,
   和角 A B C D E F G H I -> 和角 C B A D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := 和角推出不重合 A B C D E F G H I Hsuma).
  分离合取式.
  apply (等角保持和角性质 A B C D E F G H I); 等角.
Qed.

Lemma 和角的中交换性 : forall A B C D E F G H I,
   和角 A B C D E F G H I -> 和角 A B C F E D G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := 和角推出不重合 A B C D E F G H I Hsuma).
  分离合取式.
  apply (等角保持和角性质 A B C D E F G H I); 等角.
Qed.

Lemma 和角的右交换性 : forall A B C D E F G H I,
   和角 A B C D E F G H I -> 和角 A B C D E F I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := 和角推出不重合 A B C D E F G H I Hsuma).
  分离合取式.
  apply (等角保持和角性质 A B C D E F G H I); 等角.
Qed.

Lemma 和角的交换性 : forall A B C D E F G H I,
   和角 A B C D E F G H I -> 和角 C B A F E D I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := 和角推出不重合 A B C D E F G H I Hsuma).
  分离合取式.
  apply (等角保持和角性质 A B C D E F G H I); 等角.
Qed.

(** Basic cases of sum *)

Lemma 异侧推出和角1 : forall A B C D, TS A B C D -> 和角 C B A A B D C B D.
Proof.
  intros A B C D HTS.
  exists D.
  统计不重合点.
  split; 等角.
  split; Side.
  split; 等角; Cop.
Qed.

Lemma 异侧推出和角2 : forall A B C D, TS A B C D -> 和角 C A B B A D C A D.
Proof.
  intros A B C D HTS.
  apply 异侧推出和角1, invert_two_sides, HTS.
Qed.

Lemma 在角内推出和角 : forall A B C P, 在角内 P A B C -> 和角 A B P P B C A B C.
Proof.
  intros A B C P HInangle.
  assert (Hcopy := HInangle); destruct Hcopy as [HAB [HCB [HPB _]]].
  exists C; repeat (split; 等角); Cop.
  elim (共线的决定性 B P A).
    apply col123__nos.
  intro HNCol.
  elim (共线的决定性 B P C).
    apply col124__nos.
  intro HNCol2.
  apply l9_9, invert_two_sides, 角端点在角内点与顶点连线两侧; Col.
Qed.

Lemma 中间性推出和角 : forall A B C P, A <> B -> B <> C -> P <> B -> Bet A B C ->
  和角 A B P P B C A B C.
Proof.
  intros A B C P HAB HBC HPB HBet.
  apply 在角内推出和角; Side.
Qed.


(** Characterization of 和角不大于平角 using 角度小于等于. *)

Lemma 用角度小于等于特征化和角不大于平角 : forall A B C D E F A', A<>B -> A'<>B -> Bet A B A' ->
   (和角不大于平角 A B C D E F <-> 角度小于等于 D E F C B A').
Proof.
  intros A B C D E F A' HAB HA'B HABA'.
  split.
  - intro Hint.
    destruct Hint as [_ [HUn [J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
    统计不重合点.
    destruct HUn as [HEOut | HBNBet].
    apply l11_31_1_任何角小于等于平角_Out表述; auto.
    elim (共线的决定性 A B C).
    { intro HColB.
      apply l11_31_1_任何角小于等于平角_Bet表述; auto.
      apply (bet_out_out_bet A B A'); try (apply out_trivial); auto.
      apply l6_4_2; auto.
    }
    intro HNColB.
    elim (共线的决定性 D E F).
    { intro HColE.
      elim (中间性的决定性 D E F).
      { intro HDEF.
        exfalso.
        apply HJ3.
        assert (HCBJ : Bet C B J) by (apply (零角的等角是零角 D E F); 等角).
        repeat split; Col.
          intro; apply HNColB; apply (共线的传递性1 B J C A); Col.
        exists B.
        split; Col; Between.
      }
      intro; apply l11_31_1_任何角小于等于平角_Out表述; auto; apply l6_4_2; auto.
    }
    intro HNColE.
    apply 角度小于等于的传递性 with C B J; [Lea|].
    exists J.
    split; 等角.
    apply l11_24_在角内的对称性; apply (在角内的特殊反向性 A); auto.
    assert (HTwo : TS B C A J).
    { apply cop_nos__ts; Cop.
      apply (不共线三点构成的角的等角三点也不共线 D E F); 等角.
    }
    destruct HTwo as [_ [_ [X [HXCol HXBet]]]].
    repeat split; auto.
    exists X.
    split; auto.
    elim (两点重合的决定性 B X); auto.
    intro HBX.
    right.
    apply (col_one_side_out B A X C); Col.
    apply invert_one_side.
    apply (one_side_transitivity A B X J).
    { apply out_one_side.
      left; intro; apply HNColB; apply (共线的传递性1 B X); Col.
      assert (HAX : A<>X) by (intro; treat_equalities; Col).
      apply bet_out; auto.
    }
    apply one_side_symmetry.
    apply cop_nts__os; Col; Cop.
    intro; apply HNColB; apply (共线的传递性1 B X); Col; apply (共线的传递性3 J); Col.
    intro; treat_equalities; auto.

  - intro Hlea.
    统计不重合点.
    split; auto.
    elim (共线的决定性 A B C).
    { intro HColB.
      elim (中间性的决定性 A B C).
      { intro HBBet.
        assert (HEOut : Out E D F).
        { assert (Out B C A') by (apply (l6_3_2); repeat split; auto; exists A; repeat split; Between).
          apply (l11_21_a C B A'); auto.
          apply 双角度偏序推等角; auto.
          apply l11_31_1_任何角小于等于平角_Out表述; auto.
        }
        split; try left; auto.
        exists C.
        split.
        apply l11_21_b; try (apply out_trivial); auto.
        split.
        apply col124__nos; Col.
        split; Cop.
        apply not_two_sides_id.
      }
      intro HBNBet.
      assert (HBOut : Out B A C) by (apply not_bet_out; auto).
      split.
      right; auto.
      assert (HJ : exists J : Tpoint, 等角 D E F C B J) by (apply (给定角一边可作出等角 D E F C B); auto).
      destruct HJ as [J HJ].
      exists J.
      split; 等角.
      split.
      apply col123__nos; Col.
      split; Cop.
      intro HTwo; destruct HTwo as [HBA [HNCol _]]; Col.
    }
    intro HNColB.
    assert (HNColB' : ~ Col A' B C) by (intro; apply HNColB; apply (共线的传递性1 B A'); Col).
    elim (共线的决定性 D E F).
    { intro HNColE.
      assert (HEOut : Out E D F).
      { apply not_bet_out; auto.
        intro HEBet.
        apply HNColB'.
        apply 中间性蕴含共线1; apply 中间性的对称性.
        apply (bet_lea__bet D E F); auto.
      }
      split.
      left; auto.
      exists C.
      split.
      apply l11_21_b; try (apply out_trivial); auto.
      split.
      apply col124__nos; Col.
      split; Cop.
      apply not_two_sides_id.
    }
    intro HNColE.
    split.
    right; intro; Col.
    assert (HJ : exists J, 等角 D E F C B J /\ TS C B J A) by (apply 给定角一边可作出与给定点异侧一点构成等角_非平角; Col).
    destruct HJ as [J [HCongaJ HTwo]].
    统计不重合点.
    exists J.
    split; 等角.
    split.
    apply l9_9; apply l9_2; apply invert_two_sides; auto.
    elim (共线的决定性 A B J).
    { intro HColJ.
      split; Cop.
      intro HTwo'.
      destruct HTwo' as [HBA [HNColC [HNColJ _]]].
      Col.
    }
    intro HNColJ.
    assert (HF : ~ TS A' B C J).
    { apply l9_9_bis.
      apply one_side_symmetry.
      apply (角内点和一端点在角另一边同侧); auto.
      intro; apply HNColJ; apply (共线的传递性1 B A'); Col.
      apply l11_24_在角内的对称性.
      destruct Hlea as [K [H在角内 HCongaK]].
      apply (conga_preserves_in_angle C B A' K C B A' J); 等角.
      apply (角等的传递性 C B K D E F); 等角.
      exists A; split; auto.
      apply l9_2, invert_two_sides, bet__ts; Col.
    }
    split; Cop.
    intro; apply HF.
    apply (col_preserves_two_sides A B); Col.
Qed.

Lemma 和角不大于平角推出不重合 : forall A B C D E F, 和角不大于平角 A B C D E F ->
   A<>B /\ B<>C /\ D<>E /\ E<>F.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HP1 [HP2 [J HJ]]].
  分离合取式.
  统计不重合点.
  repeat split; auto.
Qed.

Lemma 和角不大于平角的对称性 : forall A B C D E F, 和角不大于平角 A B C D E F ->
   和角不大于平角 D E F A B C.
Proof.
  intros A B C D E F Hisi.
  assert(A<>B/\B<>C/\D<>E/\E<>F) by (apply 和角不大于平角推出不重合; auto).
  分离合取式.
  assert(HD' : exists D', 中点 E D D') by apply 构造对称点.
  destruct HD' as [D'].
  assert(HA' : exists A', 中点 B A A') by apply 构造对称点.
  destruct HA' as [A'].
  统计不重合点.
  apply (用角度小于等于特征化和角不大于平角 D E F A B C D'); Between.
  apply 角度小于等于的右交换性.
  apply (l11_36_双补角组中的角度偏序 D _ _ A'); Between.
  apply 角度小于等于的右交换性.
  apply (用角度小于等于特征化和角不大于平角 A); Between.
Qed.

Lemma 和角不大于平角的右交换性 : forall A B C D E F, 和角不大于平角 A B C D E F ->
   和角不大于平角 A B C F E D.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HAB [HUn [J [HJ1 [HJ2 HJ3]]]]].
  split; auto.
  split.
  { destruct HUn.
    left; apply l6_6; auto.
    right; auto.
  }
  exists J.
  split.
  apply 等角的右交换性; auto.
  split; auto.
Qed.

Lemma 和角不大于平角的左交换性 : forall A B C D E F, 和角不大于平角 A B C D E F ->
   和角不大于平角 C B A D E F.
Proof.
  intros.
  apply 和角不大于平角的对称性.
  apply 和角不大于平角的右交换性.
  apply 和角不大于平角的对称性.
  assumption.
Qed.

Lemma 和角不大于平角的交换性 : forall A B C D E F, 和角不大于平角 A B C D E F ->
   和角不大于平角 C B A F E D.
Proof.
  intros.
  apply 和角不大于平角的左交换性.
  apply 和角不大于平角的右交换性.
  assumption.
Qed.

Lemma 等角保持和角不大于平角性质 : forall A B C D E F A' B' C' D' E' F',
   等角 A B C A' B' C' -> 等角 D E F D' E' F' ->
   和角不大于平角 A B C D E F -> 和角不大于平角 A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HCongaB HCongaE Hisi.
  assert(HA0 : exists A0, 中点 B A A0) by apply 构造对称点.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, 中点 B' A' A'0) by apply 构造对称点.
  destruct HA'0 as [A'0].
  统计不重合点.
  apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A'0); Between.
  apply (l11_30_等角保持小于等于 D E F C B A0); try (apply (用角度小于等于特征化和角不大于平角 A)); Between.
  apply 等角的交换性.
  apply (l11_13 A B C A'); Between.
Qed.

Lemma OutEDF推和角不大于平角 : forall A B C D E F, A <> B -> B <> C -> Out E D F -> 和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F HAB HBC HOut.
  destruct (由一点往一方向构造等长线段 A B A B) as [A' [HBet HCong]].
  统计不重合点.
  apply 用角度小于等于特征化和角不大于平角 with A'; auto.
  apply l11_31_1_任何角小于等于平角_Out表述; auto.
Qed.

Lemma OutBAC推和角不大于平角 : forall A B C D E F, D <> E -> E <> F -> Out B A C -> 和角不大于平角 A B C D E F.
Proof.
  intros; apply 和角不大于平角的对称性, OutEDF推和角不大于平角; trivial.
Qed.

Lemma 和角为平角推和角不大于平角 : forall A B C D E F G H I, 和角 A B C D E F G H I -> Bet G H I ->
  和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F G H I HSuma HBet.
  destruct HSuma as [A' [HConga1 [HNOS [HCop HConga2]]]].
  apply (零角的等角是零角 _ _ _ A B A') in HBet; 等角.
  统计不重合点.
  repeat split; auto.
  - elim (中间性的决定性 A B C).
    { intro HBet'; left.
      apply (l11_21_a C B A'); trivial.
      apply l6_2 with A; Between.
    }
    intro HNBet; auto.
  - exists A'; repeat (split; trivial).
    intros [_ [HNCol _]]; apply HNCol; Col.
Qed.

Lemma 邻补角之和不大于平角 : forall A B C P, A <> B -> B <> C -> P <> B -> Bet A B C -> 和角不大于平角 A B P P B C.
Proof.
  intros A B C P HAB HBC HPB HBet.
  apply 和角为平角推和角不大于平角 with A B C.
    apply 中间性推出和角; auto.
    assumption.
Qed.

Lemma 补角之和不大于平角 : forall A B C D E F, 互为补角 A B C D E F -> 和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F [HAB [A' [HBet HCong]]].
  统计不重合点.
  apply (等角保持和角不大于平角性质 A B C C B A'); 等角.
  apply 邻补角之和不大于平角; auto.
Qed.
(*
    B
   /|\
  /*|*\
 /  |  \
A---+---C
    |
    P
*)
Lemma 同侧异侧推和角不大于平角 : forall A B C P, TS B P A C -> OS A B P C -> 和角不大于平角 A B P P B C.
Proof.
  intros A B C P HTS HOS.
  统计不重合点.
  repeat split; auto.
    right; intro; apply (one_side_not_col123 A B P C); Col.
  exists C.
  split; 等角.
  repeat split; Side; Cop.
Qed.
(*
    B
   /|\
  /*|*\
 /  |  \
A---+---C
    |
    P
*)
Lemma 双同侧推和角不大于平角 : forall A B C P, OS A B P C -> OS C B P A -> 和角不大于平角 A B P P B C.
Proof.
  intros A B C P HOS1 HOS2.
  apply 同侧异侧推和角不大于平角; trivial.
  apply l9_31; Side.
Qed.
(* 半无用 *)
Lemma 在角内推和角不大于平角 : forall A B C P, 在角内 P A B C -> 和角不大于平角 A B P P B C.
Proof.
  intros A B C P HIn.
  统计不重合点.
  destruct (or_bet_out A B C) as [HBet|[HOut|HNCol]].
    apply 邻补角之和不大于平角; auto.
    apply OutBAC推和角不大于平角; auto; apply in_angle_out with C; assumption.
  assert (~ Bet A B C) by (intro; apply HNCol; Col).
  destruct (共线的决定性 B A P).
    apply OutBAC推和角不大于平角; auto; apply col_in_angle_out with C; assumption.
  destruct (共线的决定性 B C P).
    apply OutEDF推和角不大于平角; auto; apply l6_6, col_in_angle_out with A; Between; apply l11_24_在角内的对称性, HIn.
  apply 同侧异侧推和角不大于平角.
    apply invert_two_sides, 角端点在角内点与顶点连线两侧; assumption.
    apply 角内点和一端点在角另一边同侧; assumption.
Qed.

End Suma_1.


Ltac 统计不重合点 :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := 不共线则不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := 非中间性则任两点不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_AB不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BA不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BC不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_CB不等推AC不等 A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D (不重合的对称性 B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于推出不重合 A B C D H);clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B (不重合的对称性 B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B (不重合的对称性 A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B (不重合的对称性 B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H (不重合的对称性 B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H (不重合的对称性 C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直推出不重合 A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:垂直于 ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直于推出不重合 X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 角等推AB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= 角等推CB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= 角等推DE不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= 角等推FE不重合 A B C A' B' C' H);clean_reap_hyps

      | H:(垂直平面于 ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:和角 ?A ?B ?C ?D ?E ?F ?G ?I ?J |- _ =>
      let h := fresh in
      not_exist_hyp6 A B B C D E E F G I I J;
      assert (h := 和角推出不重合 A B C D E F G I J H);decompose [and] h;clear h;clean_reap_hyps
      | H: 三角形内角和 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp5 A B B C A C D E E F;
      assert (h := 三角形内角和推出不重合 A B C D E F H);decompose [and] h;clear h; clean_reap_hyps
      | H:和角不大于平角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 和角不大于平角推出不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(在角内 ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := 在角内推出点不重合 A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于等于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于等于推出点不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于推不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为锐角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为锐角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为钝角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为钝角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:互为补角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
 end.

Hint Resolve 和角的对称性 和角的左交换性 和角的中交换性 和角的右交换性
             和角的交换性 异侧推出和角1 异侧推出和角2 在角内推出和角 中间性推出和角
             和角不大于平角的右交换性 和角不大于平角的交换性 和角不大于平角的左交换性 和角不大于平角的对称性
             OutBAC推和角不大于平角 OutEDF推和角不大于平角 邻补角之和不大于平角 补角之和不大于平角 在角内推和角不大于平角 : suma.

Ltac 和角 := auto with suma.

Section Suma_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** ABC <= ABC + DEF. *)

Lemma 原角小于等于和角 : forall A B C D E F G H I, 和角 A B C D E F G H I ->
   和角不大于平角 A B C D E F -> 角度小于等于 A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  统计不重合点.
  分离合取式.
  elim(共线的决定性 A B C).
  { intro HColB.
    elim(中间性的决定性 A B C).
    { intro HBBet.
      destruct Hisi as [_[[HEout|]]]; try solve[exfalso; auto].
      apply 等角小于等于自己.
      apply (任何角加上零角大小不变 _ _ _ D E F); auto.
    }
    intro HBout.
    apply l11_31_1_任何角小于等于平角_Out表述; auto.
    apply not_bet_out; auto.
  }
  intro HNColB.
  elim(共线的决定性 D E F).
  { intro HColE.
    elim(中间性的决定性 D E F).
    { intro HEBet.
      apply 和角不大于平角的对称性 in Hisi.
      destruct Hisi as [_[[HBout|]]]; try solve[exfalso; auto].
      apply l11_31_1_任何角小于等于平角_Out表述; auto.
    }
    intro HEout.
    apply 等角小于等于自己.
    apply (任何角加上零角大小不变 _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(共线的决定性 G H I).
  { intro HColH.
    elim(中间性的决定性 G H I).
      apply l11_31_1_任何角小于等于平角_Bet表述; auto.
    intro HHout.
    apply not_bet_out in HHout; auto.
    exfalso.
    destruct Hisi as [_ [HUn _]].
    destruct HUn as [HEout | HBNBet].
      apply HNColE; apply 等价共线BAC; apply out_col; auto.
    destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
    apply HJ2.
    apply 等角的对称性 in HJ4.
    apply l11_21_a in HJ4; auto.
    apply (l9_19 _ _ _ _ B); try split; Col.
  }
  intro HNColH.
  destruct Hisi as [_ [_ [J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
  统计不重合点.
  assert(HNColJ : ~ Col J B C).
  { intro HColJ.
    apply HNColE.
    apply (共线三点构成的角的等角三点也共线 J B C); 等角.
  }
  assert(HCongaJ : 等角 A B J G H I).
  { apply (和角的唯一性 A B C D E F); auto.
    exists J.
    repeat (split; 等角).
  }
  assert(HNColJ2 : ~ Col J B A).
  { intro HColJ.
    apply HNColH.
    apply (共线三点构成的角的等角三点也共线 A B J); Col.
  }
  apply (l11_30_等角保持小于等于 A B C A B J); 等角.
  exists C.
  split; 等角.
  apply cop_nos__ts in HJ2; Cop.
  destruct HJ2 as [a [b [X [HColX HXBet]]]].
  repeat split; auto.
  exists X.
  split; auto.
  right.
  assert(HNColX : ~Col X A B).
  { intro.
    apply HNColJ2.
    apply 等价共线BCA; apply (共线的传递性2 A X); Col.
    intro; subst X; Col.
  }
  统计不重合点.
  apply (col_one_side_out _ A); Col.
  apply invert_one_side.
  apply (one_side_transitivity _ _ _ J).
  - apply out_one_side.
    left; Col.
    apply bet_out; auto.
  - apply one_side_symmetry.
    apply cop_nts__os; Col; Cop.
Qed.

(** DEF <= ABC + DEF. *)

Lemma 加角小于等于和角 : forall A B C D E F G H I, 和角 A B C D E F G H I ->
   和角不大于平角 A B C D E F -> 角度小于等于 D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  apply (原角小于等于和角 D E F A B C G H I); 和角.
Qed.

(** 角度小于等于 preserves 和角不大于平角. *)

Lemma 角度小于等于保持和角不大于平角性质 : forall A B C D E F A' B' C' D' E' F',
   和角不大于平角 A' B' C' D' E' F' -> 角度小于等于 A B C A' B' C' -> 角度小于等于 D E F D' E' F' ->
   和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F A' B' C' D' E' F' Hisi HleaB HleaE.
  assert(HA0 : exists A0, 中点 B A A0) by apply 构造对称点.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, 中点 B' A' A'0) by apply 构造对称点.
  destruct HA'0 as [A'0].
  统计不重合点.
  apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A0); Between.
  apply (角度小于等于的传递性 D E F D' E' F'); auto.
  apply (角度小于等于的传递性 D' E' F' C' B' A'0).
  - apply (用角度小于等于特征化和角不大于平角 A'); Between.
  - apply 角度小于等于的交换性.
    apply (l11_36_双补角组中的角度偏序 A B C A'); Between.
Qed.

Lemma 和角保持角度小于等于性质_右 : forall A B C D E F G H I D' E' F' G' H' I',
   角度小于等于 D E F D' E' F' -> 和角不大于平角 A B C D' E' F' -> 和角 A B C D E F G H I ->
   和角 A B C D' E' F' G' H' I' -> 角度小于等于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I D' E' F' G' H' I' Hlea Hisi' Hsuma Hsuma'.
  统计不重合点.
  elim(out_dec E' D' F').
  { intro HE'out.
    apply 等角小于等于自己.
    apply (角等的传递性 _ _ _ A B C).
    apply 等角的对称性; apply (任何角加上零角大小不变 _ _ _ D E F); auto; apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (任何角加上零角大小不变 _ _ _ D' E' F'); auto.
  }
  intro HE'Nout.
  elim(共线的决定性 A B C).
  { intro HColB.
    destruct Hisi' as [_ [[HE'out|HBNBet]_]].
    exfalso; auto.
    apply not_bet_out in HColB; auto.
    apply (l11_30_等角保持小于等于 D E F D' E' F'); auto; apply (零角加上任何角后者大小不变 A B C); auto.
  }
  intro HNColB.
  elim(共线的决定性 D' E' F').
  { intro HColE'.
    apply 和角不大于平角的对称性 in Hisi'.
    destruct Hisi' as [_ [[HBout|HE'NBet]_]]; exfalso.
    apply HNColB; Col.
    apply not_bet_out in HColE'; auto.
  }
  intro HNColE'.
  clear HE'Nout.
  elim(共线的决定性 D E F).
  { intro HColE.
    assert(~ Bet D E F) by (intro; apply HNColE'; apply 中间性蕴含共线1; apply (bet_lea__bet D E F); auto).
    apply (l11_30_等角保持小于等于 A B C G' H' I'); try (apply 同角相等); auto.
    apply (原角小于等于和角 _ _ _ D' E' F'); auto.
    apply (任何角加上零角大小不变 _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(共线的决定性 G' H' I').
  { intro HColH'.
    elim(中间性的决定性 G' H' I').
    apply l11_31_1_任何角小于等于平角_Bet表述; auto.
    intro HH'out.
    apply not_bet_out in HH'out; auto.
    exfalso.
    apply HNColB.
    apply 等价共线BAC.
    apply out_col.
    apply (out_lea__out _ _ _ G' H' I'); auto.
    apply (原角小于等于和角 _ _ _ D' E' F'); auto.
  }
  intro HNColH'.
  destruct Hisi' as [_[_[F'1]]].
  分离合取式.
  apply(l11_30_等角保持小于等于 _ _ _ _ _ _ D E F C B F'1) in Hlea; 等角.
  destruct Hlea as [F1].
  分离合取式.
  统计不重合点.
  assert(等角 A B F'1 G' H' I').
    apply (和角的唯一性 A B C D' E' F'); auto; exists F'1; repeat (split; 等角).
  assert(~ Col A B F'1) by (apply (不共线三点构成的角的等角三点也不共线 G' H' I'); 等角).
  assert(~ Col C B F'1) by (apply (不共线三点构成的角的等角三点也不共线 D' E' F'); 等角).
  apply (l11_30_等角保持小于等于 A B F1 A B F'1); auto.
  - exists F1.
    split; 等角.
    apply l11_24_在角内的对称性.
    apply (在角内的传递性 _ _ _ C).
    apply l11_24_在角内的对称性; auto.
    assert(Hts : TS B C A F'1) by (apply cop_nos__ts; Col; Cop).
    destruct Hts as [_ [_ [X]]].
    分离合取式.
    repeat split; auto.
    exists X.
    split; Between.
    right.
    apply (col_one_side_out _ A); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ F'1); auto.
      apply out_one_side; Col; apply bet_out; auto; intro; subst A; Col.
    apply one_side_symmetry; apply cop_nts__os; Col.

  - apply (和角的唯一性 A B C D E F); auto.
    assert (TS B C F1 A).
    { apply (l9_8_2 _ _ F'1).
        apply l9_2; apply cop_nos__ts; Col; Cop.
      apply invert_one_side; apply one_side_symmetry.
      apply 角内点和一端点在角另一边同侧; Col.
      apply 共线否定排列BAC; apply (不共线三点构成的角的等角三点也不共线 D E F); auto.
    }
    exists F1.
    repeat (split; 等角); Side; Cop.
Qed.

Lemma 和角保持角度小于等于性质_左 : forall A B C D E F G H I A' B' C' G' H' I',
   角度小于等于 A B C A' B' C' -> 和角不大于平角 A' B' C' D E F -> 和角 A B C D E F G H I ->
   和角 A' B' C' D E F G' H' I' -> 角度小于等于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C'.
  intros.
  apply (和角保持角度小于等于性质_右 D E F A B C _ _ _ A' B' C'); 和角.
Qed.

(** 和角 preserves 角度小于等于. *)

Lemma 和角保持角度小于等于性质 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 A B C A' B' C' -> 角度小于等于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于等于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HleaB HleaD Hisi' Hsuma Hsuma'.
  统计不重合点.
  assert(Haux := 和角的存在性 A B C D' E' F').
  destruct Haux as [G'' [H'' [I'']]]; auto.
  apply (角度小于等于的传递性 _ _ _ G'' H'' I'').
  - apply (和角保持角度小于等于性质_右 A B C D E F _ _ _ D' E' F'); auto.
    apply (角度小于等于保持和角不大于平角性质 _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  - apply (和角保持角度小于等于性质_左 A B C D' E' F' _ _ _ A' B' C'); auto.
Qed.

(** Unicity of the difference of angles. *)

Lemma 和角推加角唯一性 : forall A B C D E F D' E' F' G H I,
   和角不大于平角 A B C D E F -> 和角不大于平角 A B C D' E' F' ->
   和角 A B C D E F G H I -> 和角 A B C D' E' F' G H I ->
   等角 D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' G H I Hisi Hisi' Hsuma Hsuma'.
  统计不重合点.
  elim(共线的决定性 A B C).
  { intro HColB.
    elim(中间性的决定性 A B C).
    { intro HBBet.
      destruct Hisi as [_ [[HEout|]_]]; try solve [exfalso; Between].
      destruct Hisi' as [_ [[HE'out|]_]]; try solve [exfalso; Between].
      apply l11_21_b; auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    apply (角等的传递性 _ _ _ G H I).
    - apply (零角加上任何角后者大小不变 A B C); auto.
    - apply 等角的对称性.
      apply (零角加上任何角后者大小不变 A B C); auto.
  }
  intro HNColB.
  destruct Hisi as [_[_[J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
  destruct Hisi' as [_[_[J' [HJ'1 [HJ'2 [HJ'3 HJ'4]]]]]].
  统计不重合点.
  apply (角等的传递性 _ _ _ C B J); try solve [apply 等角的对称性; auto].
  apply (角等的传递性 _ _ _ C B J'); auto.
  assert(等角 A B J A B J').
  { apply (角等的传递性 _ _ _ G H I).
      apply (和角的唯一性 A B C D E F); auto; exists J; repeat (split; 等角).
    apply (和角的唯一性 A B C D' E' F'); auto; exists J'; repeat (split; 等角).
  }
  assert(HJJ' : Out B J J' \/ TS A B J J').
    apply conga_cop__or_out_ts; auto; apply coplanar_trans_1 with C; Cop; Col.
  destruct HJJ' as [Hout|Hts].
  - apply out2__conga; Out.
  - exfalso.
    apply HJ'3.
    apply (l9_8_2 _ _ J); auto.
    apply one_side_symmetry.
    apply cop_nts__os; Col.
    apply two_sides_not_col in Hts; Col.
Qed.

(** Unicity of the difference on the left. *)

Lemma 和角推原角唯一性 : forall A B C A' B' C' D E F G H I,
   和角不大于平角 A B C D E F -> 和角不大于平角 A' B' C' D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D E F G H I ->
   等角 A B C A' B' C'.
Proof.
  intros A B C A' B' C' D E F G H I Hisi Hisi' Hsuma Hsuma'.
  apply (和角推加角唯一性 D E F _ _ _ _ _ _ G H I); 和角.
Qed.
(* (∠ABC+∠DEF)+∠GHI = ∠ABC+(∠DEF+∠GHI) = ∠KLM
   =∠A'B'C'                  =∠D'E'F'     
*)
Lemma 和角结合律1 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   和角 A' B' C' G H I K L M -> 和角 A B C D' E' F' K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F' HisiBE HisiEH HsBE HsEH HsB'H.
  assert(HA0 : exists A0, 中点 B A A0) by apply 构造对称点.
  destruct HA0 as [A0 []].
  assert(HD0 : exists D0, 中点 E D D0) by apply 构造对称点.
  destruct HD0 as [D0 []].
  统计不重合点.
  elim(共线的决定性 A B C).
  { intro HColB.
    elim(中间性的决定性 A B C).
    { intro HBBet.
      destruct HisiBE as [_ [[HEout | HBNBet] HJ]]; try solve [exfalso; Between].
      apply (等角保持和角性质 A' B' C' G H I K L M); try (apply 同角相等); auto.
      apply 等角的对称性; apply (任何角加上零角大小不变 _ _ _ D E F); auto.
      apply (零角加上任何角后者大小不变 D E F); auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    assert(Hexsuma : exists K0 L0 M0, 和角 A B C D' E' F' K0 L0 M0) by (apply 和角的存在性; auto).
    destruct Hexsuma as [K0 [L0 [M0]]].
    apply (等角保持和角性质 A B C D' E' F' K0 L0 M0); try (apply 同角相等); auto.
    apply (角等的传递性 _ _ _ D' E' F').
    apply 等角的对称性; apply (零角加上任何角后者大小不变 A B C); auto.
    apply (和角的唯一性 D E F G H I); auto.
    apply (等角保持和角性质 A' B' C' G H I K L M); try (apply 同角相等); auto.
    apply 等角的对称性.
    apply (零角加上任何角后者大小不变 A B C); auto.
  }
  intro HNColB.
  assert(~ Col C B A0) by (intro; apply HNColB; apply (共线的传递性1 _ A0); Col).
  elim(共线的决定性 D E F).
  { intro HColE.
    elim(中间性的决定性 D E F).
    { intro HEBet.
      destruct HisiEH as [_ [[HHout | HENBet] HJ]]; try solve [exfalso; Between].
      apply (等角保持和角性质 A B C D E F A' B' C'); try (apply 同角相等); try (apply (任何角加上零角大小不变 _ _ _ G H I)); auto.
    }
    intro HEout.
    apply not_bet_out in HEout; auto.
    apply (等角保持和角性质 A' B' C' G H I K L M); try (apply 同角相等); auto.
    apply 等角的对称性; apply (任何角加上零角大小不变 _ _ _ D E F); auto.
    apply (零角加上任何角后者大小不变 D E F); auto.
  }
  intro HNColE.
  assert(~ Col F E D0) by (intro; apply HNColE; apply (共线的传递性1 _ D0); Col).
  elim(共线的决定性 G H I).
  { intro HColH.
    elim(中间性的决定性 G H I).
    { intro HHBet.
      apply 和角不大于平角的对称性 in HisiEH.
      destruct HisiEH as [_ [[HEout | HHNBet] HJ]]; try solve [exfalso; Between].
      exfalso.
      apply HNColE.
      apply 等价共线BAC.
      apply out_col; auto.
    }
    intro HHout.
    apply not_bet_out in HHout; auto.
    apply (等角保持和角性质 A B C D E F A' B' C'); try (apply 同角相等); try (apply (任何角加上零角大小不变 _ _ _ G H I)); auto.
  }
  intro HNColH.
  assert(~ OS B C A A0).
  { apply l9_9.
    repeat split; Col.
    exists B.
    split; Col; Between.
  }
  assert(TS E F D D0) by (apply bet__ts; Col).
  elim(共线的决定性 A' B' C').
  { intro HColB'.
    elim(中间性的决定性 A' B' C').
    { intro HB'Bet.
      elim(共线的决定性 D' E' F').
      { intro HColE'.
        elim(中间性的决定性 D' E' F').
        { intro HE'Bet.
          apply 和角的对称性.
          apply (等角保持和角性质 A' B' C' G H I K L M); [等角..| |等角].
          apply 等角的对称性.
          apply (角等的传递性 _ _ _ D0 E F).
          - apply (和角推原角唯一性 _ _ _ _ _ _ D E F A' B' C'); [和角..|].
            apply 和角的对称性.
            exists D0.
            repeat (split; 等角); Side; Cop.
          - apply (和角推加角唯一性 D E F _ _ _ _ _ _ D' E' F'); auto.
              和角.
            exists D0.
            repeat (split; 等角); Side; Cop.
        }
        intro HE'out.
        apply not_bet_out in HE'out; auto.
        exfalso.
        apply HNColE.
        apply 等价共线BAC.
        apply out_col.
        apply (out_lea__out _ _ _ D' E' F'); auto.
        apply (原角小于等于和角 _ _ _ G H I); auto.
      }
      intro HNColE'.
      assert(等角 D E F C B A0).
      { apply (和角推加角唯一性 A B C _ _ _ _ _ _ A' B' C'); auto.
          和角.
        apply (等角保持和角性质 A B C C B A0 A B A0); [和角|等角..].
      }
      assert(HJ : 和角不大于平角 C B A0 G H I) by (apply (等角保持和角不大于平角性质 D E F G H I); try (apply 同角相等); auto).
      destruct HJ as [_ [_ [J]]].
      destruct HisiEH as [_ [_ [F1]]].
      分离合取式.
      统计不重合点.
      assert(等角 C B J D' E' F').
      { apply (角等的传递性 _ _ _ D E F1); auto.
        - apply (l11_22 _ _ _ A0 _ _ _ F); auto.
          split.
            left; split; apply cop_nos__ts; Cop; apply (不共线三点构成的角的等角三点也不共线 G H I); 等角.
          split.
            等角.
          apply (角等的传递性 _ _ _ G H I); 等角.

        - apply (和角的唯一性 D E F G H I); auto.
          exists F1.
          repeat (split; 等角).
      }
      apply (等角保持和角性质 A B C D' E' F' A B J); [|apply 同角相等; auto..|].
      { exists J.
        assert (TS C B J A).
        { apply (l9_8_2 _ _ A0).
            apply l9_2, invert_two_sides, bet__ts; Col.
          apply cop_nts__os; Col.
          apply 共线否定排列CAB.
          apply (不共线三点构成的角的等角三点也不共线 D' E' F'); 等角.
        }
        repeat (split; 等角); Side; Cop.
      }
      apply (和角的唯一性 A' B' C' G H I); auto.
      apply (等角保持和角性质 A B A0 A0 B J A B J); [|等角..].
      exists J.
      repeat (split; 等角); Cop.
      apply col123__nos; Col.
    }
    intro HB'out.
    apply not_bet_out in HB'out; auto.
    exfalso.
    apply HNColB.
    apply 等价共线BAC.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (原角小于等于和角 _ _ _ D E F); auto.
  }
  intro HNColB'.
  clear dependent A0.
  destruct HisiBE as [_ [_ [C1 HC1]]].
  分离合取式.
  统计不重合点.
  assert(等角 A' B' C' A B C1).
  { apply (和角的唯一性 A B C D E F); auto.
    apply (等角保持和角性质 A B C C B C1 A B C1); 等角.
    exists C1.
    repeat (split; 等角).
  }
  assert(OS B C1 C A).
  { apply one_side_symmetry.
    apply os_ts1324__os.
    - apply invert_one_side.
      apply cop_nts__os; Col.
      apply 共线否定排列CAB; apply (不共线三点构成的角的等角三点也不共线 A' B' C'); auto.
    - apply cop_nos__ts; Col; Cop.
      apply (不共线三点构成的角的等角三点也不共线 D E F); 等角.
  }
  elim(共线的决定性 D' E' F').
  { intro HColE'.
    elim(中间性的决定性 D' E' F').
    { intro HE'Bet.
      assert(HC0 : exists C0, 中点 B C C0) by apply 构造对称点.
      destruct HC0 as [C0 []].
      统计不重合点.
      assert(TS B C1 C C0).
      { apply bet__ts; auto.
        apply 共线否定排列BCA, (不共线三点构成的角的等角三点也不共线 D E F); 等角.
      }
      apply (等角保持和角性质 A B C C B C0 A B C0); [|等角..|].
        exists C0; repeat (split; 等角); Cop; apply col124__nos; Col.
      apply (和角的唯一性 A' B' C' G H I); auto.
      apply (等角保持和角性质 A B C1 C1 B C0 A B C0); [|等角| |等角].
        apply 异侧推出和角1, invert_two_sides, (l9_8_2 _ _ C); auto.
      apply (和角推加角唯一性 C B C1 _ _ _ _ _ _ C B C0).
        和角.
        apply (等角保持和角不大于平角性质 D E F G H I); 等角.
        和角.
        apply (等角保持和角性质 D E F G H I D' E' F'); 等角.
    }
    intro HE'out.
    apply not_bet_out in HE'out; auto.
    exfalso.
    apply HNColE.
    apply 等价共线BAC.
    apply out_col.
    apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (原角小于等于和角 _ _ _ G H I); auto.
  }
  intro HNColE'.
  clear dependent D0.
  assert(HJ : 和角不大于平角 C B C1 G H I) by (apply (等角保持和角不大于平角性质 D E F G H I); 等角).
  destruct HJ as [_ [_ [J]]].
  destruct HisiEH as [_ [_ [F1 HF1]]].
  分离合取式.
  统计不重合点.
  assert(等角 C B J D' E' F').
  { apply (角等的传递性 _ _ _ D E F1); auto.
    - apply (l11_22 _ _ _ C1 _ _ _ F); auto.
      split.
        left; split; apply cop_nos__ts; Cop;
        [apply (不共线三点构成的角的等角三点也不共线 D E F)|apply (不共线三点构成的角的等角三点也不共线 G H I)..]; 等角.
      split.
      等角.
      apply (角等的传递性 _ _ _ G H I); 等角.

    - apply (和角的唯一性 D E F G H I); auto.
      exists F1.
      repeat (split; 等角).
  }
  assert (~ Col C B C1) by (apply (不共线三点构成的角的等角三点也不共线 D E F); 等角).
  apply (等角保持和角性质 A B C C B J A B J); try (apply 同角相等); auto.
  - assert (TS B C J A).
    { apply (l9_8_2 _ _ C1).
        apply l9_2; apply cop_nos__ts; Col; Cop.
      apply invert_one_side.
      apply cop_nts__os; Col; Cop.
      apply 共线否定排列CAB, (不共线三点构成的角的等角三点也不共线 D' E' F'); 等角.
    }
    exists J.
    repeat (split; 等角); Side; Cop.
  - apply (和角的唯一性 A' B' C' G H I); auto.
    apply (等角保持和角性质 A B C1 C1 B J A B J); 等角.
    assert (TS B C1 A J).
    { apply (l9_8_2 _ _ C); auto.
      apply cop_nos__ts; Cop.
      apply (不共线三点构成的角的等角三点也不共线 G H I); 等角.
    }
    exists J.
    repeat (split; 等角); Side; Cop.
Qed.

Lemma 和角结合律2 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   和角 A B C D' E' F' K L M -> 和角 A' B' C' G H I K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  apply 和角的对称性.
  apply (和角结合律1 G H I D E F A B C K L M D' E' F'); 和角.
Qed.

(** Associativity of the sum of angles. *)

Lemma 和角结合律 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   (和角 A' B' C' G H I K L M <-> 和角 A B C D' E' F' K L M).
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  split.
    apply (和角结合律1 _ _ _ D E F); auto.
    apply (和角结合律2 _ _ _ D E F); auto.
Qed.

Lemma 和角不大于平角结合律1 : forall A B C D E F G H I A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   和角不大于平角 A' B' C' G H I -> 和角不大于平角 A B C D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' Hsams1 Hsams2 Hs1 Hs2 Hsams1'.
  统计不重合点.
  elim(共线的决定性 A B C).
  { intro HColB.
    destruct Hsams1 as [_ [[HEout|HBout]_]].
    - apply (等角保持和角不大于平角性质 A' B' C' G H I); auto.
      apply 等角的对称性; apply (任何角加上零角大小不变 _ _ _ D E F); auto.
      apply (零角加上任何角后者大小不变 D E F); auto.

    - apply not_bet_out in HBout; auto.
      apply 和角不大于平角的对称性.
      repeat split; auto.
      exists F'.
      split.
      apply l11_21_b; try (apply out_trivial); auto.
      split.
        apply col124__nos; Col.
      split; Cop.
      apply not_two_sides_id.
  }
  intro HNColB.
  elim(共线的决定性 D E F).
  { intro HColE.
    destruct Hsams2 as [_ [[HHout|HEout]_]].
    - apply (等角保持和角不大于平角性质 A B C D E F); try (apply 同角相等); auto.
      apply (任何角加上零角大小不变 _ _ _ G H I); auto.

    - apply not_bet_out in HEout; auto.
      apply (等角保持和角不大于平角性质 A' B' C' G H I); auto.
      apply 等角的对称性; apply (任何角加上零角大小不变 _ _ _ D E F); auto.
      apply (零角加上任何角后者大小不变 D E F); auto.
  }
  intro HNColE.
  elim(共线的决定性 G H I).
  { intro HColH.
    apply 和角不大于平角的对称性 in Hsams2.
    destruct Hsams2 as [_ [[|HHout] _]].
      exfalso; apply HNColE; Col.
    apply not_bet_out in HHout; auto.
    apply (等角保持和角不大于平角性质 A B C D E F); try (apply 同角相等); auto.
    apply (任何角加上零角大小不变 _ _ _ G H I); auto.
  }
  intro HNColH.
  split; auto.
  split.
    right; intro; apply HNColB; Col.
  assert(~ Col A' B' C').
  { intro.
    exfalso.
    destruct Hsams1' as [_ [[|HB'out] _]].
      apply HNColH; Col.
    apply not_bet_out in HB'out; auto.
    apply HNColB.
    apply 等价共线BAC.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (原角小于等于和角 _ _ _ D E F); auto.
  }
  assert(HC1 : exists C1, 等角 C B C1 D E F /\ ~ OS B C A C1 /\ ~ TS A B C C1 /\ 共面 A B C C1).
    destruct Hsams1 as [_ []]; auto.
  destruct HC1 as [C1].
  分离合取式.
  统计不重合点.
  assert(等角 A B C1 A' B' C').
    apply (和角的唯一性 A B C D E F); auto; exists C1; repeat (split; 等角).
  assert(HJ : exists J, 等角 C1 B J G H I /\ ~ OS B C1 C J /\ ~ TS C B C1 J /\ 共面 C B C1 J).
  { apply (等角保持和角不大于平角性质 _ _ _ _ _ _ C B C1 G H I) in Hsams2; 等角.
    destruct Hsams2 as [_ [_ HJ]]; auto.
  }
  destruct HJ as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
  分离合取式.
  apply (等角保持和角不大于平角性质 _ _ _ _ _ _ A B C1 C1 B J) in Hsams1'; 等角.
  destruct Hsams1' as [_ [_ [J']]].
  分离合取式.
  统计不重合点.
  assert (~ Col A B C1) by (apply (不共线三点构成的角的等角三点也不共线 A' B' C'); 等角).
  assert (~ Col C B C1) by (apply (不共线三点构成的角的等角三点也不共线 D E F); 等角).
  assert (共面 C1 B A J) by (apply coplanar_trans_1 with C; Cop; Col).
  assert (HUn : Out B J' J \/ TS C1 B J' J).
    apply conga_cop__or_out_ts; auto.
    apply coplanar_trans_1 with A; Cop; Col.
  destruct HUn as [HJJ'|Hts].
  { exists J.
    split; [|repeat split].
    - apply (和角的唯一性 D E F G H I); auto.
      apply (等角保持和角性质 C B C1 C1 B J C B J); try (apply 同角相等); auto.
      exists J.
      repeat (split; 等角).

    - elim(共线的决定性 C B J).
      intro; apply col124__nos; Col.
      intro.
      apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ C1).
        apply l9_2; apply cop_nos__ts; Col; Cop.
      apply invert_one_side.
      apply cop_nts__os; Col; Cop.

    - elim(共线的决定性 A B J).
        intro; intro Hts; destruct Hts; 分离合取式; Col.
      intro.
      apply l9_9_bis.
      apply (one_side_transitivity _ _ _ C1).
        apply cop_nts__os; Col.
      apply (one_side_transitivity _ _ _ J');
      [|apply invert_one_side; apply out_one_side; Col].
      apply cop_nts__os; Col.
      apply 共线否定排列CAB; apply (不共线三点构成的角的等角三点也不共线 A B J); auto.
      apply out2__conga; [apply out_trivial|]; auto.

    - apply coplanar_trans_1 with C1; Cop; Col.
  }
  exfalso.
  apply l9_2 in Hts.
  apply invert_two_sides in Hts.
  apply HJ2.
  exists J'.
  split; auto.
  apply (l9_8_2 _ _ A).
  - apply cop_nos__ts; Cop.
    apply (不共线三点构成的角的等角三点也不共线 G H I); auto.
    apply (角等的传递性 _ _ _ C1 B J); 等角.
  - apply os_ts1324__os.
    apply invert_one_side; apply cop_nts__os; Col.
    apply cop_nos__ts; Col; Cop.
Qed.

Lemma 和角不大于平角结合律2 : forall A B C D E F G H I A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   和角不大于平角 A B C D' E' F' -> 和角不大于平角 A' B' C' G H I.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply 和角不大于平角的对称性.
  apply (和角不大于平角结合律1 G H I D E F A B C D' E' F'); 和角.
Qed.

Lemma 和角不大于平角结合律 : forall A B C D E F G H I A' B' C' D' E' F',
   和角不大于平角 A B C D E F -> 和角不大于平角 D E F G H I ->
   和角 A B C D E F A' B' C' -> 和角 D E F G H I D' E' F' ->
   (和角不大于平角 A' B' C' G H I <-> 和角不大于平角 A B C D' E' F').
Proof.
  intros A B C D E F.
  split.
  apply (和角不大于平角结合律1 _ _ _ D E F); auto.
  apply (和角不大于平角结合律2 _ _ _ D E F); auto.
Qed.

Lemma 和角不大于平角推不同侧不异侧 : forall A B C J, 和角不大于平角 A B C C B J -> ~ OS B C A J ->
  ~ TS A B C J.
Proof.
  intros A B C J HIsi HNOS HTS.
  destruct HIsi as [_ [HUn [J' [HConga [HNOS' [HNTS HCop]]]]]].
  assert (共面 C B J J').
    apply coplanar_trans_1 with A; Cop.
    apply two_sides_not_col in HTS; Col.
  destruct (conga_cop__or_out_ts C B J J') as [HOut|HTS1]; 等角.
  - apply HNTS.
    apply l9_2, l9_8_2 with J; Side.
    apply invert_one_side, out_one_side; trivial.
    destruct HTS as [_ []]; Col.
  - destruct HTS as [HNCol1 [HNCol2 _]].
    统计不重合点.
    absurd (OS B C J J'); Side.
    destruct HTS1 as [HNCol _].
    assert (~ Col C B J') by (apply (不共线三点构成的角的等角三点也不共线 C B J); Col; 等角).
    exists A; split; apply cop_nos__ts; Col; Side.
      apply coplanar_trans_1 with J'; Col; Cop.
      Cop.
Qed.

Lemma 和角不大于平角推不同侧不异侧_间接 : forall A B C D E F J,
  和角不大于平角 A B C D E F -> 等角 C B J D E F -> ~ OS B C A J -> ~ TS A B C J.
Proof.
  intros A B C D E F J HIsi HConga.
  apply 和角不大于平角推不同侧不异侧.
  统计不重合点.
  apply (等角保持和角不大于平角性质 A B C D E F); 等角.
Qed.


(** If B <= B', E <= E' and B + E = B' + E', then B = B' and E = E' *)

Lemma 两角与非较大角和等则对应角等_1 : forall A B C D E F G H I A' B' C' D' E' F',
   角度小于等于 A B C A' B' C' -> 角度小于等于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G H I -> 等角 A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' HleaB HleaE Hisi' Hsuma Hsuma'.
  统计不重合点.
  apply (和角推原角唯一性 _ _ _ _ _ _ D E F G H I); auto.
    apply (角度小于等于保持和角不大于平角性质 _ _ _ _ _ _ A' B' C' D' E' F'); auto.
    apply (角度小于等于保持和角不大于平角性质 _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  assert (Haux := 和角的存在性 A' B' C' D E F).
  destruct Haux as [G' [H' [I']]]; auto.
  apply (等角保持和角性质 A' B' C' D E F G' H' I'); try (apply 同角相等); auto.
  apply 双角度偏序推等角.
  apply (和角保持角度小于等于性质_右 A' B' C' D E F _ _ _ D' E' F'); auto.
  apply (和角保持角度小于等于性质_左 A B C D E F _ _ _ A' B' C'); auto.
  apply (角度小于等于保持和角不大于平角性质 _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
Qed.

Lemma 两角与非较大角和等则对应角等_2 : forall A B C D E F G H I A' B' C' D' E' F',
   角度小于等于 A B C A' B' C' -> 角度小于等于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G H I -> 等角 D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply (两角与非较大角和等则对应角等_1 _ _ _ A B C G H I _ _ _ A' B' C'); 和角.
Qed.

(** If B + E = E, then B = 0 *)

Lemma 和角与加角等则原角为零角 : forall A B C D E F, 和角 A B C D E F D E F -> 和角不大于平角 A B C D E F -> Out B A C.
Proof.
  intros A B C D E F HSuma HIsi.
  统计不重合点.
  apply (l11_21_a D E D).
    apply out_trivial; auto.
  apply 两角与非较大角和等则对应角等_1 with D E F D E F D E F; Lea.
  exists F; repeat (split; 等角); Cop.
  apply col123__nos; Col.
Qed.

Lemma 和角与原角等则加角为零角 : forall A B C D E F, 和角 A B C D E F A B C -> 和角不大于平角 A B C D E F -> Out E D F.
Proof.
  intros A B C D E F HSuma HIsi.
  apply 和角与加角等则原角为零角 with A B C.
    apply 和角的对称性; trivial.
  apply 和角不大于平角的对称性; trivial.
Qed.

(** If B < B' and E <= E', then B + E < B' + E' *)

Lemma 角度一全序一偏序则和角保持全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 A B C A' B' C' -> 角度小于等于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HltaB HleaE Hisi' Hsuma Hsuma'.
  统计不重合点.
  split.
  apply (和角保持角度小于等于性质 A B C D E F _ _ _ A' B' C' D' E' F'); Lea.
  intro.
  destruct HltaB as [HleaB HNConga].
  apply HNConga.
  apply (两角与非较大角和等则对应角等_1 _ _ _ D E F G H I _ _ _ D' E' F'); auto.
  apply (等角保持和角性质 A' B' C' D' E' F' G' H' I'); 等角.
Qed.

Lemma 角度一偏序一全序则和角保持全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 A B C A' B' C' -> 角度小于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (角度一全序一偏序则和角保持全序 D E F A B C _ _ _ D' E' F' A' B' C'); 和角.
Qed.

Lemma 角度双全序则和角保持全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 A B C A' B' C' -> 角度小于 D E F D' E' F' -> 和角不大于平角 A' B' C' D' E' F' ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (角度一全序一偏序则和角保持全序 A B C D E F _ _ _ A' B' C' D' E' F'); auto.
  apply 角度小于蕴含角度小于等于; auto.
Qed.

(** If E >= E' and B + E <= B' + E', then B <= B' *)

Lemma 加角和角偏序则原角偏序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 D' E' F' D E F -> 角度小于等于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于等于 A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  统计不重合点.
  elim(lta_dec A' B' C' A B C); [|intro; apply n角度小于蕴含角度小于等于; auto].
  intro Hlta.
  exfalso.
  assert(~ 角度小于等于 G H I G' H' I'); auto.
  apply 角度小于蕴含反向角度小于等于的否定.
  apply(角度一全序一偏序则和角保持全序 A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.
(* 无用 *)
Lemma 原角和角偏序则加角偏序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 A' B' C' A B C -> 角度小于等于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于等于 D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (加角和角偏序则原角偏序 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply 和角的对称性); auto.
  apply 和角不大于平角的对称性; assumption.
Qed.

(** If E > E' and B + E <= B' + E', then B < B' *)

Lemma 加角反全序和角偏序则原角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 D' E' F' D E F -> 角度小于等于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  统计不重合点.
  elim(lea_dec A' B' C' A B C) ;[|intro; apply nlea__lta; auto].
  intro Hlea.
  exfalso.
  assert(~ 角度小于等于 G H I G' H' I'); auto.
  apply 角度小于蕴含反向角度小于等于的否定.
  apply(角度一偏序一全序则和角保持全序 A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma 原角反全序和角偏序则加角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 A' B' C' A B C -> 角度小于等于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (加角反全序和角偏序则原角全序 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply 和角的对称性); auto.
  apply 和角不大于平角的对称性; assumption.
Qed.

(** If E >= E' and B + E < B' + E', then B < B' *)

Lemma 加角反偏序和角全序则原角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 D' E' F' D E F -> 角度小于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  统计不重合点.
  elim(lea_dec A' B' C' A B C); [|intro; apply nlea__lta; auto].
  intro Hlta.
  exfalso.
  assert(~ 角度小于 G H I G' H' I'); auto.
  apply 两角成偏序关系则不可能成反全序关系.
  apply(和角保持角度小于等于性质 A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma 原角反偏序和角全序则加角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于等于 A' B' C' A B C -> 角度小于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (加角反偏序和角全序则原角全序 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply 和角的对称性); auto.
  apply 和角不大于平角的对称性; assumption.
Qed.
(* 无用 *)
Lemma 加角反全序和角全序则原角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 D' E' F' D E F -> 角度小于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (加角反偏序和角全序则原角全序 _ _ _ D E F G H I _ _ _ D' E' F' G' H' I'); auto.
  apply 角度小于蕴含角度小于等于; assumption.
Qed.

Lemma 原角反全序和角全序则加角全序 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   角度小于 A' B' C' A B C -> 角度小于 G H I G' H' I' -> 和角不大于平角 A B C D E F ->
   和角 A B C D E F G H I -> 和角 A' B' C' D' E' F' G' H' I' -> 角度小于 D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (原角反偏序和角全序则加角全序 A B C _ _ _ G H I A' B' C' _ _ _ G' H' I'); auto.
  apply 角度小于蕴含角度小于等于; assumption.
Qed.

(** The sum of two angles of a triangle is less than a straight angle (three lemmas) *)

Lemma 三角形两内角之和小于平角_BC : forall A B C, A <> B -> A <> C -> B <> C -> 和角不大于平角 A B C B C A.
Proof.
  intros A B C.
  intros.
  assert(HA' := 构造对称点 A B).
  destruct HA' as [A'].
  统计不重合点.
  apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A'); Between.
  elim(共线的决定性 A B C).
  { intro HCol.
    elim(中间性的决定性 A C B).
    { intro HCBet.
      apply 等角小于等于自己.
      apply 成中间性三点组的角相等; Between.
      apply (中间性的交换传递性1 A); Between.
    }
    intro.
    apply l11_31_1_任何角小于等于平角_Out表述; auto.
    apply l6_6.
    apply not_bet_out; Col.
  }
  intro.
  apply 角度小于蕴含角度小于等于.
  apply l11_41_证明辅助定理; Col; Between.
Qed.

Lemma 共线与和角推共线 : forall A B C D E F, Col D E F -> 和角 A B C B C A D E F -> Col A B C.
Proof.
  intros A B C D E F HCol HSuma.
  destruct (共线的决定性 A B C) as [|HNCol]; [trivial|].
  exfalso.
  destruct (中间性的决定性 D E F).
  - assert (HP := 构造对称点 A B).
    destruct HP as [P []].
    统计不重合点.
    assert (Hlta : 角度小于 D E F A B P);
    [|destruct Hlta as [Hlea HNConga]; apply HNConga; 等角].
    assert (TS B C A P).
      apply bet__ts; Col.
    apply (角度一偏序一全序则和角保持全序 A B C B C A _ _ _ A B C C B P); [Lea| |和角..].
    apply l11_41_证明辅助定理; Col.

  - 统计不重合点.
    apply HNCol.
    apply 等价共线CBA.
    apply out_col.
    apply (out_lea__out _ _ _ D E F).
      apply not_bet_out; Col.
    apply (加角小于等于和角 A B C); auto.
    apply 三角形两内角之和小于平角_BC; auto.
Qed.
(* 无用 *)
Lemma 不共线与和角推不共线 : forall A B C D E F, ~ Col A B C -> 和角 A B C B C A D E F -> ~ Col D E F.
Proof.
  intros A B C D E F HNCol HSuma HCol.
  apply HNCol, 共线与和角推共线 with D E F; assumption.
Qed.


(** Sum of two right angles is a straight angle:
  90+90=180.
 *)

Lemma 两直角之和为平角 : forall A B C D E F G H I, Per A B C -> Per D E F ->
   和角 A B C D E F G H I -> Bet G H I.
Proof.
  intros A B C D E F G H I HB HE HSuma.
  destruct HSuma as [A1 [HConga1 [HNos [HCop HConga2]]]].
  统计不重合点.
  assert(Per A1 B C) by (apply (l11_17_等于直角的角是直角 D E F); 等角).
  apply (零角的等角是零角 A B A1); auto.
  apply (col_two_sides_bet _ C).
  apply 等价共线CAB; apply cop_per2__col with C; Cop.
  apply cop_nos__ts; Cop; apply 成直角三点不共线; auto.
Qed.

Lemma 平角为两直角之和 : forall A B C D E F G H I,
   A <> B -> B <> C -> D <> E -> E <> F -> G <> H -> H <> I ->
   Per A B C -> Per D E F ->
   Bet G H I -> 和角 A B C D E F G H I.
Proof.
  intros A B C D E F G H I H1 H2 H3 H4 H5 H6 HB HE HBet.
  destruct (和角的存在性 A B C D E F) as [G' [H' [I' HSuma]]]; auto.
  apply 等角保持和角性质 with A B C D E F G' H' I'; [|apply 同角相等..|]; auto.
  统计不重合点.
  apply 成中间性三点组的角相等; auto.
  apply (两直角之和为平角 A B C D E F); assumption.
Qed.

Lemma 两直角之和不大于平角 : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
  Per A B C -> Per D E F -> 和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F HAB HBC HDE HEF HPerB HPerE.
  destruct (和角的存在性 A B C D E F) as [G [H [I]]]; auto.
  apply 和角为平角推和角不大于平角 with G H I; [|apply (两直角之和为平角 A B C D E F)]; assumption.
Qed.

(** If 90+x=180 then x=90. *)
(* 半无用 *)
Lemma 直角加上一角为平角则该角为直角 : forall A B C D E F G H I, Per A B C -> Bet G H I ->
   和角 A B C D E F G H I -> Per D E F.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  assert(HA1 := 构造对称点 A B).
  destruct HA1 as [A1].
  统计不重合点.
  assert(HNCol : ~ Col A B C) by (apply 成直角三点不共线; auto).
  apply (l11_17_等于直角的角是直角 A B C); auto.
  apply (和角推加角唯一性 A B C _ _ _ _ _ _ G H I); auto.
  - apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A1); Between.
    apply 等角小于等于自己.
    apply 等角的左交换性.
    apply l11_18_1; Between; Perp.

  - destruct HSuma as [F1 [HConga1 [HNos [HCop HConga2]]]].
    repeat split; auto.
      right; intro; apply HNCol; Col.
    exists F1.
    repeat (split; auto).
    intro Habs.
    destruct Habs as [_ [Habs]].
    apply Habs.
    apply 等价共线CAB.
    apply 中间性蕴含共线1.
    apply (零角的等角是零角 G H I); 等角.

  - assert(HSuma' := 和角的存在性 A B C A B C).
    destruct HSuma' as [G' [H' [I']]]; auto.
    统计不重合点.
    apply (等角保持和角性质 A B C A B C G' H' I'); try (apply 同角相等); auto.
    apply 成中间性三点组的角相等; auto.
    apply (两直角之和为平角 A B C A B C); auto.
Qed.

(** If x+90=180 then x=90. *)

Lemma 一角加上直角为平角则该角为直角 : forall A B C D E F G H I, Per D E F -> Bet G H I ->
   和角 A B C D E F G H I -> Per A B C.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  apply (直角加上一角为平角则该角为直角 D E F _ _ _ G H I); 和角.
Qed.

(** If x+x=180 then x=90. *)

Lemma 一角的倍角为平角则该角为直角 : forall A B C D E F, Bet D E F -> 和角 A B C A B C D E F ->
   Per A B C.
Proof.
  intros A B C D E F HBet HSuma.
  统计不重合点.
  destruct HSuma as [A' [HConga1 [_ [_ HConga2]]]].
  apply 直角的对称性.
  apply (l11_18_2 _ _ _ A'); 等角.
  apply (零角的等角是零角 D E F); 等角.
Qed.

(** If x<90 then x+x<180 (two lemmas). *)

Lemma 锐角的倍角不大于平角 : forall A B C, 为锐角 A B C -> 和角不大于平角 A B C A B C.
Proof.
  intros A B C Hacute.
  assert(HA' := 构造对称点 A B).
  destruct HA' as [A'].
  统计不重合点.
  apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A'); Between.
  apply acute_obtuse__lta; auto.
  apply 为钝角的对称性.
  apply (acute_中间性平角为钝角 A); Between.
Qed.

Lemma 锐角的倍角不为平角 : forall A B C D E F, 为锐角 A B C -> 和角 A B C A B C D E F -> ~ Bet D E F.
Proof.
  intros A B C D E F Hacute HSuma.
  统计不重合点.
  intro.
  apply (一角不可能小于自己 A B C).
  apply acute_per__lta; auto.
  apply (一角的倍角为平角则该角为直角 _ _ _ D E F); auto.
Qed.

(** If x<90 and y<90 then x+y<180 (two lemmas). *)

Lemma 两锐角之和不大于平角 : forall A B C D E F, 为锐角 A B C -> 为锐角 D E F -> 和角不大于平角 A B C D E F.
Proof.
  assert (Haux : forall A B C D E F, 为锐角 A B C -> 角度小于等于 D E F A B C -> 和角不大于平角 A B C D E F).
  { intros A B C D E F H为锐角 HLea.
    apply 角度小于等于保持和角不大于平角性质 with A B C A B C.
      apply 锐角的倍角不大于平角, H为锐角.
      统计不重合点; apply 任何角小于等于自己; auto.
      assumption.
  }
  intros A B C D E F H为锐角1 H为锐角2.
  统计不重合点.
  destruct (lea_total A B C D E F); 和角.
Qed.

Lemma 两锐角之和不为平角 : forall A B C D E F G H I,
  为锐角 A B C -> 为锐角 D E F -> 和角 A B C D E F G H I -> ~ Bet G H I.
Proof.
  assert (Haux : forall A B C D E F G H I, 为锐角 A B C -> 角度小于等于 D E F A B C -> 和角 A B C D E F G H I ->
    ~ Bet G H I).
  { intros A B C D E F G H I H为锐角 HLea HSuma HBet.
    统计不重合点.
    destruct (和角的存在性 A B C A B C) as [A' [B' [C']]]; auto.
    apply (锐角的倍角不为平角 A B C A' B' C'); trivial.
    apply (bet_lea__bet G H I); [apply HBet|].
    apply 和角保持角度小于等于性质 with A B C D E F A B C A B C; trivial.
      apply 任何角小于等于自己; auto.
      apply 锐角的倍角不大于平角, H为锐角.
  }
  intros A B C D E F G H I H为锐角1 H为锐角2 HSuma.
  统计不重合点.
  destruct (lea_total A B C D E F); auto.
    apply 和角的对称性 in HSuma; apply (Haux D E F A B C); assumption.
    apply (Haux A B C D E F); assumption.
Qed.

(** If x<90 then x+90<180 (two lemmas) *)

Lemma 锐角与直角之和不大于平角 : forall A B C D E F, A <> B -> B <> C ->
  Per A B C -> 为锐角 D E F -> 和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F HAB HBC HPer H为锐角.
  apply 角度小于等于保持和角不大于平角性质 with A B C A B C.
    apply 两直角之和不大于平角; auto.
    apply 任何角小于等于自己; auto.
    apply acute_per__lta; auto.
Qed.

Lemma 锐角与直角之和不为平角 : forall A B C D E F G H I, A <> B -> B <> C ->
  Per A B C -> 为锐角 D E F -> 和角 A B C D E F G H I -> ~ Bet G H I.
Proof.
  intros A B C D E F G H I HAB HBC HPer H为锐角 HSuma HBet.
  统计不重合点.
  apply (一角不可能小于自己 G H I).
  apply 角度一偏序一全序则和角保持全序 with A B C D E F A B C A B C; Lea.
    apply 两直角之和不大于平角; auto.
    apply 平角为两直角之和; auto.
Qed.

(** If x>90 then x+x>180. *)

Lemma 钝角的倍角大于平角 : forall A B C, 为钝角 A B C -> ~ 和角不大于平角 A B C A B C.
Proof.
  intros A B C Hobtuse.
  assert(HA' := 构造对称点 A B).
  destruct HA' as [A'].
  统计不重合点.
  intro.
  apply (一角不可能小于自己 A B C).
  apply (lea123456_lta__lta _ _ _ A' B C).
  - apply 角度小于等于的右交换性.
    apply (用角度小于等于特征化和角不大于平角 A); Between.
  - apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); Between.
Qed.

(** If x+x<180 then x<90. *)

Lemma 一角的倍角不大于平角则该角为锐角 : forall A B C D E F, ~ Bet D E F -> 和角不大于平角 A B C A B C ->
   和角 A B C A B C D E F -> 为锐角 A B C.
Proof.
  intros A B C D E F HNBet HIsi HSuma.
  统计不重合点.
  elim(angle_partition A B C); auto.
  intro HUn.
  exfalso.
  destruct HUn.
  - apply HNBet.
    apply (两直角之和为平角 A B C A B C); auto.
  - assert(~ 和角不大于平角 A B C A B C); auto.
    apply 钝角的倍角大于平角; auto.
Qed.

(** If x+x>180 then x>90. *)

Lemma 一角的倍角大于平角则该角为钝角 : forall A B C, A <> B -> B <> C -> ~ 和角不大于平角 A B C A B C -> 为钝角 A B C.
Proof.
  intros A B C HAB HBC HNIsi.
  elim(angle_partition A B C); auto.
  - intro.
    exfalso.
    apply HNIsi.
    apply 锐角的倍角不大于平角; auto.

  - intro HUn.
    destruct HUn; auto.
    exfalso.
    apply HNIsi.
    assert(HA' := 构造对称点 A B).
    assert(HNCol : ~ Col A B C) by (apply 成直角三点不共线; auto).
    destruct HA' as [A'].
    统计不重合点.
    repeat split; auto.
    right; intro; Col.
    exists A'.
    split.
      apply 等角的右交换性; apply 等角的对称性; apply l11_18_1; Between; Perp.
    split.
    { apply l9_9.
      apply bet__ts; Between; Col.
    }
    split; Cop.
    intros [_ [HNCol']]; apply HNCol'; Col.
Qed.

(** If doubling two acute angles makes the same result, then these angles are congruent *)

Lemma 两角倍角不大于平角且相等则两角相等 : forall A B C D E F A' B' C',
  和角不大于平角 A B C A B C -> 和角 A B C A B C D E F ->
  和角不大于平角 A' B' C' A' B' C' -> 和角 A' B' C' A' B' C' D E F ->
  等角 A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HIsi HSuma HIsi' HSuma'.
  统计不重合点.
  destruct (lea_total A B C A' B' C'); trivial; [|apply 等角的对称性];
  eapply 两角与非较大角和等则对应角等_1; eauto.
Qed.

Lemma 两锐角倍角相等则两角相等 : forall A B C D E F A' B' C',
  为锐角 A B C -> 和角 A B C A B C D E F ->
  为锐角 A' B' C' -> 和角 A' B' C' A' B' C' D E F ->
  等角 A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HB HSuma HB'.
  apply 两角倍角不大于平角且相等则两角相等; try apply 锐角的倍角不大于平角; assumption.
Qed.

(** Sum of two straight angles is a null angle *)

Lemma 两平角之和为零角 : forall A B C D E F G H I, Bet A B C -> Bet D E F ->
  和角 A B C D E F G H I -> Out H G I.
Proof.
  intros A B C D E F G H I HBet1 HBet2 HSuma.
  统计不重合点.
  apply (零角的等角推出外共线 A B).
  apply (和角的唯一性 A B C D E F); trivial.
  exists A.
  repeat (split; 等角); Cop.
  apply col123__nos; Col.
Qed.

(** Sum of two degenerate angles is degenerate *)

Lemma 两退化角之和退化 : forall A B C D E F G H I, Col A B C -> Col D E F ->
  和角 A B C D E F G H I -> Col G H I.
Proof.
  intros A B C D E F G H I HCol1 HCol2 HSuma.
  destruct (中间性的决定性 A B C).
  destruct (中间性的决定性 D E F).
  - apply 等价共线BAC, out_col, (两平角之和为零角 A B C D E F); assumption.
  - apply (共线三点构成的角的等角三点也共线 A B C); trivial.
    apply 任何角加上零角大小不变 with D E F; trivial.
    apply not_bet_out; assumption.
  - apply (共线三点构成的角的等角三点也共线 D E F); trivial.
    apply (零角加上任何角后者大小不变 A B C); trivial.
    apply not_bet_out; assumption.
Qed.

(** The sum of two supplementary angles is a flat angle (two lemmas) *)

Lemma 补角和为平角 : forall A B C D E F G H I,
  互为补角 A B C D E F -> 和角 A B C D E F G H I -> Bet G H I.
Proof.
  intros A B C D E F G H I [_ [A' [HBet HCong]]] [A'' [HConga1 [HNOS [HCop HConga2]]]].
  apply (零角的等角是零角 A B A''); trivial.
  统计不重合点.
  apply 中间性的对称性, l6_2 with A'; Between.
  destruct (conga_cop__or_out_ts C B A' A'') as [|HTS]; auto.
    apply 等价共面ACDB, col_cop__cop with A; Col; Cop.
    apply 角等的传递性 with D E F; 等角.
  exfalso.
  apply HNOS.
  exists A'; split; [|Side].
  destruct HTS as [HNCol1 [HNCol2 _]].
  repeat split.
    intro; apply HNCol1; ColR.
    Col.
  exists B; split; Col.
Qed.

Lemma 平角为补角和 : forall A B C D E F G H I, G <> H -> H <> I ->
  互为补角 A B C D E F -> Bet G H I -> 和角 A B C D E F G H I.
Proof.
  intros A B C D E F G H I; intros.
  统计不重合点.
  destruct (和角的存在性 A B C D E F) as [G' [H' [I']]]; auto.
  apply (等角保持和角性质 A B C D E F G' H' I'); try apply 同角相等; auto.
  统计不重合点.
  apply 成中间性三点组的角相等; auto.
  apply (补角和为平角 A B C D E F); assumption.
Qed.

(** If the sum of two angles is a flat angle, then they are supplementary *)

Lemma 和角为平角则为补角 : forall A B C D E F G H I,
  和角 A B C D E F G H I -> Bet G H I -> 互为补角 A B C D E F.
Proof.
  intros A B C D E F G H I [A' [HConga1 [_ [_ HConga2]]]] HBet.
  统计不重合点.
  split; auto.
  exists A'.
  split; 等角.
  apply (零角的等角是零角 G H I); 等角.
Qed.

(** The sum of two angles is equal to the sum of their two supplementary angles *)

Lemma 两角和与其补角和相等_中间性表述 : forall A B C D E F G H I A' D', A' <> B -> D' <> E ->
  Bet A B A' -> Bet D E D' -> 和角 A B C D E F G H I -> 和角 A' B C D' E F G H I.
Proof.
  intros A B C D E F G H I A' D' HBA' HED' HBetA HBetD [J [HJ1 [HJ2 [HJ3 HJ4]]]]; 分离合取式.
  destruct (由一点往一方向构造等长线段 C B B C) as [C' []].
  统计不重合点.
  apply (等角保持和角性质 A B C' D' E F G H I); [|apply l11_14; Between|等角..].
  exists J.
  split.
    apply l11_13 with C D; Between.
  repeat (split; trivial).
    intro; apply HJ2, col_one_side with C'; Col.
  apply 等价共面ACDB, col_cop__cop with C; Col; Cop.
Qed.

Lemma 两角和与其补角和相等 : forall A B C D E F G H I A' B' C' D' E' F',
  互为补角 A B C A' B' C' -> 互为补角 D E F D' E' F' -> 和角 A B C D E F G H I ->
  和角 A' B' C' D' E' F' G H I.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' [_ [A0 []]] [_ [D0 []]] HSuma.
  统计不重合点.
  apply (等角保持和角性质 A0 B C D0 E F G H I); 等角.
  apply 两角和与其补角和相等_中间性表述 with A D; auto.
Qed.

(** If doubling two obtuse angles makes the same result, then these angles are congruent *)

Lemma 两钝角倍角相等则两角相等 : forall A B C D E F A' B' C',
  为钝角 A B C -> 和角 A B C A B C D E F ->
  为钝角 A' B' C' -> 和角 A' B' C' A' B' C' D E F ->
  等角 A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HB HSuma HB' HSuma'.
  destruct (由一点往一方向构造等长线段 A B A B) as [A0 []].
  destruct (由一点往一方向构造等长线段 A' B' A' B') as [A0' []].
  统计不重合点.
  apply l11_13 with A0 A0'; Between.
  apply 两锐角倍角相等则两角相等 with D E F.
    apply (bet_obtuse__acute A); auto.
    apply 两角和与其补角和相等_中间性表述 with A A; auto.
    apply (bet_obtuse__acute A'); auto.
    apply 两角和与其补角和相等_中间性表述 with A' A'; auto.
Qed.

(** If doubling two angles makes the same result, then they are either congruent or supplementary *)

Lemma 两角倍角相等则两角相等或补角相等 : forall A B C D E F A' B' C' A0, A0 <> B ->
  Bet A B A0 -> 和角 A B C A B C D E F -> 和角 A' B' C' A' B' C' D E F ->
  等角 A B C A' B' C' \/ 等角 A0 B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' A0 HBA0 HBet HSuma.
  revert A' B' C'.
  assert (Haux : forall A' B' C', 为锐角 A' B' C' -> 和角 A' B' C' A' B' C' D E F ->
    等角 A B C A' B' C' \/ 等角 A0 B C A' B' C').
  { intros A' B' C' H为锐角' HSuma'.
    统计不重合点.
    destruct (angle_partition A B C) as [H为锐角|[HPer|H为钝角]]; auto.
    - left; apply 两锐角倍角相等则两角相等 with D E F; auto.
    - exfalso.
      apply (锐角的倍角不为平角 A' B' C' D E F); [..|apply (两直角之和为平角 A B C A B C)]; assumption.
    - right; apply 两锐角倍角相等则两角相等 with D E F; auto.
        apply (bet_obtuse__acute A); auto.
        apply 两角和与其补角和相等_中间性表述 with A A; auto.
  }
  intros A' B' C' HSuma'.
  统计不重合点.
  destruct (angle_partition A' B' C') as [H为锐角|[HPer|H为钝角]]; auto.
  - left.
    apply l11_16_直角相等; auto.
    apply 一角的倍角为平角则该角为直角 with D E F; [apply (两直角之和为平角 A' B' C' A' B' C')|]; assumption.
  - destruct (由一点往一方向构造等长线段 A' B' A' B') as [A0' []].
    统计不重合点.
    destruct (Haux A0' B' C').
      apply (bet_obtuse__acute A'); auto.
      apply 两角和与其补角和相等_中间性表述 with A' A'; auto.
      right; apply l11_13 with A A0'; Between.
      left; apply l11_13 with A0 A0'; Between.
Qed.

Lemma 两角倍角相等则两角相等或互补 : forall A B C A' B' C' D E F ,
  和角 A B C A B C D E F -> 和角 A' B' C' A' B' C' D E F ->
  等角 A B C A' B' C' \/ 互为补角 A B C A' B' C'.
Proof.
  intros A B C A' B' C' D E F HSuma HSuma'.
  destruct (由一点往一方向构造等长线段 A B A B) as [A0 []].
  统计不重合点.
  destruct (两角倍角相等则两角相等或补角相等 A B C D E F A' B' C' A0); auto.
  right.
  split; auto.
  exists A0; split; 等角.
Qed.


(** Basic properties about the sum of the angles of a triangle *)

Lemma 三角形内角和的存在性 : forall A B C, A <> B -> B <> C -> A <> C ->
  exists D E F, 三角形内角和 A B C D E F.
Proof.
  intros A B C HAB HBC HAC.
  destruct (和角的存在性 A B C B C A) as [G [H [I HSuma1]]]; auto.
  统计不重合点.
  destruct (和角的存在性 G H I C A B) as [D [E [F HSuma2]]]; auto.
  exists D; exists E; exists F; exists G; exists H; exists I.
  split; assumption.
Qed.

Lemma 等价三角形内角和BCA : forall A B C D E F, 三角形内角和 A B C D E F -> 三角形内角和 B C A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  统计不重合点.
  assert(Hex:= 和角的存在性 B C A C A B).
  destruct Hex as [B2 [C2 [A2 Hex]]]; auto.
  exists B2.
  exists C2.
  exists A2.
  split; auto.
  apply 和角的对称性.
  apply (和角结合律 A B C B C A C A B D E F A1 B1 C1 B2 C2 A2); try (apply 三角形两内角之和小于平角_BC); auto.
Qed.

Lemma 等价三角形内角和CAB : forall A B C D E F, 三角形内角和 A B C D E F -> 三角形内角和 C A B D E F.
Proof.
  intros.
  do 2 apply 等价三角形内角和BCA.
  assumption.
Qed.

Lemma 等价三角形内角和CBA : forall A B C D E F, 三角形内角和 A B C D E F -> 三角形内角和 C B A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  apply 和角的对称性 in HT2.
  统计不重合点.
  assert(Hex:= 和角的存在性 C A B A B C).
  destruct Hex as [C2 [A2 [B2 Hex]]]; auto.
  exists C2.
  exists A2.
  exists B2.
  split.
  和角.
  apply 和角的中交换性.
  apply (和角结合律 C A B A B C B C A D E F C2 A2 B2 A1 B1 C1); try (apply 三角形两内角之和小于平角_BC); auto.
Qed.

Lemma 等价三角形内角和BAC : forall A B C D E F, 三角形内角和 A B C D E F -> 三角形内角和 B A C D E F.
Proof.
  intros.
  apply 等价三角形内角和CBA.
  apply 等价三角形内角和CAB.
  assumption.
Qed.

Lemma 等价三角形内角和ACB : forall A B C D E F, 三角形内角和 A B C D E F -> 三角形内角和 A C B D E F.
Proof.
  intros.
  apply 等价三角形内角和CBA.
  apply 等价三角形内角和BCA.
  assumption.
Qed.

Lemma 等角保持三角形内角和性质 : forall A B C D E F D' E' F',
  三角形内角和 A B C D E F -> 等角 D E F D' E' F' -> 三角形内角和 A B C D' E' F'.
Proof.
  intros A B C D E F D' E' F' HTri HConga.
  destruct HTri as [G [H [I [HSuma1 HSuma2]]]].
  exists G; exists H; exists I; split; trivial.
  统计不重合点; apply (等角保持和角性质 G H I C A B D E F); 等角.
Qed.

Lemma 三角形内角和的唯一性 : forall A B C D E F D' E' F',
  三角形内角和 A B C D E F -> 三角形内角和 A B C D' E' F' -> 等角 D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' HTri HTri'.
  destruct HTri as [G [H [I [HSuma1 HSuma2]]]].
  destruct HTri' as [G' [H' [I' [HSuma1' HSuma2']]]].
  apply (和角的唯一性 G H I C A B); trivial.
  统计不重合点.
  apply (等角保持和角性质 G' H' I' C A B D' E' F'); 等角.
  apply (和角的唯一性 A B C B C A); trivial.
Qed.

Lemma 两三角形内角对应相等则内角和相等 : forall A B C D E F A' B' C', 三角形内角和 A B C D E F ->
  等角 A B C A' B' C' -> 等角 B C A B' C' A' -> 等角 C A B C' A' B' ->
  三角形内角和 A' B' C' D E F.
Proof.
  intros A B C D E F A' B' C' HTri HCongaB HCongaC HCongaA.
  destruct HTri as [G [H [I [HSuma HSuma']]]].
  统计不重合点; exists G; exists H; exists I; split;
  [apply (等角保持和角性质 A B C B C A G H I)|apply (等角保持和角性质 G H I C A B D E F)]; 等角.
Qed.

(** The sum of the angles of a degenerate triangle is a straight angle *)

Lemma 退化三角形的内角和为平角 : forall A B C P Q R, Col A B C -> 三角形内角和 A B C P Q R -> Bet P Q R.
Proof.
  intros A B C P Q R HCol HTri.
  destruct HTri as [D [E [F []]]].
  统计不重合点.
  destruct HCol as [|[|]].
  - apply (零角的等角是零角 A B C); auto.
    apply (角等的传递性 _ _ _ D E F).
    apply (任何角加上零角大小不变 _ _ _ B C A); try (apply bet_out); Between.
    apply (任何角加上零角大小不变 _ _ _ C A B); try (apply l6_6; apply bet_out); auto.
  - apply (零角的等角是零角 B C A); auto.
    apply (角等的传递性 _ _ _ D E F).
    apply (零角加上任何角后者大小不变 A B C); try (apply l6_6; apply bet_out); auto.
    apply (任何角加上零角大小不变 _ _ _ C A B); try (apply bet_out); Between.
  - apply (零角的等角是零角 C A B); auto.
    apply (零角加上任何角后者大小不变 D E F); auto.
    apply (l11_21_a B C A); try (apply l6_6; apply bet_out); auto.
    apply (零角加上任何角后者大小不变 A B C); try (apply bet_out); Between.
Qed.

(** Decidability properties *)

Lemma 和角的决定性 : forall A B C D E F G H I, 和角 A B C D E F G H I \/ ~ 和角 A B C D E F G H I.
Proof.
  intros A B C D E F G H I.
  destruct(两点重合的决定性 A B).
    subst; right; intro; 统计不重合点; auto.
  destruct(两点重合的决定性 C B).
    subst; right; intro; 统计不重合点; auto.
  destruct(两点重合的决定性 D E).
    subst; right; intro; 统计不重合点; auto.
  destruct(两点重合的决定性 F E).
    subst; right; intro; 统计不重合点; auto.
  destruct (和角的存在性 A B C D E F) as [G' [H' [I']]]; auto.
  destruct(等角的决定性 G H I G' H' I') as [|HN等角].
    left; apply (等角保持和角性质 A B C D E F G' H' I'); 等角.
  right.
  intro.
  apply HN等角, (和角的唯一性 A B C D E F); auto.
Qed.

Lemma 和角不大于平角的决定性 : forall A B C D E F, 和角不大于平角 A B C D E F \/ ~ 和角不大于平角 A B C D E F.
Proof.
  intros A B C D E F.
  destruct(两点重合的决定性 A B).
    subst; right; intro; 统计不重合点; auto.
  assert(HA' := 构造对称点 A B).
  destruct HA' as [A'].
  统计不重合点.
  destruct(lea_dec D E F C B A') as [|HNlea].
    left; apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A'); Between.
  right.
  intro.
  apply HNlea, (用角度小于等于特征化和角不大于平角 A); Between.
Qed.

Lemma 三角形内角和的决定性 : forall A B C P Q R, 三角形内角和 A B C P Q R \/ ~ 三角形内角和 A B C P Q R.
Proof.
  intros A B C P Q R.
  destruct(两点重合的决定性 A B).
    subst; right; intros [D [E [F []]]]; 统计不重合点; auto.
  destruct(两点重合的决定性 B C).
    subst; right; intros [D [E [F []]]]; 统计不重合点; auto.
  destruct(两点重合的决定性 A C).
    subst; right; intros [D [E [F []]]]; 统计不重合点; auto.
  destruct (三角形内角和的存在性 A B C) as [D [E [F]]]; auto.
  destruct (等角的决定性 D E F P Q R) as [|HNCong].
    left; apply 等角保持三角形内角和性质 with D E F; assumption.
    right; intro; apply HNCong, (三角形内角和的唯一性 A B C); assumption.
Qed.

End Suma_2.

Hint Resolve 两直角之和不大于平角 两锐角之和不大于平角 锐角与直角之和不大于平角 三角形两内角之和小于平角_BC 平角为补角和 : suma.
