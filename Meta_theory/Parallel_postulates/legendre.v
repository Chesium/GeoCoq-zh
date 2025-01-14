Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_ID.
Require Export GeoCoq.Meta_theory.Parallel_postulates.TCP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_proclus.
Require Export GeoCoq.Meta_theory.Continuity.angle_archimedes.
Require Export GeoCoq.Meta_theory.Continuity.archimedes.
Require Export GeoCoq.Meta_theory.Continuity.aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_5_original_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_triangle_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_TCP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_bis_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_universal_posidonius_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_existential_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.universal_posidonius_postulate_par_perp_perp.
Require Export GeoCoq.Tarski_dev.Annexes.defect.

Section Legendre.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Theorem stronger_legendre_s_first_theorem :
  aristotle_s_axiom ->
  forall A B C D E F,
    和角 C A B A B C D E F ->
    和角不大于平角 D E F B C A.
Proof.
  intros ari A B C D E F.
  apply (t22_20 (aristotle__obtuse_case_elimination ari)).
Qed.

Theorem legendre_s_first_theorem :
  archimedes_axiom ->
  forall A B C D E F,
    和角 C A B A B C D E F ->
    和角不大于平角 D E F B C A.
Proof.
  intros archi A B C D E F.
  apply (t22_20 (archi__obtuse_case_elimination archi)).
Qed.

Theorem legendre_s_second_theorem :
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights ->
  triangle_postulate.
Proof.
  intro H; exact (rah__triangle (existential_triangle__rah H)).
Qed.

Lemma legendre_s_third_theorem_aux :
  aristotle_s_axiom ->
  triangle_postulate ->
  euclid_s_parallel_postulate.
Proof.
  intros HA HT.
  apply aristotle__greenberg in HA.
  apply triangle__playfair_bis in HT; trivial.
  apply playfair_bis__playfair in HT.
  apply euclid_5__original_euclid, tarski_s_euclid_implies_euclid_5.
  apply triangle_circumscription_implies_tarski_s_euclid.
  apply inter_dec_plus_par_perp_perp_imply_triangle_circumscription.
  { apply strong_parallel_postulate_implies_inter_dec.
    apply proclus_s_postulate_implies_strong_parallel_postulate.
    apply alternate_interior__proclus; trivial.
    apply playfair__alternate_interior, HT.
  }
  apply universal_posidonius_postulate__perpendicular_transversal_postulate.
  apply playfair__universal_posidonius_postulate, HT.
Qed.

Theorem legendre_s_third_theorem :
  archimedes_axiom ->
  triangle_postulate ->
  euclid_s_parallel_postulate.
Proof.
  intros; apply legendre_s_third_theorem_aux; [apply t22_24|]; assumption.
Qed.

Lemma legendre_aux :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C D B1 C1 P Q R S T U V W X,
    ~ Col A B C -> 等角 A C B C B D ->
    Cong A C B D -> TS B C A D -> Out A B B1 -> Out A C C1 -> Bet B1 D C1 ->
    三角形内角和与平角之差 A B C P Q R -> 三角形内角和与平角之差 A B1 C1 S T U -> 和角 P Q R P Q R V W X ->
    和角不大于平角 P Q R P Q R /\ 角度小于等于 V W X S T U.
Proof.
  intros noah A B C D B1 C1 P Q R S T U V W X HNCol HConga HCong HTS HOutB HOutC HBet HDef HDef1 HSuma.
  destruct (l11_49 A C B D B C) as [HCong1 [HConga1 HConga2]]; 等角; Cong.
    统计不重合点; auto.
  assert (HPar : 严格平行 A C B D).
  { apply par_not_col_strict with B; Col.
    apply par_left_comm, l12_21_b; Side; 等角.
  }
  assert (HPar' : 严格平行 A B C D).
  { apply par_not_col_strict with C; Col.
    apply par_left_comm, l12_21_b; Side; 等角.
  }
  assert (HNCol2:= HPar'); assert (HNCol3 := HPar'); assert (HNCol4 := HPar').
  apply par_strict_not_col_2 in HNCol2; apply par_strict_not_col_3 in HNCol3; apply par_strict_not_col_4 in HNCol4.
  assert (HB : ~ Col B1 B D /\ TS B D B1 C1 /\ Bet A B B1).
  { 统计不重合点.
    apply par_strict_symmetry, (par_strict_col_par_strict B D A C C1) in HPar; Col.
    assert (HNCol' := par_strict_not_col_4 B D A C1 HPar).
    assert (B <> B1) by (intro; subst B1; apply HNCol'; Col).
    assert (~ Col B1 B D) by (intro; apply HNCol4; ColR).
    assert (TS B D B1 C1) by (repeat split; Col; exists D; Col).
    repeat (split; auto).
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with C1; Side.
  }
  destruct HB as [HNCol5 [HTS1 HBetB]].
  assert (HC : ~ Col C D B1 /\ C <> C1 /\ Bet A C C1).
  { 统计不重合点.
    apply par_strict_symmetry, (par_strict_col_par_strict C D A B B1) in HPar'; Col.
    assert (HNCol' := par_strict_not_col_4 C D A B1 HPar').
    assert (C <> C1) by (intro; subst C1; apply HNCol'; Col).
    repeat split; auto.
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with B1; Side.
    repeat split; Col.
      intro; apply HNCol3; ColR.
    exists D; Col.
  }
  destruct HC as [HNCol6 [HCC1 HBetC]].
  统计不重合点.
  destruct (ts2__ex_bet2 B C D B1) as [Z [HZ1 HZ2]].
    apply l9_8_2 with C1; Side; apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    { apply l9_31.
        apply l9_17 with C1; trivial.
        exists A; repeat split; Col; try (intro; apply HNCol; ColR);
        [exists B|exists C]; split; Col; Between.
      apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    }

  rename H into HAB1.
  destruct (三角形内角和与平角之差的存在性 A B1 C) as [G [H [I HDef2]]]; auto.
  destruct (三角形内角和与平角之差的存在性 B1 C C1) as [J [K [L HDef3]]]; auto.
  destruct (三角形内角和与平角之差的存在性 C B B1) as [M [N [O HDef4]]]; auto.
  destruct (三角形内角和与平角之差的存在性 B1 C D) as [A' [B' [C' HDef5]]]; auto.
  destruct (三角形内角和与平角之差的存在性 C D C1) as [D' [E' [F' HDef6]]]; auto.
  destruct (三角形内角和与平角之差的存在性 B1 B D) as [M' [N' [O' HDef7]]]; auto.
  assert (Hd := 三角形内角和与平角之差推点不重合 A B1 C G H I HDef2).
  assert (Hd2 := 三角形内角和与平角之差推点不重合 C B B1 M N O HDef4).
  assert (Hd3 := 三角形内角和与平角之差推点不重合 B1 C D A' B' C' HDef5).
  分离合取式; clean.
  destruct (和角的存在性 G H I A' B' C') as [G' [H' [I' HSuma1]]]; auto.
  destruct (和角的存在性 M N O A' B' C') as [J' [K' [L' HSuma2]]]; auto.

  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah A B1 C1 C G H I J K L S T U) as [HIsi3 HSuma3]; trivial.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah B1 C C1 D A' B' C' D' E' F' J K L) as [HIsi4 HSuma4]; trivial.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah A C B1 B P Q R M N O G H I) as [HIsi5 HSuma5]; trivial.
    apply 等价三角形内角和与平角之差排列ACB, HDef.
    apply 等价三角形内角和与平角之差排列ACB, HDef2.
  assert (HIsi1 : 和角不大于平角 G H I A' B' C').
    apply 角度小于等于保持和角不大于平角性质 with G H I J K L; Lea.
    apply 原角小于等于和角 with D' E' F'; trivial.
  assert (HIsi2 : 和角不大于平角 M N O A' B' C').
    apply 角度小于等于保持和角不大于平角性质 with G H I A' B' C'; Lea.
    apply 加角小于等于和角 with P Q R; trivial.
  assert (HSuma6 : 和角 G' H' I' D' E' F' S T U).
    apply 和角结合律2 with G H I A' B' C' J K L; trivial.
  assert (HIsi6 : 和角不大于平角 G' H' I' D' E' F').
    apply 和角不大于平角结合律2 with G H I A' B' C' J K L; trivial.
  assert (HSuma7 : 和角 P Q R J' K' L' G' H' I').
    apply 和角结合律1 with M N O A' B' C' G H I; trivial.
  assert (HIsi7 : 和角不大于平角 P Q R J' K' L').
    apply 和角不大于平角结合律1 with M N O A' B' C' G H I; trivial.
  destruct (t22_16_2_四边形内三角形内角和与平角之差的可加性 noah C B B1 D M' N' O' A' B' C' P Q R M N O Z J' K' L') as [HIsi8 HSuma8]; trivial.
    apply 等价三角形内角和与平角之差排列BCA, (等内角三角形内角和与平角之差相等 A B C); 等角.
    apply 等价三角形内角和与平角之差排列BCA, HDef5.
  assert (HLea : 角度小于等于 P Q R J' K' L') by (apply 原角小于等于和角 with M' N' O'; trivial).

  split.
    suma.统计不重合点.
    apply 角度小于等于保持和角不大于平角性质 with P Q R J' K' L'; Lea.
  apply 角度小于等于的传递性 with G' H' I'.
    apply 和角保持角度小于等于性质_右 with P Q R P Q R J' K' L'; trivial.
  apply 原角小于等于和角 with D' E' F'; trivial.
Qed.

Lemma legendre_aux1 : forall A B C B' C',
  ~ Col A B C -> Out A B B' -> Out A C C' ->
  exists D', 在角内 D' B A C /\ 等角 A C' B' C' B' D' /\
             Cong A C' B' D' /\ TS B' C' A D'.
Proof.
  intros A B C B' C' HNCol HOutB HOutC.
  统计不重合点.
  assert (HNCol' : ~ Col A B' C') by (intro; 统计不重合点; apply HNCol; ColR).
  destruct (中点的存在性 B' C') as [M HM].
  destruct (构造对称点 A M) as [D' HD].
  assert (HNCol1 : ~ Col A M B') by (intro; 统计不重合点; apply HNCol'; ColR).
  assert (HNCol2 : ~ Col D' B' C') by (intro; 统计不重合点; apply HNCol'; ColR).
  exists D'.
  统计不重合点; destruct HM; destruct HD; split.
    apply l11_25 with D' B' C'; try (apply out_trivial); auto.
    repeat split; auto.
    exists M; split; trivial.
    right; apply bet_out; auto.
  destruct (l11_49 A M C' D' M B') as [HCong1 [HConga1 HConga2]]; Cong.
    apply l11_14; Between.
  split.
    apply (l11_10 A C' M M B' D'); Out; 等角.
  split; Cong.
  repeat split; Col.
  exists M; split; Col.
Qed.

Lemma legendre_aux2 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C,
    ~ Col A B C ->  为锐角 B A C ->
    (forall T,
       在角内 T B A C ->
       exists X Y : Tpoint, Out A B X /\ Out A C Y /\ Bet X T Y) ->
    forall P Q R S T U,
      三角形内角和与平角之差 A B C P Q R -> 角度在对数刻度上 P Q R S T U ->
      exists B' C' P' Q' R',
        (Out A B B' /\ Out A C C' /\
         三角形内角和与平角之差 A B' C' P' Q' R' /\ 角度小于等于 S T U P' Q' R').
Proof.
  intros noah A B C HNCol H为锐角 legendre P Q R S T U HDef.
  induction 1; rename A0 into P; rename B0 into Q; rename C0 into R.
    exists B; exists C; exists P; exists Q; exists R; 统计不重合点.
    repeat (split; [Out|]); Lea.
  rename D into S; rename E into T; rename F into U.
  destruct IH角度在对数刻度上 as [B' [C' [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]]]]; trivial.
  destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
  assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
  destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
  assert (Hd := 三角形内角和与平角之差推点不重合 A B' C' P' Q' R' HDef'); 分离合取式; 统计不重合点.
  destruct (三角形内角和与平角之差的存在性 A B'' C'') as [P'' [Q'' [R'' HDef'']]]; auto.
    intro; subst; apply HNCol; ColR.
  exists B''; exists C''; exists P''; exists Q''; exists R''.
  repeat (split; trivial).
  destruct (和角的存在性 P' Q' R' P' Q' R') as [V [W [X HSuma1]]]; auto.
  destruct (legendre_aux noah A B' C' D' B'' C'' P' Q' R' P'' Q'' R'' V W X) as [HIsi1 HLea1]; trivial.
    apply l6_7 with B; Out.
    apply l6_7 with C; Out.
  apply 角度小于等于的传递性 with V W X; trivial.
  apply 和角保持角度小于等于性质 with S T U S T U P' Q' R' P' Q' R'; trivial.
Qed.

Lemma legendre_s_fourth_theorem_aux :
  archimedes_axiom ->
  legendre_s_parallel_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros archi legendre.
  destruct legendre as [B [A [C [HNCol [H为锐角 legendre]]]]].
  统计不重合点.
  destruct (三角形内角和与平角之差的存在性 A B C) as [P [Q [R HDef]]]; auto.
  destruct (共线的决定性 P Q R) as [HCol|HNCol1].
  - apply archi__obtuse_case_elimination in archi.
    apply (非退化三角形内角和与平角之差为零角蕴含直角萨凯里四边形假设 A B C P Q R); Col.
    apply not_bet_out; Col.
    intro HBet.
    apply HNCol.
    apply 等价三角形内角和与平角之差排列BAC in HDef.
    destruct HDef as [D [E [F [[G [H [I [HSuma1 HSuma2]]]] HSuppa]]]].
    apply out_col, l6_6, out_lea__out with D E F.
      apply (bet_suppa__out P Q R); [|apply suppa_sym]; assumption.
    apply 加角小于等于和角 with G H I; trivial.
    apply (t22_20 archi); trivial.
  - destruct (archi__gradaexp_destruction archi P Q R HNCol1) as [S [T [U [HGAE H为钝角]]]].
    apply archi__obtuse_case_elimination in archi.
    apply 共线否定排列BAC in HNCol.
    destruct (legendre_aux2 archi A B C HNCol H为锐角 legendre P Q R S T U HDef HGAE) as [B' [C' HInter]].
    destruct HInter as [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]].
    apply (一角小于等于钝角则该角为钝角 P' Q' R'), 钝角的倍角大于平角 in H为钝角; auto.
    exfalso.
    apply H为钝角.
    destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
    assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
    destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
    统计不重合点.
    destruct (三角形内角和与平角之差的存在性 A B'' C'') as [S' [T' [U' HDef'']]]; auto.
      intro; subst; apply HNCol; ColR.
    destruct (和角的存在性 P' Q' R' P' Q' R') as [V [W [X HSuma]]]; auto.
    destruct (legendre_aux archi A B' C' D' B'' C'' P' Q' R' S' T' U' V W X); trivial;
    [apply l6_7 with B|apply l6_7 with C]; Out.
Qed.

Theorem legendre_s_fourth_theorem :
  archimedes_axiom ->
  legendre_s_parallel_postulate ->
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights.
Proof.
  intros; apply triangle__existential_triangle, rah__triangle, legendre_s_fourth_theorem_aux; assumption.
Qed.

End Legendre.