Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section triangle_playfair_bis.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma legendre_aux :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A B C P Q,
    Perp Q A P Q -> Perp P B P Q -> 严格平行 Q A P B ->
    严格平行 Q A P C -> OS P B Q C -> OS P Q C A -> OS P Q C B ->
    False.
Proof.
  intros greenberg triangle.
  intros A B C P Q HPerpAP HPerpBP HParAB HParAC HOS1 HOS2 HOS3.
  destruct (构造对称点 B P) as [B'].
  assert(H在角内 : 在角内 C Q P B) by Side.
  assert (~ Col P B C) by (apply one_side_not_col124 with Q, HOS1).
  assert (~ Col P Q C) by (apply one_side_not_col123 with A, HOS2).
  assert (~ Col P Q A) by (apply one_side_not_col124 with C, HOS2).
  assert(角度小于 B P C B P Q).
    apply 非边上角内点分角小于大角; [Col|apply l11_24_在角内的对称性, H在角内].
  assert(为锐角 B P C).
    exists B, P, Q; split; Perp.
  统计不重合点.
  destruct (greenberg P Q A B P C) as [R []]; Perp; Col.
  统计不重合点.
  assert(OS P Q R A) by (apply invert_one_side, out_one_side; Col).
  assert(OS P C Q R).
    apply l12_6, par_strict_col_par_strict with A; Par; Col.
  destruct (和角的存在性 B' P R P R Q) as [D [E [F Hsuma1]]]; auto.
  assert(Htri : 三角形内角和 R Q P D E F).
  { exists B', P, R; split; auto.
    apply (等角保持和角性质 B' P Q Q P R B' P R); try (apply 同角相等; auto).
    - exists R.
      assert (TS P Q R B'); [|repeat (split; 等角); Side; Cop].
      apply (l9_8_2 _ _ B).
        apply bet__ts; Between; apply one_side_not_col124 with C, HOS3.
      apply (one_side_transitivity _ _ _ A); [|Side].
      apply (one_side_transitivity _ _ _ C); Side.
    - apply l11_16_直角相等; auto; apply 直角的对称性.
        apply 直角边共线点也构成直角2 with B; Perp; Col.
        apply 直角边共线点也构成直角2 with A; Perp; Col.
  }
  destruct (和角的存在性 B' P R C P B) as [I [J [K Hsuma2]]]; auto.
  assert(~ Col R P B').
  { apply (par_not_col Q A); Col.
    apply par_strict_col_par_strict with B; Col.
  }
  assert(Hsuma3 : 和角 B' P R R P B B' P B) by (apply 中间性推出和角; Between).
  assert(Hsams3 : 和角不大于平角 B' P R R P B) by (apply 邻补角之和不大于平角; Between).
  assert(角度小于等于 C P B R P B).
  { apply 角度小于等于的交换性, 角内点分角小于等于大角1, os_ts__inangle.
    - apply l9_2, (l9_8_2 _ _ Q); trivial.
      apply invert_two_sides, 角端点在角内点与顶点连线两侧; Col.
    - apply (one_side_transitivity _ _ _ Q); trivial.
      apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Par; Col.
  }
  assert(Habs : 角度小于 D E F B' P B).
  { apply (lea456789_lta__lta _ _ _ I J K);
    [|apply (和角保持角度小于等于性质 B' P R C P B _ _ _ B' P R R P B); Lea].
    apply (角度一偏序一全序则和角保持全序 B' P R P R Q _ _ _ B' P R C P B); Lea.
    apply (角度小于等于保持和角不大于平角性质 _ _ _ _ _ _ B' P R R P B); Lea.
  }
  apply Habs.
  apply 和角推出不重合 in Hsuma1; 分离合取式.
  apply 成中间性三点组的角相等; Between.
  apply (triangle R Q P); auto.
Qed.

Lemma legendre_aux1 :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A1 A2 B1 B2 C1 C2 P,
    Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> 共面 A1 A2 B1 B2 ->
    Par A1 A2 C1 C2 -> Col P C1 C2 -> ~ TS B1 B2 A1 C1 ->
    Col C1 B1 B2.
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HNC HPB HCop HParAC HPC HNts.
  assert(HParAB : 严格平行 A1 A2 B1 B2)
    by (apply (col_cop_perp2__pars_bis P); Col).
  apply (par_not_col_strict _ _ _ _ P) in HParAC; Col.
  elim(共线的决定性 C1 B1 B2); auto.
  intro HC1NotB.
  exfalso.
  assert(P<>C1) by (intro; subst C1; Col).
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpBP]]]].
  assert(HQ := HPerpAP); auto.
  destruct HQ as [Q [_ [_ [HQP[HQA _]]]]].
  assert(P<>Q) by (intro; subst Q; Col).
  apply (与垂线共线之线也为垂线1 _ _ _ _ P Q) in HPerpAP; Col.
  apply (与垂线共线之线也为垂线1 _ _ _ _ P Q) in HPerpBP; Col.
  clear dependent P1.
  clear dependent P2.

  统计不重合点.
  assert(Hos : OS B1 B2 Q C1).
  { apply (one_side_transitivity _ _ _ A1).
    - destruct (两点重合的决定性 A1 Q).
        subst A1; apply one_side_reflexivity; auto; apply (par_strict_not_col_2 A2); Par.
      apply l12_6, par_strict_right_comm, (par_strict_col_par_strict _ _ _ A2); Col; Par.
    - apply cop_nts__os; Col; [|apply (par_strict_not_col_2 A2); Par].
      apply coplanar_pseudo_trans with A1 A2 P.
        assumption.
        apply 等价共面ABDC, col_cop__cop with B2; Col.
        apply 等价共面ABDC, col_cop__cop with B1; Col; Cop.
        Cop.
        apply 等价共面ABDC, col_cop__cop with C2; Col; Cop.
  }
  assert(~ Col Q C1 P) by (apply (par_not_col A1 A2); auto; apply par_strict_col_par_strict with C2; Col).
  assert(HQNotB : ~ Col B1 B2 Q) by (apply one_side_not_col123 with C1; auto).
  assert(HB3 : exists B3, Col B1 B2 B3 /\ OS P Q C1 B3).
  { destruct (共线的决定性 P Q B1);
    [|apply cop_not_par_same_side with P; Col; apply 等价共面CABD, coplanar_trans_1 with B2; Col; Cop].
    assert (P = B1) by (apply (l6_21_两线交点的唯一性 B1 B2 Q P); Col).
    treat_equalities.
    destruct (cop_not_par_same_side P Q B2 P P C1) as [B3 []]; Col; Cop.
    exists B3; split; Col.
  }
  destruct HB3 as [B3 []].
  assert(~ Col P Q B3) by (apply (one_side_not_col123 _ _ _ C1); Side).
  assert(HA3 : exists A3, Col A1 A2 A3 /\ OS P Q C1 A3).
  { assert (共面 A1 A2 C1 P) by (apply col_cop__cop with C2; Col; Cop).
    destruct (共线的决定性 P Q A1);
    [|apply cop_not_par_same_side with Q; Col; apply 等价共面ADCB, col_cop__cop with A2; Col; Cop].
    assert (Q = A1) by (apply (l6_21_两线交点的唯一性 A1 A2 P Q); Col).
    treat_equalities.
    destruct (cop_not_par_same_side P Q A2 Q Q C1) as [A3 []]; Col; Cop.
    exists A3; split; Col.
  }
  destruct HA3 as [A3 []].
  统计不重合点.
  apply (legendre_aux greenberg triangle A3 B3 C1 P Q); trivial.
    apply (与垂线共线之线也为垂线2 A1 A2); Col.
    apply (与垂线共线之线也为垂线2 B1 B2); Col.
    apply (par_strict_col4__par_strict A1 A2 B1 B2); Col.
    apply (par_strict_col4__par_strict A1 A2 C1 C2); Col.
    apply (col2_os__os B1 B2); Col.
Qed.

Lemma legendre_aux2 :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A1 A2 B1 B2 C1 C2 P,
    Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> 共面 A1 A2 B1 B2 ->
    Par A1 A2 C1 C2 -> Col P C1 C2 ->
    Col C1 B1 B2. (** "half" of playfair_bis *)
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HNC HPB HCop HParAC HPC.
  assert(HParAB : 严格平行 A1 A2 B1 B2)
    by (apply (col_cop_perp2__pars_bis P); Col).
  apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C2 P); auto.
  intro Hts.
  assert(HC1NotB : ~ Col C1 B1 B2) by (destruct Hts as [_ []]; auto).
  assert(C1<>P) by (intro; subst C1; Col).
  destruct (构造对称点 C1 P) as [C3].
  统计不重合点.
  assert(HC3NotB : ~ Col C3 B1 B2) by (intro; apply HC1NotB; ColR).
  apply HC3NotB.
  apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C1 P); Col.
  - apply par_right_comm.
    apply (par_col_par _ _ _ P); Col.
    apply (par_col_par _ _ _ C2); Col.
  - apply l9_9_bis.
    exists C1.
    repeat (split; [assumption|]).
    exists P.
    split; Between.
Qed.

Lemma triangle__playfair_bis :
  greenberg_s_axiom ->
  triangle_postulate ->
  alternative_playfair_s_postulate.
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P.
  split.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C2 P); auto.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C1 P); Par; Col.
Qed.

End triangle_playfair_bis.