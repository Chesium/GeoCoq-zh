Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch13_1.
Require Import GeoCoq.Meta_theory.Continuity.grad.

(** This development is inspired by The Foundations of Geometry and the Non-Euclidean Plane, by George E Martin, chapter 22 *)

Section Archimedes.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.


(** For every m, there exists n such that A0Dm = A0An - E0En = n(A0A1 - E0E1) (m=n) *)
Lemma t22_18_aux1 : forall A0 A1 E0 E1 D1 D,
  Bet A0 D1 A1 -> Cong E0 E1 A1 D1 ->
  Grad A0 D1 D ->
  exists A E, 在同样的线性刻度上 A0 A1 A E0 E1 E /\ Cong E0 E A D /\ Bet A0 D A.
Proof.
  intros A0 A1 E0 E1 D1 D HBet HCong HG.
  induction HG.
    exists A1; exists E1; repeat split; auto; apply 双重线性刻度_初始化.
  rename A into A0.
  rename B into C1.
  destruct IHHG as [A [E [HG2 [HCong2 HBet2]]]]; auto.
  destruct (由一点往一方向构造等长线段 A0 A A0 A1) as [A' [HBet3 HCong3]].
  destruct (由一点往一方向构造等长线段 E0 E E0 E1) as [E' [HBet4 HCong4]].
  exists A'; exists E'.
  assert(HBet5 : Bet A0 C' A').
  { assert(HBet5 : Bet A0 C A') by eBetween.
    assert(Bet C C' A'); [|eBetween].
    apply grad2__grad123 in HG2.
    apply grad__bet in HG.
    apply grad__bet in HG2.
    elim(两点重合的决定性 A0 C).
      intro; treat_equalities; Between.
    intro.
    elim(两点重合的决定性 C C').
      intro; treat_equalities; Between.
    intro.
    elim(两点重合的决定性 A' C).
      intro; subst A'; assert (A=C) by (apply (双中间性推出点重合 _ _ A0); Between); treat_equalities; Between.
    intro.
    apply l6_13_1.
      destruct (l6_2 C' A' A0 C); Between.
    apply (长度小于等于的传递性 _ _ A A').
      apply (l5_6_等长保持小于等于关系 A0 C1 A0 A1); Cong; exists C1; split; Cong.
    destruct(l5_12_a C A A'); eBetween.
  }
  repeat split; auto.
    apply 双重线性刻度_步进 with A E; Cong.
  assert (HD : Le E0 E1 A A').
    apply (l5_6_等长保持小于等于关系 E0 E1 A1 A0); Cong; exists C1; split; Between.
  destruct HD as [D [HBet6 HCong6]].
  apply (等长的传递性 _ _ C D).
    apply (两组连续三点分段等则全体等 _ E _ _ A); Cong; eBetween; apply 等长的传递性 with E0 E1; trivial.
  assert (Bet C D A') by eBetween.
  apply (l4_3 _ _ A' _ _ C); Cong; eBetween.
  apply (等长的传递性 _ _ A0 C1); Cong.
  apply 等长的左交换性; apply (l4_3 _ _ A _ _ A1); Between; Cong.
  apply 等长的传递性 with E0 E1; Cong.
Qed.

(** For every n, B0Bn is lower than or equal to n times B0B1 *)
Lemma t22_18_aux2 : forall A0 A1 B0 B1 A B E,
  萨凯里四边形 A0 B0 B1 A1 ->
  在同样的线性刻度上 A0 A1 A B0 B1 E -> 萨凯里四边形 A0 B0 B A -> Le B0 B B0 E.
Proof.
  intros A0 A1 B0 B1 A B E HSac1 HG.
  revert B.
  induction HG; rename A into A0; rename B into A1; rename D into B0; rename E into B1.
  { intros B HSac.
    assert(B = B1); [|subst B; Le].
    assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac1); unfold 萨凯里四边形 in *; 分离合取式.
    apply (l6_11_uniqueness A1 A0 B0 B1); Cong; [|apply out_trivial; auto].
    apply (col_one_side_out _ A0).
      apply 等价共线CAB, cop_per2__col with A0; Perp.
      apply 等价共面ACDB, coplanar_trans_1 with B0; Cop.
      apply 共线否定排列CAB, one_side_not_col123 with B1; assumption.
    apply (one_side_transitivity _ _ _ B0); Side.
  }
  rename C into A; rename F into E; rename C' into A'; rename F' into E'.
  intros B' HSac'.
  assert (A0 <> A).
  { intro; treat_equalities.
    assert (A0 = A1) by (apply 中间性的同一律, grad__bet, (grad2__grad123 _ _ _ B0 B1 E); auto).
    treat_equalities.
    apply sac_distincts in HSac1; 分离合取式; auto.
  }
  assert (HB : exists B, 萨凯里四边形 A0 B0 B A).
  { clear dependent A'; clear dependent B'; clear IHHG.
    apply grad2__grad123 in HG.
    apply grad__bet in HG.
    destruct (l10_15 A0 A1 A B0) as [P [HPerp HOS]]; Col.
      apply par_strict_not_col_1 with B1, sac__pars1423, HSac1.
    destruct (l6_11_existence A A0 B0 P) as [B [HOut Hcong5]].
      统计不重合点; auto.
      assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac1); 分离合取式; auto.
    exists B.
    unfold 萨凯里四边形 in *; 分离合取式; 统计不重合点.
    repeat split; Cong.
    - apply (直角边共线点也构成直角2 _ _ A1); Col.
    - apply L形垂直转直角2, (垂线共线点也构成垂直2 _ _ _ P); Col.
      apply 垂直的交换性; apply (垂线共线点也构成垂直1 _ A1); Col.
    - apply invert_one_side.
      apply (out_out_one_side _ _ _ P); [|apply l6_6; auto].
      apply invert_one_side.
      apply (col_one_side _ A1); Col.
  }
  destruct HB as [B HSac].
  assert (HLe := HSac).
  apply IHHG in HLe; auto.
  clear IHHG.
  destruct (由一点往一方向构造等长线段 B0 B E E') as [C [HBet HCong]].
  assert (Cong B0 B1 B B').
    apply (cong2_sac2__cong A0 B0 B1 A1 A _ _ A'); auto; [|unfold 萨凯里四边形 in *; 分离合取式; Cong].
    apply cop_sac2__sac with A0 B0; Cop.
    intro; treat_equalities; apply sac_distincts in HSac1; 分离合取式; auto.
  apply (长度小于等于的传递性 _ _ B0 C).
    apply (triangle_inequality B0 B B' C); trivial.
    apply 等长的传递性 with E E'; Cong.
    apply 等长的传递性 with B0 B1; Cong.
  apply (bet2_le2__le1346 _ B _ _ E); Le.
Qed.

Lemma t22_18 :
  archimedes_axiom ->
  forall A0 B0 B1 A1, 萨凯里四边形 A0 B0 B1 A1 -> ~ Lt B0 B1 A1 A0.
Proof.
  intros Harchi A0 B0 B1 A1 HSac.
  intro Hlt.
  destruct Hlt as [Hle HNcong].
  destruct Hle as [D1 [Hbet Hcong]].
  destruct (由一点往一方向构造等长线段 A0 D1 A0 B0) as [C0 [Hbet2 Hcong2]].
  destruct (由一点往一方向构造等长线段 A0 C0 A0 B0) as [C [Hbet3 Hcong3]].
  assert(H : forall D, Grad A0 D1 D -> Lt A0 D A0 C).
  { intros D HG.
    destruct (t22_18_aux1 A0 A1 B0 B1 D1 D) as [A [E [HG2 [Hcong4 Hbet4]]]]; Between.
    assert (Hbet5 := grad2__grad123 A0 A1 A B0 B1 E HG2).
    apply grad__bet in Hbet5.
    destruct (l10_15 A0 A1 A B0) as [P [HPerp HOS]].
      Col.
      apply par_strict_not_col_1 with B1, sac__pars1423, HSac.
    destruct (l6_11_existence A A0 B0 P) as [B [HOut Hcong5]].
      统计不重合点; auto.
      assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac); 分离合取式; auto.
    assert(HSac2 : 萨凯里四边形 A0 B0 B A).
    { unfold 萨凯里四边形 in *; 分离合取式; 统计不重合点; assert(A0 <> A) by (intro; treat_equalities; auto).
      repeat split; Cong.
      - apply (直角边共线点也构成直角2 _ _ A1); Col.
      - apply L形垂直转直角2, (垂线共线点也构成垂直2 _ _ _ P); Col.
        apply 垂直的交换性, (垂线共线点也构成垂直1 _ A1); Col.
      - apply invert_one_side.
        apply (out_out_one_side _ _ _ P); [|apply l6_6; auto].
        apply invert_one_side.
        apply (col_one_side _ A1); Col.
    }
    assert(HLe : Le B0 B B0 E) by (apply (t22_18_aux2 A0 A1 B0 B1 A); auto).
    assert (HLe2 : Le B0 B A A0).
      apply (长度小于等于的传递性 _ _ B0 E); auto.
      apply (l5_6_等长保持小于等于关系 A D A A0); Cong.
      destruct (l5_12_a A D A0); Between.
    assert (HLe2' := HLe2).
    destruct HLe2' as [Q [Hbet6 Hcong6]].
    apply (长度小于等于_小于_传递性 _ _ A0 Q).
      apply (bet2_le2__le1245 _ _ A _ _ A); Between; Le.
      apply (l5_6_等长保持小于等于关系 B0 B B0 E); Cong.
    clear dependent D; clear dependent E.
    destruct (l6_11_existence A0 A0 B0 A) as [B0' [HOut2 Hcong4]];
      try (统计不重合点; intro; treat_equalities; auto).
    destruct (由一点往一方向构造等长线段 A0 B0' B0 B) as [B' [Hbet7 Hcong7]].
    destruct (由一点往一方向构造等长线段 B0' B' B A) as [A' [Hbet8 Hcong8]].
    assert (Le A0 A A0 A'). (** A0A' = A0B0 + B0B + BA *)
    { destruct (由一点往一方向构造等长线段 A0 B0' B0 A) as [B'' [Hbet9 Hcong9]].
      apply (长度小于等于的传递性 _ _ A0 B'').
        apply (triangle_inequality_2 _ B0 _ _ B0'); Cong.
      apply (bet2_le2__le1346 _ B0' _ _ B0'); Le.
        apply (中间性的外传递性2 _ _ B'); auto.
        intro; treat_equalities; apply sac_distincts in HSac2; 分离合取式; auto.
      apply (l5_6_等长保持小于等于关系 B0 A B0' A'); Cong.
      apply (triangle_inequality_2 _ B _ _ B'); Cong.
    }
    assert (HLe3 : Le B0 B A' B0').
      apply (l5_6_等长保持小于等于关系 B0' B' B0' A'); Cong; destruct (l5_12_a B0' B' A'); auto.
    destruct HLe3 as [Q' [Hbet9 Hcong9]].
    assert (HBet10 : Bet A0 B0' A').
      apply sac_distincts in HSac2; 分离合取式; 统计不重合点.
      apply (中间性的外传递性2 _ _ B'); Between.
    apply (长度小于等于_小于_传递性 _ _ A0 Q').
      apply (bet2_le2__le1245 _ _ A' _ _ A); eBetween.
      apply 等长则小于等于; apply (等长的传递性 _ _ B0 B); Cong.
    assert (Cong B0' Q' A0 B0).
    { apply (等长的传递性 _ _ A B); Cong.
      apply (等长的传递性 _ _ A' B'); Cong.
      assert(Hcong10 : Cong B0' B' A' Q') by (apply (等长的传递性 _ _ B0 B); auto).
      elim(中间性的决定性 B0' Q' B').
        intro; apply (l4_3 _ _ B' _ _ Q'); Cong; eBetween.
      intro HNBet.
      apply sac_distincts in HSac2; 分离合取式; 统计不重合点.
      assert (Q' <> B0') by (intro; subst; apply HNBet; Between).
      assert (A' <> B0') by (intro; treat_equalities; auto).
      assert (HOut3 : Out B0' B' Q').
       apply (l6_7 _ _ A'); [| apply l6_6]; apply bet_out; Between.
      assert (Hbet11 : Bet B0' B' Q').
        apply out2__bet; auto.
        apply not_bet_out; Col.
      apply (两组连续三点分段等则全体等 _ B' _ _ Q'); Cong; eBetween.
    }
    assert (Hbet10 : Bet A0 D1 C) by eBetween.
    apply (等长保持小于关系 D1 C A0 C); Cong; [split|].
      destruct (l5_12_a A0 D1 C); auto.
      intro; assert (D1 = A0) by (apply (between_cong C); Between; Cong); treat_equalities; Cong.
    apply (两组连续三点分段等则全体等 _ C0 _ _ B0'); eBetween; apply 等长的传递性 with A0 B0; Cong.
  }
  unfold archimedes_axiom in *.
  specialize Harchi with A0 D1 A0 C.
  destruct Harchi as [D [HG Hle]].
    intro; treat_equalities; auto.
  assert(HLt := HG).
  apply H in HLt.
  apply grad__le in HG.
  apply (长度小于等于推出反向不小于 A0 C A0 D); auto.
Qed.

Lemma t22_19 :
  archimedes_axiom ->
  forall A B C D, 萨凯里四边形 A B C D -> ~ 为钝角 A B C.
Proof.
  intros archi A B C D HSac HObt.
  assert (H := t22_18 archi _ _ _ _ (sac_perm _ _ _ _ HSac)).
  apply H.
  apply 长度小于的左交换性; apply <- lt_sac__obtuse; auto.
Qed.

Lemma archi__obtuse_case_elimination :
  archimedes_axiom ->
  ~ 钝角萨凯里四边形假设.
Proof.
  intros archi obtuse.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  absurd(为钝角 A B C).
    apply t22_19 with D; trivial.
    apply obtuse with D; trivial.
Qed.

Lemma t22_23_aux :
  forall A B C M N L,
    ~ Col A M N -> Per B C A -> A <> C -> 中点 M A B ->
    Per M N A -> Col A C N ->
    中点 M N L -> Bet A N C /\ Lambert四边形 N L B C /\ Cong B L A N.
Proof.
  intros A B C M N L HNCol HPerC HAC HM HPerN HColN HN.
  统计不重合点.
  assert (HBet : Bet A N C) by (apply per23_preserves_bet with M B; Perp; Col; Between).
  destruct (l11_49 A M N B M L) as [HCong1 [H等角1 H等角2]]; auto with cong.
    apply l11_14; Between.
  assert(B <> L) by (intro; treat_equalities; auto).
  repeat split; Cong.
  - intro; treat_equalities; apply HNCol; ColR.
  - intro; treat_equalities; apply H6.
    apply (l6_21_两线交点的唯一性 A M N M); Col.
    apply 等价共线CBA, cop_per2__col with A; Col; Cop.
  - apply 直角边共线点也构成直角2 with A; Col.
    apply 直角的对称性, 直角边共线点也构成直角2 with M; Col; Perp.
  - apply 直角的对称性, 直角边共线点也构成直角2 with A; Col.
  - apply l11_17_等于直角的角是直角 with M N A; auto.
    apply (l11_10 M N A M L B); auto; try (apply out_trivial; auto).
    apply l6_6, bet_out; Between.
  - apply 等价共面CDAB, col_cop__cop with M; Col.
    apply 等价共面CABD, col_cop__cop with A; Col; Cop.
Qed.

Lemma t22_23 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C M N L,
    ~ Col A M N -> Per B C A -> A <> C -> 中点 M A B ->
    Per M N A -> Col A C N -> 中点 M N L ->
    Bet A N C /\ Le N C A N /\ Le L N B C.
Proof.
  intros HNob A B C M N L HNCol HPerC HAC HM HPerN HColN HN.
  destruct (t22_23_aux A B C M N L) as [HBet [HLam HCong]]; auto.
  split; auto.
  assert (HLBC : ~ 为钝角 L B C) by (intro; apply HNob, (lam_obtuse__oah N L B C); trivial).
  assert (Hos1 : OS N L B C) by (apply lam__os; trivial).
  assert (Hos2 : OS N C B L) by (apply lam__os, lam_perm; trivial).
  unfold Lambert四边形 in HLam; 分离合取式.
  destruct (angle_partition L B C) as [H为锐角 | [HPer | H为钝角]]; trivial; [ | | exfalso; auto].
  - split; apply 长度小于蕴含小于等于; [apply (等长保持小于关系 N C B L); Cong | ].
      apply lta_os_per2__lt; Perp; Side; apply 角度小于的左交换性, acute_per__lta; auto.
    apply 长度小于的左交换性, lta_os_per2__lt; Side; apply acute_per__lta; auto.
  - split; apply 等长则小于等于; [apply 等长的传递性 with B L; trivial | apply 等长的左交换性];
    apply conga_per2_os__cong; Perp; Side; apply l11_16_直角相等; Perp.
Qed.

(** For every n, 2^n times B0C0 is lower than or equal to BnCn *)
(** B0 is introduced twice for the induction tactic to work properly *)
Lemma t22_24_aux :
  ~ 钝角萨凯里四边形假设 ->
  forall A B0 B00 C0 B C E,
    ~ Col A B0 C0 -> Perp A C0 B0 C0 -> B0 = B00 ->
    在同样的对数刻度上 A B0 B B00 C0 E -> Perp A C0 B C -> Col A C0 C ->
    Le B0 E B C.
Proof.
  intros HNob A B0 B00 C0 B C E HNCol HPerp0 Heq HGE.
  revert C.
  induction HGE; rename B into B0; rename D into B00; rename E into C0; subst B00.
    intros C HPerp HCol; assert (C = C0) by (apply (l8_18_过一点垂线之垂点的唯一性 A C0 B0); Col); subst C; Le.
  rename C into B; rename C' into B'; rename F into E; rename F' into E'.
  intros C' HPerp' HCol'.
  apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE.
  destruct (l8_18_过一点垂线之垂点的存在性 A C0 B) as [C [HCol HPerp]].
    intro; 统计不重合点; apply HNCol; ColR.
  assert (HLe : Le B0 E B C) by (apply IHHGE; trivial).
  clear IHHGE.
  destruct (构造对称点 C B) as [D HD].
  apply 长度小于等于的传递性 with D C.
    apply bet2_le2__le1346 with E B; Between; apply (l5_6_等长保持小于等于关系 B0 E B C); auto with cong.
  assert (HAC : A <> C).
  { intro; subst C; 统计不重合点; assert (A = C0); auto.
    apply (l8_18_过一点垂线之垂点的唯一性 A C0 B0); Col.
    apply 垂直的右交换性, 垂线共线点也构成垂直2 with B; Perp; Col.
  }
  assert (HAC' : A <> C').
  { intro; subst C'; 统计不重合点; assert (A = C0); auto.
    apply (l8_18_过一点垂线之垂点的唯一性 A C0 B0); Col.
    apply 垂直的右交换性, 垂线共线点也构成垂直2 with B'; Perp; ColR.
  }
  assert (HPer : Per A C B) by (apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with C0; assumption).
  destruct (t22_23 HNob A B' C' B C D) as [_ []]; Perp.
  - 统计不重合点; apply 成直角三点不共线 in HPer; Col.
  - apply L形垂直转直角1, 垂线共线点也构成垂直2 with C0; Perp.
  - split; auto.
  - ColR.
Qed.

(** For every n, it is possible to get Bn and Cn *)
Lemma t22_24_aux1 : forall A B0 C0 E,
  ~ Col A B0 C0 -> Perp A C0 B0 C0 -> 在对数刻度上 B0 C0 E ->
  exists B C, 在同样的对数刻度上 A B0 B B0 C0 E /\ Perp A C0 B C /\ Col A C0 C.
Proof.
  intros A B0 C0 E HNCol HPerp0 HGE.
  induction HGE; rename A0 into B0; rename B into C0.
    exists B0; exists C0; repeat (split; Col); apply 双重对数刻度_初始化.
  rename C into E; rename C' into E'.
  destruct IHHGE as [B [C [HGE2 [HPerp HCol]]]]; trivial.
  destruct (由一点往一方向构造等长线段 A B A B) as [B' [HBet HCong]].
  exists B'.
  destruct (l8_18_过一点垂线之垂点的存在性 A C0 B') as [C' [HCol' HPerp']].
    apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE2; intro; 统计不重合点; apply HNCol; ColR. 
  exists C'; repeat (split; trivial); apply 双重对数刻度_步进 with B E; Cong.
Qed.

Lemma t22_24 : archimedes_axiom -> aristotle_s_axiom.
Proof.
  intros Harchi P Q D A B0 HNCol HACute0.
  destruct (l8_18_过一点垂线之垂点的存在性 A D B0) as [C0 [HColD HPerpD]]; Col.
  assert (HAC0 : A <> C0) by (intro; subst C0; apply (acute_not_per D A B0); Perp).
  assert (HNCol0 : ~ Col A B0 C0) by (intro; apply HNCol; ColR).
  assert (HPerp0 := 垂线共线点也构成垂直1 A D B0 C0 C0 HAC0 HPerpD HColD).
  elim (两点重合的决定性 P Q); intro HPQ.
  { subst Q; exists C0; exists B0; split; 统计不重合点.
      apply l6_6, acute_col_perp__out with B0; trivial; apply 为锐角的对称性; trivial.
    split.
      apply out_trivial; auto.
    repeat split; Perp; Le.
    intro; treat_equalities; auto.
  }
  destruct (由一点往一方向构造等长线段 P Q P Q) as [Q' [HBetQ HCongQ]].
  destruct (reach__ex_gradexp_le B0 C0 P Q') as [E [HGE HLe]].
    统计不重合点; apply Harchi; trivial.
  destruct (t22_24_aux1 A B0 C0 E) as [B [C [HGE2 [HPerp HCol]]]]; trivial.
  assert(HOut : Out A B0 B).
    apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE2; 统计不重合点; apply bet_out; auto.
  assert(H为锐角 : 为锐角 D A B).
    apply (acute_conga__acute D A B0); trivial.
    apply l6_6 in HOut.
    统计不重合点; apply out2__conga; auto; apply out_trivial; auto.
  assert (HAC : A <> C) .
    intro; subst C; 统计不重合点; apply (acute_not_per D A B); trivial.
    apply L形垂直转直角1, 垂线共线点也构成垂直1 with C0; Col.
  exists C, B; split.
    统计不重合点; apply l6_6, acute_col_perp__out with B; [apply 为锐角的对称性; trivial|ColR|apply 垂线共线点也构成垂直1 with C0; Col].
  split; trivial; split.
    apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with C0; trivial.
  apply 长度小于_小于等于_传递性 with P Q'.
  split.
    apply bet__le1213; trivial.
    intro; assert (Q = Q'); [|treat_equalities; auto].
    apply between_cong with P; assumption.
  apply 长度小于等于的传递性 with B0 E; trivial.
  apply 长度小于等于的右交换性.
  apply t22_24_aux with A B0 C0; trivial.
  apply archi__obtuse_case_elimination; assumption.
Qed.


End Archimedes.