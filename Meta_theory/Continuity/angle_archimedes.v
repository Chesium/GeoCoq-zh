Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.archimedes.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

(** This development is inspired by the proof of Lemma 35.1 in Geometry: Euclid and Beyond, by Robin Hartshorne *)

Section Archimedes_for_angles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma grada_distincts : forall A B C D E F,
  角度在线性刻度上 A B C D E F ->
  A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
  induction 1.
    assert_diffs; repeat split; trivial.
  apply suma_distincts in H2; spliter; repeat split; auto.
Qed.

Lemma conga2_grada__grada : forall A B C D E F A' B' C' D' E' F',
  角度在线性刻度上 A B C D E F ->
  等角 A B C A' B' C' -> 等角 D E F D' E' F' ->
  角度在线性刻度上 A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HGA.
  revert A' B' C' D' E' F'.
  induction HGA; intros A' B' C' D' E' F' Hconga1 Hconga2.
    apply 角度线性刻度_初始化, 角等的传递性 with D E F; trivial; apply 角等的传递性 with A B C; 等角.
  suma.assert_diffs.
  assert (Hconga3 : 等角 D E F D E F) by 等角.
  apply 角度线性刻度_步进 with D E F.
    apply (IHHGA A' B' C' D E F); trivial.
    apply (conga2_sams__sams D E F A B C); trivial.
  apply (等角保持和角 D E F A B C G H I); trivial.
Qed.

Lemma grada__lea : forall A B C D E F, 角度在线性刻度上 A B C D E F -> 角度小于等于 A B C D E F.
Proof.
  intros A B C D E F.
  induction 1.
    Lea.
  apply lea_trans with D E F; trivial.
  apply sams_suma__lea123789 with A B C; trivial.
Qed.

Lemma grada_out__out : forall A B C D E F,
  Out E D F -> 角度在线性刻度上 A B C D E F ->
  Out B A C.
Proof.
  intros A B C D E F Hout HGA.
  apply out_lea__out with D E F; trivial.
  apply grada__lea; trivial.
Qed.

Lemma grada2_sams_suma__grada : forall A B C D E F G H I K L M,
  角度在线性刻度上 A B C D E F -> 角度在线性刻度上 A B C G H I ->
  角度之和小于平角 D E F G H I -> 和角 D E F G H I K L M ->
  角度在线性刻度上 A B C K L M.
Proof.
  intros A B C D E F G H I K L M HGA1 HGA2 HIsi.
  revert K L M.
  induction HGA2.
  { rename H into HConga; rename D0 into G; rename E0 into H; rename F0 into I.
    intros K L M HSuma.
    suma.assert_diffs.
    apply (conga2_sams__sams D E F G H I D E F A B C) in HIsi; 等角.
    apply (等角保持和角 D E F G H I K L M D E F A B C K L M) in HSuma; 等角.
    apply 角度线性刻度_步进 with D E F; trivial.
  }
  assert (Hd1 := sams_distincts D0 E0 F0 A B C H0); assert (Hd2 := sams_distincts D E F G H I HIsi); spliter.
  destruct (和角的存在性 D E F D0 E0 F0) as [K [L [M HSuma]]]; auto.
  intros K0 L0 M0 HSuma2.
  assert (HIsi2 : 角度之和小于平角 D E F D0 E0 F0).
    apply sams_lea2__sams with D E F G H I; Lea.
    apply sams_suma__lea123789 with A B C; trivial.
  apply 角度线性刻度_步进 with K L M.
    apply IHHGA2; trivial.
    apply sams_assoc_2 with D E F D0 E0 F0 G H I; trivial.
  apply suma_assoc_2 with D E F D0 E0 F0 G H I; trivial.
Qed.

Lemma gradaexp__grada : forall A B C D E F,
  角度在对数刻度上 A B C D E F -> 角度在线性刻度上 A B C D E F.
Proof.
  intros A B C.
  induction 1; [apply 角度线性刻度_初始化 | apply grada2_sams_suma__grada with D E F D E F]; trivial.
Qed.

Lemma acute_archi_aux : forall O A B C D E,
  Per O A B -> O <> A -> B <> A -> C <> D -> D <> E ->
  Bet A C D -> Bet C D E -> Bet D E B -> 等角 C O D D O E ->
  Lt C D D E.
Proof.
  intros O A B C D E HPer HOA HBA HCD HDE HBet1 HBet2 HBet3 H等角.
  assert_diffs.
  assert (HNCol1 : ~ Col O A B) by (apply 成直角三点不共线; auto).
  assert (HNCol2 : ~ Col O A D).
    assert_cols; intro; elim (两点重合的决定性 A C); intro; [treat_equalities|]; apply HNCol1; ColR.
  destruct (给定角一边可作出与给定点同侧一点构成等角_非平角 A D O O D E) as [P [HP1 HP2]]; Col.
    intro; apply HNCol2; ColR.
  assert (H为锐角 : 为锐角 A D O).
    apply l11_43_aux; Col; left; apply 直角的对称性, 直角边共线点也构成直角2 with B; auto; ColR.
  assert (HF : 在角内 P O D E).
  { apply lea_in_angle; Side.
    apply (l11_30_等角保持小于等于 A D O E D O); 等角.
    destruct (acute_chara A D O E) as [HD HI]; eBetween.
    apply lta__lea, HD, H为锐角.
  }
  destruct HF as [_ [_ [HDP [F [HBet4 [Heq|HOut]]]]]].
    exfalso; subst F; apply HNCol2; ColR.
  assert_diffs.
  assert (H等角1 : 等角 A D O O D F).
    apply (l11_10 A D O O D P); try apply out_trivial; auto.
  assert (H等角2 : 等角 O D C A D O).
    apply 等角的左交换性, out2__conga; [apply l6_6, bet_out|apply out_trivial]; Between.
  clear dependent P.
  assert (HNCol3 : ~ Col O D F) by (apply (不共线三点构成的角的等角三点也不共线 A D O); Col).
  assert_diffs.
  destruct (l11_50_1 O D C O D F) as [HCong1 [HCong2 H等角3]]; Cong.
    intro; apply HNCol2; ColR.
    apply (l11_10 D O C D O E); 等角; try (apply out_trivial; auto); apply bet_out; auto.
    apply 角等的传递性 with A D O; trivial.
  apply (等长保持小于关系 D F D E); Cong.
  assert (HNCol4 : ~ Col E D F).
  { intro; elim (两点重合的决定性 E F); intro; [|apply HNCol3; ColR].
    treat_equalities.
    apply (acute_not_per A D O); trivial.
    apply 直角的对称性, 直角边共线点也构成直角2 with C; Col.
    exists E; repeat split; Cong.
  }
  assert_diffs.
  apply l11_44_2_b; trivial.
  apply lta_trans with F D O.
  - destruct (l11_41 D E O C) as [Hlta1 Hlta2]; Between.
      intro; apply HNCol3; ColR.
    apply (conga_preserves_lta D E O O D C); trivial;
      [apply out2__conga|apply (l11_10 O D A F D O)]; 等角;
      try (apply out_trivial; auto); apply bet_out; Between.
  - destruct (l11_41 F O D E); Col.
Qed.

Lemma acute_archi_aux1 : forall O A0 A1 B P Q R,
  Per O A0 B -> B <> A0 -> Bet A0 A1 B ->
  角度在线性刻度上 A0 O A1 P Q R -> A0 <> A1 ->
  角度小于等于 A0 O B P Q R \/ exists A, Bet A0 A1 A /\ Bet A0 A B /\ 等角 P Q R A0 O A.
Proof.
  intros O A0 A1 B P Q R HPer HBA0 HBet HGA HA0A1.
  assert (Hdiff := grada_distincts A0 O A1 P Q R HGA); spliter.
  assert (HNCol : ~ Col O A0 B) by (apply 成直角三点不共线; auto).
  assert_diffs.
  elim (lea_total A0 O B P Q R); auto.
  intro H角度小于等于; right.
  assert (HNCol2 : ~ Col P Q R).
  { intro HCol.
    assert (HBet1 : Bet P Q R).
      apply not_out_bet; trivial.
      intro HOut; assert (Out O A0 A1) by (apply grada_out__out with P Q R; trivial).
      apply HNCol; ColR.
    assert (Bet A0 O B) by (apply bet_lea__bet with P Q R; trivial).
    apply HNCol; Col.
  }
  destruct (给定角一边可作出与给定点同侧一点构成等角_非平角 P Q R A0 O B) as [C [Hconga HOS]]; Col.
  assert (HA : 在角内 C A0 O B).
    apply lea_in_angle; Side; apply (l11_30_等角保持小于等于 P Q R A0 O B); 等角.
  destruct HA as [_ [_ [HCO [A [HA HUn]]]]].
  destruct HUn as [Heq|Hout].
    exfalso; treat_equalities; apply HNCol; Col.
  exists A.
  assert (Hconga1 : 等角 P Q R A0 O A).
    apply l11_10 with P R A0 C; trivial; apply out_trivial; auto.
  repeat (split; trivial).
  elim (两点重合的决定性 A1 A).
    intro; subst A; Between.
  intro HAA1.
  apply (不共线三点构成的角的等角三点也不共线 P Q R A0 O A) in HNCol2; trivial.
  assert (HInangle : 在角内 A1 A0 O A).
  { apply lea_in_angle.
      apply (l11_30_等角保持小于等于 A0 O A1 P Q R); 等角; apply grada__lea; trivial.
    apply out_one_side; auto.
    assert_diffs.
    apply l6_7 with B; [|apply l6_6]; apply bet_out; auto.
  }
  destruct HInangle as [_ [_ [_ [X [HX1 HUn]]]]].
  destruct HUn as [HX2|HX2].
    subst X; exfalso; Col.
  elim (两点重合的决定性 X A1); intro.
    subst X; trivial.
  exfalso; apply HNCol2; ColR.
Qed.

Lemma acute_archi_aux2 : forall O A0 A1 B C,
  Per O A0 B -> O <> A0 -> B <> A0 ->
  Bet A0 A1 B -> A0 <> A1 -> Grad A0 A1 C ->
  exists P, exists Q, exists R, 角度在线性刻度上 A0 O A1 P Q R /\ (角度小于等于 A0 O B P Q R \/
  exists A', Bet A0 A1 A' /\ Bet A0 A' B /\ 等角 P Q R A0 O A' /\ Le A0 C A0 A' /\
  exists A, Bet A0 A A' /\ 等角 A O A' A0 O A1 /\ Le A0 A1 A A').
Proof.
  intros O A0 A1 B E HPer HOA0 HBA0 HBet HA0A1 HG.
  assert (HNCol : ~ Col O A0 B) by (apply 成直角三点不共线; auto).
  assert (HNCol1 : ~ Col A0 O A1) by (intro; apply HNCol; ColR).
  assert_diffs.
  induction HG; rename A into A0; rename B0 into A1.
    exists A0; exists O; exists A1; split; [apply 角度线性刻度_初始化; 等角|].
    right; exists A1; repeat (split; 等角); Between; Le.
    exists A0; repeat (split; 等角); Between; Le.
  destruct IHHG as [P [Q [R [HGA HUn]]]]; auto.
  destruct HUn as [HLea|HA'].
    exists P; exists Q; exists R; split; trivial; left; trivial.
  destruct HA' as [A' [HBet1' [HBet2' [HConga' [HLe' HA]]]]].
  destruct HA as [A [HBet1 [HConga HLe]]].
  assert (HIsi : 角度之和小于平角 P Q R A0 O A1).
  { apply sams_lea2__sams with A0 O B A0 O B.
    - apply acute__sams, l11_43_aux; Col.
    - apply (l11_30_等角保持小于等于 A0 O A' A0 O B); 等角.
      exists A'; assert_diffs; split; 等角.
      repeat split; auto.
      exists A'; split; trivial.
      right; apply out_trivial; auto.
    - exists A1; split; 等角.
      repeat split; auto.
      exists A1; split; trivial.
      right; apply out_trivial; auto.
  }
  assert_diffs.
  destruct (和角的存在性 P Q R A0 O A1) as [P' [Q' [R' HSuma]]]; auto.
  assert (HGA' : 角度在线性刻度上 A0 O A1 P' Q' R') by (apply 角度线性刻度_步进 with P Q R; trivial).
  exists P'; exists Q'; exists R'; split; trivial.
  destruct (acute_archi_aux1 O A0 A1 B P' Q' R') as [HLea|HA'']; auto.
  right; destruct HA'' as [A'' [HBet1'' [HBet2'' HConga'']]].
  assert (HNCol2 : ~ Col A O A') by (apply (不共线三点构成的角的等角三点也不共线 A0 O A1); Col; 等角).
  assert (HNCol3 : ~ Col A0 O A') by (intro; assert_diffs; apply HNCol; ColR).
  assert (HNCol4 : ~ Col A' O A'').
  { intro HCol; apply HNCol1.
    elim (两点重合的决定性 A' A''); intro; [|ColR].
    treat_equalities.
    assert (HSuma2 : 和角 A0 O A' A0 O A1 A0 O A').
      apply (等角保持和角 P Q R A0 O A1 P' Q' R'); 等角.
    apply sams_suma__out546 in HSuma2; Col.
    apply (conga2_sams__sams P Q R A0 O A1); 等角.
  }
  assert (HNCol5 : ~ Col A0 O A'') by (intro; assert_diffs; apply HNCol4; ColR).
  assert (HBet4 : Bet A0 A' A'').
  { apply col_two_sides_bet with O.
      ColR.
    apply 角端点在角内点与顶点连线两侧; Col.
    apply lea_in_angle.
      apply (l11_30_等角保持小于等于 P Q R P' Q' R'); 等角; apply sams_suma__lea123789 with A0 O A1; trivial.
    apply out_one_side; Col; apply l6_7 with B; [|apply l6_6]; assert_diffs; apply bet_out; auto.
  }
  assert (HConga4 : 等角 A O A' A' O A'').
  { assert_diffs.
    assert (HNOS : ~ OS O A' A0 A'') by (apply l9_9; repeat split; auto; Col; exists A'; Col).
    apply 角等的传递性 with A0 O A1; trivial.
    apply sams2_suma2__conga456 with P Q R P' Q' R'; trivial.
    - apply (conga2_sams__sams A0 O A' A' O A''); 等角.
      split; auto; split.
        right; intro; Col.
      exists A''; repeat (split; 等角); Cop.
      apply l9_9_bis, out_one_side; Col.
      apply bet_out; auto.
    - apply (等角保持和角 A0 O A' A' O A'' A0 O A''); 等角.
      exists A''; repeat (split; 等角); Cop.
  }
  assert (HLe'' : Le A0 A1 A' A'').
    apply 长度小于等于的传递性 with A A'; trivial; assert_diffs.
    apply 长度小于蕴含小于等于, acute_archi_aux with O A0 B; eBetween.
  exists A''; repeat (split; trivial).
    apply bet2_le2__le1346 with C A'; auto.
    apply (l5_6_等长保持小于等于关系 A0 A1 A' A''); Cong.
  exists A'; split; trivial; split; trivial.
  apply 角等的传递性 with A O A'; 等角.
Qed.

Lemma archi_in_acute_angles :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> 为锐角 D E F ->
    exists P Q R, 角度在线性刻度上 A B C P Q R /\ 角度小于等于 D E F P Q R.
Proof.
  intros archi A B C D E F HNCol H为锐角.
  assert_diffs.
  elim (共线的决定性 D E F).
  { intro HCol; exists A; exists B; exists C; split.
      apply 角度线性刻度_初始化; 等角.
    apply l11_31_1_任何角小于等于平角_Out表述; auto; apply not_bet_out; trivial.
    intro HBet; apply (nlta D E F), acute_obtuse__lta; trivial.
    apply bet__obtuse; auto.
  }
  intro HNCol1.
  elim (lea_total D E F A B C); auto; intro HLea.
    exists A; exists B; exists C; split; trivial; apply 角度线性刻度_初始化; 等角.
  destruct (l8_18_过一点垂线之垂点的存在性 D E F) as [D0 [HD0 HD0']]; trivial.
  assert (HOut : Out E D0 D) by (apply acute_col_perp__out with F; Col; Perp; apply acute_sym; trivial).
  assert_diffs.
  assert (HConga : 等角 D E F D0 E F) by (apply out2__conga; [|apply out_trivial]; auto).
  apply (acute_conga__acute D E F D0 E F) in H为锐角; trivial.
  apply (l11_30_等角保持小于等于 A B C D E F A B C D0 E F) in HLea; 等角.
  apply (不共线三点构成的角的等角三点也不共线 D E F D0 E F) in HNCol1; trivial.
  assert (HPer : Per E D0 F) by (apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with D; Perp; Col).
  clear H0 HD0 HD0' HOut H9.
  destruct (给定角一边可作出与给定点同侧一点构成等角_非平角 A B C D0 E F) as [D1' [HConga1 HOS]]; trivial.
  destruct (lea_in_angle D0 E F D1') as [_ [_ [_ [D1 [HBet HUn]]]]]; Side.
    apply (l11_30_等角保持小于等于 A B C D0 E F); 等角.
  destruct HUn as [Heq|HOut].
    exfalso; subst D1; Col.
  assert (HConga2 : 等角 A B C D0 E D1).
    apply (l11_10 A B C D0 E D1'); trivial; apply out_trivial; auto.
  apply one_side_not_col123 in HOS.
  assert_diffs.
  assert (D0 <> D1) by (intro; subst D1; apply HOS; Col).
  clear dependent D1'.
  destruct (由一点往一方向构造等长线段 D0 F D0 F) as [F' [HF'1 HF'2]].
  destruct (archi D0 D1 D0 F') as [G [HG1 HG2]]; auto.
  destruct (acute_archi_aux2 E D0 D1 F G) as [P [Q [R [HGA HUn]]]]; auto.
  exists P; exists Q; exists R; split.
    assert (Hdistincts := grada_distincts D0 E D1 P Q R HGA); spliter.
    apply (conga2_grada__grada D0 E D1 P Q R); 等角.
  destruct HUn as [HLea2|Habs].
    assert_diffs; apply (l11_30_等角保持小于等于 D0 E F P Q R); 等角.
  exfalso.
  destruct Habs as [A' [HBet2 [HBet3 [HConga3 [HLe HA]]]]].
  apply (长度小于等于推出反向不小于 D0 F' D0 G); trivial.
  apply 长度小于等于_小于_传递性 with D0 F.
    apply 长度小于等于的传递性 with D0 A'; Le.
  split; Le.
  intro HCong.
  assert (F = F') by (apply between_cong with D0; trivial).
  treat_equalities; auto.
Qed.

Lemma angles_archi_aux :
  forall A B C D E F G H I,
    角度在线性刻度上 A B C D E F -> 角度在线性刻度上 A B C G H I -> ~ 角度之和小于平角 D E F G H I ->
    exists P Q R, 角度在线性刻度上 A B C P Q R /\ ~ 角度之和小于平角 P Q R A B C.
Proof.
  intros A B C D E F G H I HGA1 HGA2.
  induction HGA2.
    intro HNIsi; exists D; exists E; exists F; split; trivial.
    assert (Hd := grada_distincts A B C D E F HGA1); spliter.
    intro HIsi; apply HNIsi, (conga2_sams__sams D E F A B C); 等角.
  intro HNIsi.
  elim (sams_dec D E F D0 E0 F0); [|apply IHHGA2; trivial].
  intro HIsi; clear IHHGA2.
  assert (Hd := sams_distincts D E F D0 E0 F0 HIsi); spliter.
  destruct (和角的存在性 D E F D0 E0 F0) as [P [Q [R HSuma]]]; auto.
  exists P; exists Q; exists R; split.
    apply grada2_sams_suma__grada with D E F D0 E0 F0; trivial.
  intro HIsi2; apply HNIsi, sams_assoc_1 with D0 E0 F0 A B C P Q R; trivial.
Qed.

Lemma angles_archi_aux1 :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> ~ Bet D E F ->
    exists P Q R, 角度在线性刻度上 A B C P Q R /\ (角度小于等于 D E F P Q R \/ ~ 角度之和小于平角 P Q R A B C).
Proof.
  intros archi A B C D E F HNCol HNBet.
  assert (Hdiff : D <> E /\ F <> E) by (split; intro; subst E; Between); spliter.
  assert_diffs.
  destruct (angle_bisector D E F) as [F1 [HInangle HConga]]; auto.
  assert(HNOS : ~ OS E F1 D F).
  { assert_diffs.
    elim (共线的决定性 D E F1).
      intros HCol; apply col123__nos; Col.
    intro HNCol1.
    apply l9_9, invert_two_sides, 角端点在角内点与顶点连线两侧; Col.
    apply 共线否定排列BCA, (不共线三点构成的角的等角三点也不共线 D E F1); 等角.
  }
  assert (HSuma : 和角 D E F1 D E F1 D E F) by (assert_diffs; exists F; repeat (split; 等角); Cop).
  destruct (archi_in_acute_angles archi A B C D E F1) as [P1 [Q1 [R1 [HGA HLea]]]]; trivial.
  { apply nbet_sams_suma__acute with D E F; trivial.
    assert_diffs; split; trivial; split.
      right; intro HBet; apply HNBet, 角一边反向延长线上点在角内则该角为平角 with F1; trivial.
    exists F; repeat (split; 等角); Cop.
    elim (共线的决定性 D E F1).
      intros HCol HTS; destruct HTS; Col.
    intro HNCol1.
    elim (共线的决定性 D E F).
      intros HCol HTS; destruct HTS as [_ []]; Col.
    intro HNCol2; apply l9_9_bis, 角内点和一端点在角另一边同侧; Col.
  }
  assert_diffs.
  destruct (sams_dec P1 Q1 R1 P1 Q1 R1) as [HIsi|HNIsi].
  { destruct (和角的存在性 P1 Q1 R1 P1 Q1 R1) as [P [Q [R HSuma1]]]; auto.
    exists P; exists Q; exists R; split.
      apply grada2_sams_suma__grada with P1 Q1 R1 P1 Q1 R1; trivial.
    left; apply sams_lea2_suma2__lea with D E F1 D E F1 P1 Q1 R1 P1 Q1 R1; trivial.
  }
  destruct (angles_archi_aux A B C P1 Q1 R1 P1 Q1 R1) as [P [Q [R [HGA1 HNsams1]]]]; trivial.
  exists P; exists Q; exists R; split; auto.
Qed.

(** Inspired by Hartshorne's demonstration of Lemma 35.1 in Geometry Euclid and Beyond *)
Lemma archi_in_angles :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> D <> E -> F <> E ->
    exists P Q R, 角度在线性刻度上 A B C P Q R /\ (角度小于等于 D E F P Q R \/ ~ 角度之和小于平角 P Q R A B C).
Proof.
  intros archi A B C D E F HNCol HDE HFE.
  elim (中间性的决定性 D E F); [|apply angles_archi_aux1; trivial].
  intro HBet1.
  destruct (由一点往一方向构造等长线段 A B A B) as [A0 [HBet HCong]].
  assert_diffs.
  assert (HNCol1 : ~ Col A0 B C) by (intro; apply HNCol; ColR).
  destruct (angles_archi_aux1 archi A B C C B A0) as [P1 [Q1 [R1 [HGA HUn]]]]; Between.
    intro; apply HNCol1; Col.
  elim (sams_dec P1 Q1 R1 A B C); [|intro; exists P1; exists Q1; exists R1; auto].
  intro HIsi.
  destruct HUn as [HLea|HNIsi]; [|exfalso; auto].
  assert_diffs.
  destruct (和角的存在性 P1 Q1 R1 A B C) as [P [Q [R HSuma]]]; auto.
  exists P; exists Q; exists R; split.
    apply 角度线性刻度_步进 with P1 Q1 R1; trivial.
  suma.assert_diffs.
  left; apply l11_31_1_任何角小于等于平角_Bet表述; auto.
  apply (bet_lea__bet A B A0); trivial.
  apply sams_lea2_suma2__lea with A0 B C A B C P1 Q1 R1 A B C; Lea.
  exists A; repeat (split; 等角); Cop.
  apply l9_9; repeat split; auto.
  exists B; split; Col; Between.
Qed.

(** If Archimedes' postulate holds, every nondegenerate angle can be repeated until exceeding 180° *)
Lemma archi__grada_destruction :
  archimedes_axiom ->
  forall A B C,
    ~ Col A B C ->
    exists P Q R, 角度在线性刻度上 A B C P Q R /\ ~ 角度之和小于平角 P Q R A B C.
Proof.
  intros archi A B C HNCol.
  destruct (由一点往一方向构造等长线段 A B A B) as [A0 [HBet HCong]].
  assert_diffs.
  destruct (archi_in_angles archi A B C A B A0) as [P [Q [R [HGA HUn]]]]; auto.
  exists P; exists Q; exists R; split; auto.
  destruct HUn as [HLea|]; trivial.
  intro HIsi.
  destruct HIsi as [_ [[HOut|HNBet] _]].
    apply HNCol; Col.
  apply HNBet, (bet_lea__bet A B A0); trivial.
Qed.


Lemma gradaexp_destruction_aux : forall A B C P Q R,
  角度在线性刻度上 A B C P Q R ->
  exists S T U, 角度在对数刻度上 A B C S T U /\ (为钝角 S T U \/ 角度小于等于 P Q R S T U).
Proof.
  intros A B C.
  induction 1.
    assert_diffs; exists D; exists E; exists F; split; [apply 角度对数刻度_初始化|right]; Lea.
  destruct IH角度在线性刻度上 as [P [Q [R [HGAE HUn]]]].
  assert (Hd := HGAE); apply gradaexp__grada, grada_distincts in Hd; spliter.
  destruct (sams_dec P Q R P Q R) as [HIsi|HNIsi].
  { destruct HUn as [Habs|HLea].
      absurd (角度之和小于平角 P Q R P Q R); trivial; apply obtuse__nsams, Habs.
    destruct (和角的存在性 P Q R P Q R) as [S [T [U HSuma]]]; auto.
    exists S; exists T; exists U; split.
      apply 角度对数刻度_步进 with P Q R; trivial.
    right; apply sams_lea2_suma2__lea with D E F A B C P Q R P Q R; trivial.
    apply grada__lea, gradaexp__grada, HGAE.
  }
  apply nsams__obtuse in HNIsi; auto.
  exists P; exists Q; exists R; split; auto.
Qed.

(** If Archimedes' postulate holds, every nondegenerate angle can be doubled until exceeding 90° *)
Lemma archi__gradaexp_destruction :
  archimedes_axiom ->
  forall A B C,
    ~ Col A B C ->
    exists P Q R, 角度在对数刻度上 A B C P Q R /\ 为钝角 P Q R.
Proof.
  intros archi A B C HNCol.
  destruct (archi__grada_destruction archi A B C HNCol) as [D [E [F [HGA HNIsi]]]].
  destruct (gradaexp_destruction_aux A B C D E F HGA) as [P [Q [R [HGAE HUn]]]].
  exists P; exists Q; exists R; split; trivial.
  destruct HUn as [H为钝角|HLea]; trivial.
  assert_diffs.
  apply nsams__obtuse; auto.
  intro HIsi; apply HNIsi.
  apply sams_lea2__sams with P Q R P Q R; trivial.
  apply grada__lea, gradaexp__grada, HGAE.
Qed.

End Archimedes_for_angles.
