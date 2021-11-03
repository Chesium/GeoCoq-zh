Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section Aristotle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma aristotle__greenberg : aristotle_s_axiom -> greenberg_s_axiom.
Proof.
  intros aristotle P Q R A B C.
  intros HNColB HABCacute HQRdiff HQright.
  elim (两点重合的决定性 P Q); intro HPQdiff.
  { treat_equalities.
    assert_diffs.
    exists R.
    split; [|apply out_trivial; auto].
    split.
    apply lea121345; auto.
    intro.
    apply HNColB.
    apply 等价共线BAC.
    apply out_col.
    apply (eq_conga_out P R); auto.
  }
  assert (HXY : (exists X Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y)) by (apply aristotle; assumption).
  destruct HXY as [X [Y [PX [PY [HXright [Hle HNcong]]]]]].
  assert_diffs.
  assert (HXYdiff : X <> Y) by (intro; treat_equalities; auto).
  assert (HT : (exists T, Out Q T P /\ Cong Q T X Y)) by (apply l6_11_existence; auto).
  destruct HT as [T []].
  assert (HS : (exists S, Out Q S R /\ Cong Q S X B)) by (apply l6_11_existence; auto).
  destruct HS as [S []].
  assert_diffs.
  exists S.
  split; auto.
  assert (Per S Q P) by (apply (l8_3_直角边共线点也构成直角1 R); Perp; Col).
  assert (Per T Q S) by (apply (l8_3_直角边共线点也构成直角1 P); Perp; Col).
  assert (P<>S).
  { intro; treat_equalities.
    assert (P=Q) by (apply ABA直角则A与B重合; auto); treat_equalities; absurde.
  }
  assert (T<>S).
  { intro; treat_equalities.
    assert (T=Q) by (apply ABA直角则A与B重合; auto); treat_equalities; absurde.
  }
  apply conga_preserves_lta with P S Q T S Q; try (apply conga_refl; auto); [|split].
  - apply conga_trans with X B Y; [|apply out2__conga; auto].
    assert (HInter : (Cong T S Y B /\ (T <> S -> 等角 Q T S X Y B /\ 等角 Q S T X B Y))).
    { apply (l11_49 T Q S Y X B); Cong.
      apply l11_16; Perp.
    }
    destruct HInter as [_ [_ HConga]]; auto.
    apply conga_left_comm; auto.

  - apply lea_comm.
    apply (l11_29_b Q S P Q S T).
    exists T.
    split; 等角.
    repeat split; auto.
    exists P.
    split; [|right; apply out_trivial; auto].
    apply l6_13_1.
    apply l6_6; auto.
    apply (长度小于等于的传递性 Q P X Y).
    apply (长度小于等于的传递性 Q P P Q); Le.
    apply (等长则小于等于); Cong.

  - intro HConga.
    assert (HInter : Cong Q P Q T /\ Cong S P S T /\ 等角 Q P S Q T S).
    { apply l11_50_1; Cong.
      { intro.
        assert (HUn : S=Q\/P=Q) by (apply l8_9_直角三点共线则必有两点重合; Col).
        destruct HUn; treat_equalities; absurde.
      }
      apply l11_16; Perp.
      等角.
    }
    destruct HInter as [HCong _].
    apply HNcong.
    apply (等长的传递性 P Q T Q); Cong.
Qed.


(** This proof is inspired by The elementary Archimedean axiom in absolute geometry, by Victor Pambuccian *)

Lemma greenberg__aristotle : greenberg_s_axiom -> aristotle_s_axiom.
Proof.
intros HG P Q A B C HNC H为锐角.
destruct (l10_15 A B B C) as [D' [HPerp1 HOS1]]; Col.
elim (两点重合的决定性 P Q); intro HPQ; treat_equalities.

  {
  destruct (l8_18_过一点垂线之垂点的存在性 A B C) as [X [HCol HPerp]]; Col; exists X, C.
  split; [apply l6_6, acute_col_perp__out with C; try apply acute_sym; finish|].
  split; [apply out_trivial; assert_diffs; auto|].
  split; [|apply BC不重合则AA小于BC; assert_diffs; auto].
  elim (两点重合的决定性 X B); intro HBX; treat_equalities; Perp.
  apply L形垂直转直角1, 与垂线共线之线也为垂线2 with A B; Col.
  }

  {
  destruct (由一点往一方向构造等长线段_3 B D' P Q) as [P' [HOut1 HCong1]];
  try solve [assert_diffs; auto].
  destruct (HG P' B A A B C) as [C' HC']; Col; try solve [assert_diffs; auto];
  [apply L形垂直转直角2,  与垂线共线之线也为垂线2 with D' B; finish; assert_diffs; auto|].
  destruct HC' as [H角度小于 HOut2].
  destruct (l10_15 B C' C' C) as [D'' [HPerp2 HOS2]]; Col;
  try (intro H; apply HNC; assert_diffs; assert_cols; ColR).
  destruct (由一点往一方向构造等长线段_3 C' D'' P Q) as [P'' [HOut3 HCong2]];
  try solve [assert_diffs; auto].
  destruct (由一点往一方向构造等长线段_3 B C B P'') as [Z [HOut4 HCong3]];
  try (intro; treat_equalities; assert_cols; Col);
  [elim (垂直推出不共线 _ _ _ _ HPerp2); intro HF; apply HF; Col|].
  destruct (l8_18_过一点垂线之垂点的存在性 A B Z) as [Z' [HCol HPerp3]];
  [intro; apply HNC; ColR|]; assert (HOut5 : Out B Z' A).
    {
      apply acute_col_perp__out with Z; finish.
      apply acute_sym, acute_out2__acute with A C; finish.
      apply out_trivial; assert_diffs; auto.
    }
  exists Z', Z; do 2 (split; finish); split;
  [apply L形垂直转直角1, 与垂线共线之线也为垂线2 with A B; assert_diffs; Col|].
  apply 等长保持小于关系 with C' P'' Z' Z; Cong.
  apply cong_lt_per2__lt_1 with B B; Cong; try (apply L形垂直转直角1);
  [apply 与垂线共线之线也为垂线2 with A B|apply 与垂线共线之线也为垂线3 with C' D''|];
  try solve [assert_diffs; Col; Perp].
  assert (H等角 : 等角 B C' P' A B P'').
    {
    apply l11_10 with B P' C' P''; try solve [assert_diffs; finish].
    apply l11_49; try solve [assert_diffs; finish]; eCong.
    apply l11_16; try solve [assert_diffs; auto]; apply L形垂直转直角1;
    [apply 与垂线共线之线也为垂线2 with B D'|apply 与垂线共线之线也为垂线2 with C' D''];
    assert_diffs; finish; apply 垂直的对称性; apply 与垂线共线之线也为垂线2 with B A; finish.
    }
  assert (HT : 在角内 P'' Z' B Z).
    {
    apply l11_25 with P'' A C; finish; [|apply out_trivial; intro];
    [|treat_equalities; elim (垂直推出不共线 _ _ _ _ HPerp3); Col].
    apply lea_in_angle.

      {
      apply l11_30 with B C' P' A B C; finish;
      apply conga_refl; assert_diffs; auto.
      }

      {
      apply one_side_transitivity with D''.
      apply col2_os__os with B C'; assert_diffs; finish.
      apply out_one_side_1 with C'; finish.
      elim (垂直推出不共线 _ _ _ _ HPerp2); intro HF; Col.
      intro; apply HF; ColR.
      }
    }
  destruct HT as [_ [_ [_ [T [HBet1 [?|HOut6]]]]]]; treat_equalities;
  [exfalso; apply HNC; ColR|destruct HOut6 as [_ [_ HOut6]]].
  assert (HPar : Par Z Z' C' P'').
    {
    apply l12_9 with B C'; Cop; [|apply col__coplanar; ColR|apply 垂直的对称性|];
    [|apply 与垂线共线之线也为垂线2 with A B; assert_diffs; finish|
    apply 与垂线共线之线也为垂线2 with C' D''; assert_diffs; finish].
    assert (共面 B Z C  C') by (apply col__coplanar; ColR).
    assert (共面 C' P'' D'' B) by (apply col__coplanar; ColR).
    assert (共面 C' B D'' C); [Cop|CopR].
    }
  assert (HTZ : T <> Z).
    {
    intro; treat_equalities; destruct H角度小于 as [_ HF]; apply HF.
    apply conga_trans with A B P''; finish.
    apply conga_sym, out2__conga; [assert_diffs; finish|].
    apply l6_7 with T; finish.
    assert_diffs; split; auto; split; auto.
    induction HOut6; auto.
    }
  assert (HTZ' : T <> Z').
    {
    intro; treat_equalities; elim (垂直推出不共线 _ _ _ _ HPerp2); Col.
    intro HF; apply HF; induction HOut6; ColR.
    }
  assert (HTP'' : T <> P'').
    {
    intro; treat_equalities; assert (HF : 为锐角 B T Z).
      {
      apply cong__acute; try solve [assert_diffs; finish].
      }
    apply (acute__not_obtuse _ _ _ HF).
    apply acute_suppa__obtuse with B T Z';
    try (apply suppa_left_comm, bet__suppa); try solve [assert_diffs; finish].
    apply acute_sym, l11_43; try solve [assert_diffs; auto]; left.
    apply L形垂直转直角1; apply 与垂线共线之线也为垂线2 with A B; Col; [|assert_diffs; auto].
    apply 垂直的对称性, 与垂线共线之线也为垂线2 with Z Z'; finish.
    }
  assert (HBet2 : Bet B T P''); [|clear HOut6].
    {
    elim HOut6; [auto|clear HOut6; intro HF; exfalso].
    assert (H为钝角 : 为钝角 Z T B).
      {
      apply acute_suppa__obtuse with B T Z';
      try (apply suppa_left_comm, suppa_right_comm);
      try (apply bet__suppa); try solve [assert_diffs; finish].
      apply acute_sym, l11_43; try solve [assert_diffs; auto]; left.
      apply L形垂直转直角1; apply 与垂线共线之线也为垂线2 with A B; Col; [|assert_diffs; auto].
    apply 垂直的对称性, 与垂线共线之线也为垂线2 with Z Z'; finish.
      }
    apply (两长度不可能互相小于对方a B Z T B T Z); split.

      {
      apply acute_obtuse__lta; [|apply obtuse_sym; auto].
      apply acute_sym, l11_43; assert_diffs; finish.
      right; apply obtuse_sym; auto.
      }

      {
      apply l11_44_2_a; [intro; apply HNC; ColR|].
      apply 长度小于等于_小于_传递性 with B P''; [apply 等长则小于等于; finish|].
      apply bet__lt1213; assert_diffs; finish.
      }
    }
  apply par_symmetry in HPar; apply (par_not_col_strict _ _ _ _ T) in HPar; Col;
  [|intro; apply HTP'', l6_21_两线交点的唯一性 with C' P'' B T; Col;
    [|intro; treat_equalities; apply HNC; ColR];
    elim (垂直推出不共线 _ _ _ _ HPerp2); Col;
    intros HF ?; apply HF; ColR].
  assert (HOS3 := pars__os3412 _ _ _ _ HPar).
  assert (HOut6 : Out P'' T B) by (split; [auto|split; assert_diffs; finish]).
  assert (HOut7 : Out B C' Z') by (apply l6_7 with A; finish).
  destruct HOut7 as [_ [_ [HBet3|HBet3]]];
  [|apply bet__lt1213; Between;
    intro; treat_equalities; apply par_strict_not_col_1 in HPar; Col;
    apply one_side_not_col123 in HOS3; Col].
  exfalso; apply (l9_9_bis _ _ _ _ HOS3), l9_8_2 with B.

    {
    split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists T; split; finish.
    }

    {
    apply out_one_side_1 with Z'; finish; [intro; apply HNC; ColR|].
    assert_diffs; do 2 (split; auto); right; finish.
    }
  }
Qed.


(** This proof is inspired by Several topics from geometry, by Franz Rothe *)

Lemma aristotle__obtuse_case_elimination :
  aristotle_s_axiom ->
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros aristotle obtuse.
  destruct ex_lambert as [Q' [C' [P [Q HLam]]]].
  assert (H为钝角 : 为钝角 C' P Q) by (apply <- (lam_obtuse__oah Q'); trivial).
  assert (HPar : 严格平行 Q' Q C' P) by (apply lam__pars1423, HLam).
  destruct HLam; spliter.
  destruct (l10_15 P Q P C') as [A' [HPerp HOS]]; Col.
    apply 共线否定排列BCA.
    apply par_strict_not_col_1 with Q'; Par.
  assert_diffs.
  assert (H角度小于 : 角度小于 Q P A' C' P Q) by (apply obtuse_per__lta; Perp).
  destruct H角度小于 as [H角度小于等于 HN等角].
  assert (H在角内 : 在角内 A' Q P C').
    apply lea_in_angle; Side; apply lea_right_comm; trivial.
  destruct (由一点往一方向构造等长线段 C' P C' P) as [C [HC1 HC2]].
  destruct (由一点往一方向构造等长线段 A' P A' P) as [A [HA1 HA2]].
  assert_diffs.
  assert (H在角内1 : 在角内 C A P Q).
    apply in_angle_reverse with A'; auto.
    apply l11_24, in_angle_reverse with C'; auto.
    apply l11_24; trivial.
  assert (HNCol : ~ Col P C' A').
  { intro Habs.
    apply HN等角, conga_right_comm, out2__conga.
      apply out_trivial; auto.
    apply col_one_side_out with Q; trivial.
  }
  assert (HNCol1 : ~ Col P C A) by (intro; apply HNCol; ColR).
  assert (HNCol2 : ~ Col P Q C) by (intro; apply (par_strict_not_col_2 Q' Q C' P); ColR).
  assert (HPer : Per A P Q) by (apply 直角的对称性, 直角边共线点也构成直角2 with A'; Perp; Col).
  assert (HOS1 : OS A P C Q).
    apply in_angle_one_side; Col.
    apply 成直角三点不共线; auto.
  destruct (aristotle P Q A P C) as [X [Y]]; Col.
  { exists A, P, Q; split; Perp; split.
      apply inangle__lea; trivial.
    intro H等角.
    assert (Out P C Q) by (apply (conga_os__out A); assumption).
    apply HNCol2; Col.
  }

  spliter.
  apply (两长度不可能互相小于对方 P Q X Y).
  split; trivial.
  destruct (l8_18_过一点垂线之垂点的存在性 P Q Y) as [Z [HZ1 HZ2]].
    intro; assert_diffs; apply HNCol2; ColR.
  apply 长度小于的传递性 with P Z.

  - assert (P <> Z).
    { intro; subst Z.
      assert_diffs.
      assert (Per Q P C) by (apply 直角边共线点也构成直角2 with Y; Col; Perp).
      apply HNCol1, cop_perp2__col with P Q; Perp; Cop.
    }
    assert (HLam : Lambert四边形 P X Y Z).
    { assert_diffs.
      repeat split; auto.
        apply 直角边共线点也构成直角2 with Q; Col.
        apply 直角的对称性, 直角边共线点也构成直角2 with A; Perp; Col.
        apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with Q; auto.
        assert (在角内 Y X P Q).
          apply l11_25 with C A Q; try (apply l6_6); trivial; apply out_trivial; auto.
        apply coplanar_perm_12, col_cop__cop with Q; Col; Cop.
    }
    apply lam_obtuse__lt; trivial.
    apply <- (lam_obtuse__oah P); trivial.

  - assert (HOut : Out Q P Z).
    { apply col_one_side_out with Q'; Col.
      apply one_side_transitivity with Y.
        assert_diffs; apply l12_6, par_strict_col_par_strict with C'; Par; ColR.
      apply l12_6, par_not_col_strict with Y; Col.
      { apply l12_9 with P Q; Perp; [Cop..| |Cop].
        apply coplanar_perm_12, col_cop__cop with C; Col.
        apply  col_cop__cop with C'; Col; Cop.
      }
      apply 共线否定排列BCA, par_not_col with P C'; Par; ColR.
    }
    assert_diffs.
    apply bet__lt1213; auto.
    apply out2__bet; trivial.
    apply col_one_side_out with A; Col.
    apply one_side_transitivity with Y.
    { apply l12_6, par_not_col_strict with Y; Col.
        apply l12_9 with P Q; Perp; [Cop..|].
        apply coplanar_perm_12, col_cop__cop with C; Col; Cop.
      intro; apply HNCol1; ColR.
    }
    apply one_side_symmetry, out_out_one_side with C; Side.
Qed.

Lemma aristotle__acute_or_right :
  aristotle_s_axiom ->
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros aristotle.
  destruct saccheri_s_three_hypotheses as [Ha|[Hr|Ho]]; auto.
  exfalso; apply aristotle__obtuse_case_elimination in aristotle; auto.
Qed.

End Aristotle.
