Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.tarski_s_euclid_remove_degenerated_cases.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section SPP_tarski.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma impossible_case_5 : forall P Q R S U I,
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Bet S Q I ->
  Bet U I P ->
  False.
Proof.
intros P Q R S U I HQUR HNC HNC' HPar HSQI HPUI.
apply 严格中间性的等价 in HQUR.
apply par_symmetry in HPar.
apply (par_not_col_strict Q S P R P) in HPar; Col.
assert (HOS : OS Q S R U).
  {
  assert (HQS : Q <> S) by (统计不重合点; auto).
  assert (HQSQ : Col Q S Q) by Col.
  assert (HRUQ : Col R U Q) by (分离合取式; Col).
  rewrite (l9_19 Q S R U Q HQSQ HRUQ).
  分离合取式.
  split; [Out|apply par_strict_not_col_4 with P, HPar].
  }
apply (l9_9 Q S P U); [|apply one_side_transitivity with R; Side].
apply one_side_not_col124 in HOS.
分离合取式; repeat split; Col.
exists I; split; [Col|Between].
Qed.

Lemma impossible_case_6 : forall P Q R S U I,
  BetS Q U R ->
  ~ Col P Q S ->
  Par P S Q R ->
  Bet S Q I ->
  Bet I P U ->
  False.
Proof.
intros P Q R S U I HQUR HNC HPar HSQI HPUI.
apply 严格中间性的等价 in HQUR.
apply 中间性的对称性 in HPUI.
destruct (帕施公理 S U I Q P HSQI HPUI) as [J [HBet1 HBet2]].
assert (HParS : 严格平行 P S Q U).
  {
  分离合取式.
  apply par_strict_col_par_strict with R; Col.
  apply par_not_col_strict with Q; Col.
  }
apply HParS; exists J; split; Col.
Qed.

Lemma impossible_case_7 : forall P Q R S U I,
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Col P U I ->
  Bet Q I S ->
  False.
Proof.
intros P Q R S U I HQUR HNC HNC' HPar1 HPar2 HPUI HSQI.
apply 严格中间性的等价 in HQUR.
revert HPUI.
apply one_side_not_col124 with Q.
apply l9_17 with S; [|assumption].
destruct HQUR as [HQUR HDiff].
apply 中间性的对称性 in HQUR.
exists R; split.
  分离合取式; apply l9_2, invert_two_sides, bet__ts; Col.
apply l9_31.
  {
  apply one_side_symmetry, l9_17 with Q; [|assumption].
  apply l12_6, par_not_col_strict with Q; Par; Col.
  }
apply one_side_transitivity with Q.
  分离合取式; apply invert_one_side, out_one_side; [Col|Out].
apply l12_6, par_strict_symmetry, par_not_col_strict with P; Par; Col.
Qed.

Lemma impossible_case_8 : forall P Q R S U I,
  BetS Q U R ->
  ~ Col P Q S ->
  Par P R Q S ->
  Par P S Q R ->
  Col P U I ->
  Bet I S Q ->
  False.
Proof.
intros P Q R S U I HQUR HNC HPar1 HPar2 HPUI HSQI.
apply 严格中间性的等价 in HQUR.
destruct HQUR as [HQUR [HQU [HQR HUR]]].
assert (H : 严格平行 P S Q U)
  by (apply par_strict_col_par_strict with R; Col; apply par_not_col_strict with Q; Col; Par).
apply 中间性的对称性 in HSQI.
elim HPUI; clear HPUI; intro HPUI.

  {
  apply H.
  destruct (帕施公理 P Q I U S HPUI HSQI) as [J [HQJU HPJS]]; exists J.
  split; Col.
  }

  {
  elim HPUI; clear HPUI; intro HPUI.

    {
    apply H.
    destruct (outer_pasch U Q I P S HPUI HSQI) as [J [HQJU HPSJ]]; exists J.
    split; Col.
    }

    {
    assert (H1 : 严格平行 P R Q I).
      统计不重合点; apply par_strict_col_par_strict with S; Col.
      apply par_strict_symmetry, par_not_col_strict with P; Col; Par.
    apply H1.
    destruct (outer_pasch Q I U R P HQUR HPUI) as [J [HQJI HRPJ]]; exists J.
    split; Col.
    }
  }
Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid_aux :
  strong_parallel_postulate ->
  (forall A B D T,
   A <> B ->
   A <> D ->
   A <> T ->
   B <> D ->
   B <> T ->
   D <> T ->
   ~ Col A B T ->
   Bet A D T ->
   exists B', exists B'', exists MB, exists X, Bet A B X /\ 严格平行 T X B D /\
   BetS B MB T /\ BetS B' MB B'' /\
   Cong B MB T MB /\ Cong B' MB B'' MB /\
   Col B B' D /\ Bet B'' T X /\
   B <> B' /\ B'' <> T).
Proof.
intros HSPP A B D T HAB HAD HAT HBD HBT HDT HABT HADT.
destruct (构造对称点 D B) as [B' HB'].
destruct (严格中点组推论2 B D B' HBD HB') as [HB'D HBB'].
destruct HB' as [HBDB' HCong1].
apply 中间性的对称性 in HADT.
apply 中间性的对称性 in HBDB'.
destruct (中点的存在性 B T) as [MB HMB].
destruct (严格中点组推论1 MB B T HBT HMB) as [HBMB HMBT].
destruct HMB as [HBMBT HCong2].
destruct (构造对称点 B' MB) as [B'' HB''].
assert (HB'MB : MB <> B').
  {
  intro; treat_equalities; apply HABT; ColR.
  }
destruct (严格中点组推论2 MB B' B'' HB'MB HB'') as [HB'B'' HB''MB].
destruct HB'' as [HB'MBB'' HCong3].
assert (H1 : ~ Col B T B'') by (intro; apply HABT; ColR).
assert (H2 : BetS B MB T) by (repeat split; Between).
assert (H3 : BetS B' MB B'') by (repeat split; Between).
destruct (outer_pasch T B' D A B HADT HBDB') as [B''' [HTB'''B' HABB''']].
assert (HB'B''' : B' <> B''').
  {
  intro; treat_equalities; apply HABT; ColR.
  }
assert (HB'''T : B''' <> T).
  {
  intro; treat_equalities; Col.
  }
assert (H4 : BetS T B''' B') by (repeat split; Between).
assert (HNC : ~ Col B B' B''') by (intro; apply H1; ColR).
destruct (HSPP B T B' B'' MB B''') as [X [HBetS HX]]; Cong; [Cop|].
assert (HPar1 : Par B B' T B'')
  by (unfold BetS in *; 分离合取式; apply l12_17 with MB; [|split..]; auto).
assert (HPar2 : Par B B'' T B').
  {
  apply 不共线则不重合 in H1; 分离合取式.
  unfold BetS in *; 分离合取式; apply l12_17 with MB; [|split..]; Between; Cong.
  }
elim HBetS; clear HBetS; intro HBetS.

  {
  elim HX; clear HX; intro HX.

    {
    assert (H : BetS B'' T X).
      {
      repeat split; [|intro; treat_equalities..]; Col.
      apply HABT; ColR.
      }
    clear HBetS; rename H into HBetS.
    assert (H : BetS B B''' X).
      {
      repeat split; [|intro; treat_equalities..]; Col.
      unfold BetS in *; 分离合取式; apply H1; ColR.
      }
    clear HX; rename H into HX.
    apply 严格中间性的等价 in HBetS; destruct HBetS as [HB''TX [HB''T [HB''X HBTX]]].
    exists B', B'', MB, X.
    split.
      unfold BetS in HX; 分离合取式; eBetween.
    split.
      apply par_strict_col_par_strict with B'; Col.
      apply par_strict_symmetry, par_strict_col_par_strict with B''; Col.
      apply par_strict_symmetry, par_not_col_strict with B; Par; Col.
    repeat (split; [try assumption|]); Cong; Col.
    }

    {
    exfalso.
    elim HX; clear HX; intro HX.

      {
      apply (impossible_case_5 B T B' B'' B''' X); assumption.
      }

      {
      apply (impossible_case_6 B T B' B'' B''' X); assumption.
      }
    }
  }

  {
  exfalso.
  elim HBetS; clear HBetS; intro HBetS.

    {
    apply (impossible_case_7 B T B' B'' B''' X); assumption.
    }

    {
    apply (impossible_case_8 B T B' B'' B''' X); assumption.
    }
  }
Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid :
  strong_parallel_postulate ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HSPP; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC HBCT.
assert (~ Col A B T) by (intro; apply HABC; ColR).
assert (~ Col A C T) by (intro; apply HABC; ColR).
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A B D T)
as [B' [B'' [MB [X [HABX [HPar' [HBet1 [HBet2 [HCong1 [HCong2 [HBB'D [HB''TX [HBB' HB''T]]]]]]]]]]]]];
[assumption..|].
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A C D T)
as [_ [_ [_ [Y [HACY [HPar _]]]]]]; Between.
exists X; exists Y; repeat (split; [assumption|]).
elim (共线的决定性 X T Y); intro HXTY.

  {
  clear dependent MB; clear dependent B'; clear dependent B''.
  assert (HAXY : ~ Col A X Y) by (intro; apply HABC; ColR).
  apply 中间性的对称性 in HACY.
  assert (HU := outer_pasch Y B C A D HACY HBDC); destruct HU as [U [HYUB HADU]].
  apply 中间性的对称性 in HABX.
  assert (HV := outer_pasch X Y B A U HABX HYUB); destruct HV as [V [HXVY HAUV]].
  assert (HEq : T = V) by (apply (l6_21_两线交点的唯一性 X Y A D); ColR).
  subst; assumption.
  }

  {
  clear dependent A.
  assert (HNC : ~ Col T B'' Y) by (intro; apply HXTY; ColR).
  apply (par_strict_col_par_strict T Y C D B) in HPar; Col.
  apply (par_strict_col_par_strict T X B D C) in HPar'; Col.
  assert (HCop : 共面 T B B'' Y).
    {
    apply 不共线则不重合 in HXTY; 分离合取式.
    apply 等价共面CADB, col_cop__cop with X; Col.
    apply 等价共面ADBC, coplanar_trans_1 with C; Col; Cop.
    }
  unfold BetS in *; 分离合取式.
  destruct (HSPP T B B'' B' MB Y) as [I [HCol1 HCol2]]; Cong; [repeat split; Between..|].
  exfalso; apply HPar; exists I; split; ColR.
  }
Qed.

End SPP_tarski.