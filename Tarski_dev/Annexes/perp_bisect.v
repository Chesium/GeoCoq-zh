Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

Section PerpBisect_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma perp_bisect_equiv_def :
  forall P Q A B, Perp_bisect P Q A B <-> 中垂线_另一定义 P Q A B.
Proof.
intros; unfold Perp_bisect; unfold 中垂线_另一定义; unfold 严格对称; split.

  {
  intro H; destruct H as [[[X [HMid HCol]] HPerp] HDiff].
  exists X; split; 中点.
  elim HPerp; clear HPerp; intro HPerp; [|exfalso;auto].
  apply l8_14_2_1b_bis; Col; Perp.
  }

  {
  intro H; destruct H as [I [HPerp HMid]].
  assert_diffs; split; Col.
  split; try (left; apply l8_14_2_1a with I); Perp.
  exists I; split; 中点.
  unfold 垂直于 in *; spliter; Col.
  }
Qed.

Lemma perp_bisect_sym_1 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect Q P A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold 中垂线_另一定义 in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_2 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect P Q B A.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold 中垂线_另一定义 in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_3 : forall A B C D,
 Perp_bisect A B C D ->
 Perp_bisect B A D C.
Proof.
intros.
apply perp_bisect_sym_1.
apply perp_bisect_sym_2.
trivial.
Qed.

Lemma perp_bisect_perp :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold 中垂线_另一定义 in *.
decompose [and ex] H;clear H.
unfold Perp.
exists x.
assumption.
Qed.

End PerpBisect_1.

Hint Resolve perp_bisect_perp : perp.

Section PerpBisect_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma perp_bisect_cong_1 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold 中垂线_另一定义 in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong P A P B).
apply (per_double_cong P I A B);
eauto with perp.
Cong.
Qed.

Lemma perp_bisect_cong_2 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A Q B Q.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold 中垂线_另一定义 in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong Q A Q B).
apply (per_double_cong Q I A B);
eauto with perp.
Cong.
Qed.

End PerpBisect_2.

Hint Resolve perp_bisect_cong_1 perp_bisect_cong_2 : cong.

Section PerpBisect_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma perp_bisect_cong2 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P /\ Cong A Q B Q.
Proof.
intros.
split.
eauto using perp_bisect_cong_1.
eauto using perp_bisect_cong_2.
Qed.

Lemma perp_bisect_cong :
 forall A A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 Perp_bisect O A1 B C -> Perp_bisect O B1 A C -> Perp_bisect O C1 A B ->
 Cong A O B O -> Cong B O C O ->
 Cong A O C O.
Proof.
intros.
apply (等长的传递性 A O B O C O); assumption.
Qed.

Lemma cong_cop_perp_bisect :
 forall P Q A B,
 P <> Q -> A <> B ->
 共面 P Q A B ->
 Cong A P B P ->
 Cong A Q B Q ->
 Perp_bisect P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def.
unfold 中垂线_另一定义.
elim (midpoint_existence A B).
intros I HI.
exists I.
split;try assumption.
assert (Per P I A)
 by (exists B; split; Cong).

show_distinct A I.
unfold 中点 in *.
spliter.
treat_equalities.
intuition.

show_distinct B I.
unfold 中点 in *.
spliter.
treat_equalities.
intuition.

induction(两点重合的决定性 P I).
subst.
eapply l8_13_2;Col.
exists Q. exists B;repeat split;Col.
unfold Per.
exists A.
split.
中点.
Cong.

eapply l8_13_2.
assumption.
assumption.

apply 等价共线CAB.
apply cop_per2__col with A; Col.
destruct(共线的决定性 B A P).
exists I.
left.
split; ColR.
apply coplanar_perm_12, col_cop__cop with B; Col; Cop.
exists B; split; Cong.

apply midpoint_col;auto.
exists P.
exists A.
repeat split;Col.
Qed.

Lemma cong_mid_perp_bisect :
 forall P Q A B,
 P <> Q -> A <> B ->
 Cong A P B P ->
 中点 Q A B ->
 Perp_bisect P Q A B.
Proof.
intros.
apply cong_cop_perp_bisect; Cong; Cop.
Qed.

Lemma perp_bisect_在中垂线上 :
 forall A B C P,
  在中垂线上 P A B ->
  在中垂线上 P B C ->
  在中垂线上 P A C.
Proof.
intros.
unfold 在中垂线上 in *.
CongR.
Qed.

Lemma perp_mid_perp_bisect : forall A B C D,
 中点 C A B -> Perp C D A B ->
 Perp_bisect C D A B.
Proof.
intros.
apply perp_bisect_equiv_def.
unfold 中垂线_另一定义 in *.
exists C.
split; auto.
apply l8_14_2_1b_bis; Col.
Qed.

Lemma cong_cop2_perp_bisect_col : forall A B C D E,
  共面 A C D E ->
  共面 B C D E ->
  Cong C D C E ->
  Perp_bisect A B D E ->
  Col A B C.
Proof.
intros A B C D E HCop1 HCop2 HCong1 HPerp.
assert (HCong2 := HPerp); apply perp_bisect_cong2 in HCong2; destruct HCong2 as [HCong2 Hc]; clear Hc.
apply perp_bisect_equiv_def in HPerp.
destruct HPerp as [F [HPerp [HBet HCong3]]].
assert (HDE : D <> E) by (assert_diffs; auto).
assert (HCol := HPerp); apply perp_in_col in HCol; destruct HCol as [HCol Hc]; clear Hc.
apply l8_14_2_1a in HPerp.
elim (两点重合的决定性 A C); intro; try (subst; Col).
apply cop_perp2__col with D E; Perp; Cop.
apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong.
Qed.

Lemma perp_bisect_cop2_existence : forall A B C,
  A <> B -> exists P, exists Q, Perp_bisect P Q A B /\ 共面 A B C P /\ 共面 A B C Q.
Proof.
intros A B C HDiff.
destruct (midpoint_existence A B) as [M HM].
destruct (ex_perp_cop A B M C HDiff) as [Q []].
exists M; exists Q; unfold Perp_bisect.
repeat split; Cop.
  exists M; split; Col; 中点.
  left; Perp.
Qed.

Lemma perp_bisect_existence :
  forall A B, A <> B -> exists P, exists Q, Perp_bisect P Q A B.
Proof.
intros A B HDiff.
destruct (perp_bisect_cop2_existence A B A HDiff) as [P [Q []]].
exists P; exists Q; assumption.
Qed.

Lemma perp_bisect_existence_cop : forall A B C,
  A <> B -> exists P, exists Q, Perp_bisect P Q A B /\ 共面 A B C P /\
                                共面 A B C Q.
Proof.
intros A B C HDiff.
destruct (midpoint_existence A B) as [M HM].
destruct (ex_perp_cop A B M C) as [Q [HQ HCop]]; auto.
exists M; exists Q; unfold Perp_bisect.
repeat split; Perp; [|Cop].
exists M; split; [中点|Col].
Qed.

End PerpBisect_3.