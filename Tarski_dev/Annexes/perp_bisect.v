Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

Section PerpBisect_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 中垂线两定义等价 :
  forall P Q A B, 中垂线 P Q A B <-> 中垂线_另一定义 P Q A B.
Proof.
intros; unfold 中垂线; unfold 中垂线_另一定义; unfold 严格对称; split.

  {
  intro H; destruct H as [[[X [HMid HCol]] HPerp] HDiff].
  exists X; split; 中点.
  elim HPerp; clear HPerp; intro HPerp; [|exfalso;auto].
  apply l8_14_2_1b_bis_交点是垂点; Col; Perp.
  }

  {
  intro H; destruct H as [I [HPerp HMid]].
  统计不重合点; split; Col.
  split; try (left; apply l8_14_2_1a_垂直于转垂直 with I); Perp.
  exists I; split; 中点.
  unfold 垂直于 in *; 分离合取式; Col.
  }
Qed.

Lemma 中垂线左对称性 :
 forall P Q A B,
  中垂线 P Q A B ->
  中垂线 Q P A B.
Proof.
intros.
apply 中垂线两定义等价 in H.
apply 中垂线两定义等价.
unfold 中垂线_另一定义 in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma 中垂线右对称性 :
 forall P Q A B,
  中垂线 P Q A B ->
  中垂线 P Q B A.
Proof.
intros.
apply 中垂线两定义等价 in H.
apply 中垂线两定义等价.
unfold 中垂线_另一定义 in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma 中垂线对称性 : forall A B C D,
 中垂线 A B C D ->
 中垂线 B A D C.
Proof.
intros.
apply 中垂线左对称性.
apply 中垂线右对称性.
trivial.
Qed.

Lemma 中垂线蕴含垂直 :
 forall P Q A B,
  中垂线 P Q A B ->
  Perp P Q A B.
Proof.
intros.
apply 中垂线两定义等价 in H.
unfold 中垂线_另一定义 in *.
decompose [and ex] H;clear H.
unfold Perp.
exists x.
assumption.
Qed.

End PerpBisect_1.

Hint Resolve 中垂线蕴含垂直 : perp.

Section PerpBisect_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 中垂线顶点距线两端等长1 :
 forall P Q A B,
 中垂线 P Q A B ->
 Cong A P B P.
Proof.
intros.
apply 中垂线两定义等价 in H.
unfold 中垂线_另一定义 in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong P A P B).
apply (直角端点和其关于顶点的对称点与另一端点等距 P I A B);
eauto with perp.
Cong.
Qed.

Lemma 中垂线顶点距线两端等长2 :
 forall P Q A B,
 中垂线 P Q A B ->
 Cong A Q B Q.
Proof.
intros.
apply 中垂线两定义等价 in H.
unfold 中垂线_另一定义 in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong Q A Q B).
apply (直角端点和其关于顶点的对称点与另一端点等距 Q I A B);
eauto with perp.
Cong.
Qed.

End PerpBisect_2.

Hint Resolve 中垂线顶点距线两端等长1 中垂线顶点距线两端等长2 : cong.

Section PerpBisect_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 中垂线顶点距线两端等长 :
 forall P Q A B,
 中垂线 P Q A B ->
 Cong A P B P /\ Cong A Q B Q.
Proof.
intros.
split.
eauto using 中垂线顶点距线两端等长1.
eauto using 中垂线顶点距线两端等长2.
Qed.
(* 无用，显而易见，不翻译 *)
Lemma perp_bisect_cong :
 forall A A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 中垂线 O A1 B C -> 中垂线 O B1 A C -> 中垂线 O C1 A B ->
 Cong A O B O -> Cong B O C O ->
 Cong A O C O.
Proof.
intros.
apply (等长的传递性 A O B O C O); assumption.
Qed.

Lemma 距线两端点等距两点连线为该线中垂线 :
 forall P Q A B,
 P <> Q -> A <> B ->
 共面 P Q A B ->
 Cong A P B P ->
 Cong A Q B Q ->
 中垂线 P Q A B.
Proof.
intros.
apply 中垂线两定义等价.
unfold 中垂线_另一定义.
elim (中点的存在性 A B).
intros I HI.
exists I.
split;try assumption.
assert (Per P I A)
 by (exists B; split; Cong).

show_distinct A I.
unfold 中点 in *.
分离合取式.
treat_equalities.
intuition.

show_distinct B I.
unfold 中点 in *.
分离合取式.
treat_equalities.
intuition.

induction(两点重合的决定性 P I).
subst.
eapply l8_13_2_两线夹角为直角则两线垂直;Col.
exists Q. exists B;repeat split;Col.
unfold Per.
exists A.
split.
中点.
Cong.

eapply l8_13_2_两线夹角为直角则两线垂直.
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

apply 中点蕴含共线;auto.
exists P.
exists A.
repeat split;Col.
Qed.

Lemma 距线两端点等距点与中点连线为该线中垂线 :
 forall P Q A B,
 P <> Q -> A <> B ->
 Cong A P B P ->
 中点 Q A B ->
 中垂线 P Q A B.
Proof.
intros.
apply 距线两端点等距两点连线为该线中垂线; Cong; Cop.
Qed.
(* 无用 *)
Lemma 三角形两边中垂线交点也在第三条中垂线上 :
 forall A B C P,
  在中垂线上 P A B ->
  在中垂线上 P B C ->
  在中垂线上 P A C.
Proof.
intros.
unfold 在中垂线上 in *.
CongR.
Qed.

Lemma 过一线中点的垂线是该线中垂线 : forall A B C D,
 中点 C A B -> Perp C D A B ->
 中垂线 C D A B.
Proof.
intros.
apply 中垂线两定义等价.
unfold 中垂线_另一定义 in *.
exists C.
split; auto.
apply l8_14_2_1b_bis_交点是垂点; Col.
Qed.

Lemma 距线两端等长的点在中垂线上 : forall A B C D E,
  共面 A C D E ->
  共面 B C D E ->
  Cong C D C E ->
  中垂线 A B D E ->
  Col A B C.
Proof.
intros A B C D E HCop1 HCop2 HCong1 HPerp.
assert (HCong2 := HPerp); apply 中垂线顶点距线两端等长 in HCong2; destruct HCong2 as [HCong2 Hc]; clear Hc.
apply 中垂线两定义等价 in HPerp.
destruct HPerp as [F [HPerp [HBet HCong3]]].
assert (HDE : D <> E) by (统计不重合点; auto).
assert (HCol := HPerp); apply 垂点是交点 in HCol; destruct HCol as [HCol Hc]; clear Hc.
apply l8_14_2_1a_垂直于转垂直 in HPerp.
elim (两点重合的决定性 A C); intro; try (subst; Col).
apply cop_perp2__col with D E; Perp; Cop.
apply 中垂线蕴含垂直; apply 距线两端点等距两点连线为该线中垂线; Cong.
Qed.
(* 半无用 *)
Lemma 任意不同两点都能作出与另两点共面的中垂线 : forall A B C,
  A <> B -> exists P, exists Q, 中垂线 P Q A B /\ 共面 A B C P /\ 共面 A B C Q.
Proof.
intros A B C HDiff.
destruct (中点的存在性 A B) as [M HM].
destruct (ex_perp_cop A B M C HDiff) as [Q []].
exists M; exists Q; unfold 中垂线.
repeat split; Cop.
  exists M; split; Col; 中点.
  left; Perp.
Qed.

Lemma 中垂线的存在性 :
  forall A B, A <> B -> exists P, exists Q, 中垂线 P Q A B.
Proof.
intros A B HDiff.
destruct (任意不同两点都能作出与另两点共面的中垂线 A B A HDiff) as [P [Q []]].
exists P; exists Q; assumption.
Qed.
(* 半无用 *)
Lemma 共面中垂线的存在性 : forall A B C,
  A <> B -> exists P, exists Q, 中垂线 P Q A B /\ 共面 A B C P /\
                                共面 A B C Q.
Proof.
intros A B C HDiff.
destruct (中点的存在性 A B) as [M HM].
destruct (ex_perp_cop A B M C) as [Q [HQ HCop]]; auto.
exists M; exists Q; unfold 中垂线.
repeat split; Perp; [|Cop].
exists M; split; [中点|Col].
Qed.

End PerpBisect_3.