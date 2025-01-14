Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.

Section Orientation.

Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.

Definition proj := fun  T A B P => A <> B /\ (~Col A B T /\ Perp A B T P /\ Col A B P \/ Col A B T /\ P = T).

Lemma proj_exists : forall A B T, A <> B -> exists P, proj T A B P.
Proof.
intros.
induction(共线的决定性 A B T).
exists T.
unfold proj.
split.
assumption.
right.
split;
auto.
assert(HH:=l8_18_过一点垂线之垂点的存在性 A B T H0).
ex_and HH P.
exists P.
unfold proj.
split.
assumption.
left.
repeat split;auto.
Qed.

Lemma proj_per : forall A B T P, A <> B -> proj T A B P -> Per T P A /\ Per T P B /\ Col A B P.
Proof.
intros.
unfold proj in H0.
分离合取式.
induction H1.
分离合取式.
repeat split.

induction (两点重合的决定性 A P).
treat_equalities.
apply 角ABB成直角.

apply L形垂直于转直角.
eauto with perp.

induction (两点重合的决定性 B P).
treat_equalities.

apply 角ABB成直角.

apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
assumption.

eauto with perp.
Col.
assumption.
分离合取式.
subst T.
repeat split.
Perp.
Perp.
assumption.
Qed.

Lemma proj_uniqueness : forall A B T P P', proj T A B P -> proj T A B P' -> P = P'.
Proof.
intros.
unfold proj in *.
分离合取式.
induction H1; induction H2; 分离合取式; assert(Col A P P').
ColR.
eapply (l8_18_过一点垂线之垂点的唯一性 A B T P P');
auto.
subst T.
contradiction.
contradiction.
subst P'.
ColR.
subst P'.
contradiction.
subst T.
subst P'.
Col.
subst T.
subst P'.
reflexivity.
Qed.


Lemma proj_col : forall T P A B, proj T A B P -> Col P A B.
Proof.
intros.
unfold proj in H.
分离合取式.
induction H0; 分离合取式.
Col.
subst T.
Col.
Qed.

Lemma proj_col_proj : forall A B C T P, proj T A B P -> A <> C -> Col A B C -> proj T A C P.
Proof.
intros.
unfold proj in *.
分离合取式.
induction H2; repeat split; auto; 分离合取式.
left.
repeat split.
intro.
apply H2.
ColR.

eapply (垂线共线点也构成垂直1 _ B); auto.
ColR.
subst T.
right.
split; auto.
ColR.
Qed.

Lemma per_proj : forall A B T P, A <> B -> Per T P A -> Per T P B -> Col A B P -> proj T A B P.
Proof.
intros.
unfold proj.
split; auto.
induction (共线的决定性 A B T).
right.
split; auto.

assert(Col T P A).
ColR.
assert(Col T P B).
ColR.

induction(两点重合的决定性 A P).
subst P.
assert(T=A \/ B=A).
apply l8_9_直角三点共线则必有两点重合; auto.
induction H6.
auto.
subst B.
tauto.

assert(T=P \/ A=P).
apply l8_9_直角三点共线则必有两点重合; auto.
induction H7.
auto.
subst P.
tauto.

left.

induction (两点重合的决定性 A P).

subst P.

repeat split; auto.

apply 直角转L形垂直于 in H1.
apply 垂直于的交换性 in H1.
apply 垂直于转T形垂直 in H1.
induction H1.
Perp.

apply 垂直推出不重合1 in H1.
tauto.
intro.
subst T.
contradiction.
assumption.

repeat split; auto.
apply 直角转L形垂直于 in H0.
apply 垂直于的交换性 in H0.
apply 垂直于转T形垂直 in H0.
induction H0.
eapply 垂线共线点也构成垂直1.
assumption.
eauto with perp.

Col.
apply 垂直推出不重合1 in H0.
tauto.
intro.
subst T.
contradiction.
auto.
Qed.


Definition eqo := fun A B P A1 B1 P1 => ~Col A B P /\ ~Col A1 B1 P1 /\
                      forall C C1 B2 M B' C' K,
                             Perp A B C A  -> Per P C A -> Perp A1 B1 C1 A1 -> Per P1 C1 A1 ->
                             Out A1 B1 B2 -> Cong A B A1 B2 ->
                             中点 M A A1 -> 中点 M B2 B' -> 中点 M C1 C' -> 中点 K B B' ->
                             Bet C A C' \/ OS A K C C'.



Definition eq_o := fun A B P A1 B1 P1 => ~Col A B P /\ ~Col A1 B1 P1 /\
                      forall C C1 B2 M B' C' K,
                             Perp A B C A -> proj P A C C -> Perp A1 B1 C1 A1 -> proj P1 A1 C1 C1 ->
                             Out A1 B1 B2 -> Cong A B A1 B2 ->
                             中点 M A A1 -> 中点 M B2 B' -> 中点 M C1 C' -> 中点 K B B' ->
                             Bet C A C' \/ OS A K C C'.

Lemma eqo_eq_o : forall A B P A1 B1 P1, eqo A B P A1 B1 P1 -> eq_o A B P A1 B1 P1.
Proof.
intros.
unfold eqo in H.
分离合取式.
unfold eq_o.
repeat split ; auto.
intros.
assert(HH:= H1 C C1 B2 M B' C' K).
apply HH; auto.
unfold proj in *.
分离合取式.
induction H13; induction H12.
分离合取式.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的对称性.
Perp.
分离合取式.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的对称性.
Perp.
分离合取式.
subst P.
apply 直角的对称性.
apply 角ABB成直角.
分离合取式.
subst P.
apply 直角的对称性.
apply 角ABB成直角.
unfold proj in *.
分离合取式.
induction H13; induction H12.
分离合取式.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的对称性.
Perp.
分离合取式.
subst P1.
apply 直角的对称性.
apply 角ABB成直角.
分离合取式.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的对称性.
Perp.
分离合取式.
subst P1.
apply 直角的对称性.
apply 角ABB成直角.
Qed.




Lemma eq_o_eqo : forall A B P A1 B1 P1, eq_o A B P A1 B1 P1 -> eqo A B P A1 B1 P1.
Proof.
intros.
unfold eq_o in H.
分离合取式.
unfold eqo.
repeat split; auto.
intros.
eapply H1.
apply H2.
apply per_proj.
apply 垂直推出不重合2 in H2.
auto.
assumption.
apply 角ABB成直角.
Col.
apply H4.
apply per_proj.
apply 垂直推出不重合2 in H4.
auto.
assumption.
apply 角ABB成直角.
Col.
apply H6.
assumption.
apply H8.
apply H9.
assumption.
assumption.
Qed.



Lemma eq_o_one_side : forall A B X Y, eq_o A B X A B Y -> OS A B X Y.
Proof.
intros.
unfold eq_o in H.
分离合取式.
assert(A <> B).
intro.
subst B.
apply H.
Col.

assert(HH:=ex_四点成首末边等长双直角S形则对边等长 B A A X A B).
assert(exists P : Tpoint, Per P A B /\ Cong P A A B /\ OS B A P X).
apply HH;
auto.
Col.
intro.
apply H.
Col.
clear HH.
ex_and H3 T.

assert(A <> T).
intro.
subst T.
apply 等长的对称性 in H4.
apply 等长的同一性 in H4.
contradiction.

assert(Perp T A A B).
apply 直角转L形垂直于 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
apply 垂直推出不重合1 in H3.
tauto.
assumption.
auto.
assumption.

assert(HH:=proj_exists A T X H6).
ex_and HH PX.
assert(HH:=proj_exists A T Y H6).
ex_and HH PY.
prolong B A B' B A.
prolong PY A C' PY A.
assert(Col PX A T).
eapply proj_col.
apply H8.
assert(Col PY A T).
eapply proj_col.
apply H9.

assert(PX <> A).
intro.
subst PX.
apply proj_per in H8.
分离合取式.
apply H.
apply 等价共线CAB.
eapply per2__col.
apply 直角的对称性.
apply H3.
assumption.
assumption.
assumption.

assert(PY <> A).
intro.
subst PY.
apply proj_per in H9.
分离合取式.
apply H0.
apply 等价共线CAB.
eapply per2__col.
apply 直角的对称性.
apply H3.
assumption.
assumption.
assumption.

assert(~Col T A B).
apply 成直角三点不共线 in H3.
assumption.
auto.
assumption.

assert(Col A PX PY).
ColR.

assert(~Col PX A B).
intro.
apply H18.
ColR.

assert(~Col PY A B).
intro.
apply H18.
ColR.

assert(A <> C').
intro.
subst C'.
apply 等长的对称性 in H13.
apply 等长的同一性 in H13.
contradiction.

assert(TS A B PY C').
unfold TS.
repeat split; auto.
intro.
apply H21.
apply 中间性蕴含共线1 in H12.
ColR.
exists A.
split.
Col.
assumption.

assert(HH:= H1 PX PY B A B' C' A).

assert(Bet PX A C' \/ OS A A PX C').
apply HH;
clear HH; clear H1.

apply 直角转L形垂直于 in H3.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
apply 垂直的交换性.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
auto.
apply H1.
Col.
apply 垂直推出不重合1 in H1.
tauto.
auto.
assumption.

eapply proj_col_proj.
apply H8.
auto.
Col.

apply 直角转L形垂直于 in H3.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
apply 垂直的交换性.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
auto.
apply H1.
Col.
apply 垂直推出不重合1 in H1.
tauto.
auto.
assumption.

eapply proj_col_proj.
apply H9.
auto.
Col.

apply out_trivial.
auto.
apply 等长的自反性.
apply A是AA中点.
unfold 中点.
apply 等长的对称性 in H11.
split;auto.
unfold 中点.
apply 等长的对称性 in H13.
split;auto.
unfold 中点.
apply 等长的对称性 in H11.
split;auto.

clear H1 HH.

assert(TS A B PX C').
unfold TS.
repeat split; auto.
intro.
apply H21.
apply 中间性蕴含共线1 in H12.
ColR.
exists A.
induction H24.
split.
Col.
assumption.
unfold OS in H1.
ex_and H1 U.
unfold TS in H1.
分离合取式.
统计不重合点; tauto.

unfold proj in H8.
分离合取式.
induction H25.
分离合取式.

assert(Par A B X PX).
apply l12_9_2D with T A.
apply 垂直的对称性.
apply H7.
apply 垂直的右交换性.
Perp.

assert(严格平行 A B X PX).
induction H28.
assumption.
分离合取式.
apply False_ind.
apply H.
ColR.

unfold proj in H9.
分离合取式.
induction H30.
分离合取式.

assert(Par A B Y PY).
apply l12_9_2D with T A.
apply 垂直的对称性.
apply H7.
apply 垂直的右交换性.
Perp.

assert(严格平行 A B Y PY).
induction H33.
assumption.
分离合取式.
apply False_ind.
apply H0.
ColR.
apply l12_6 in H29.
apply l12_6 in H34.

assert(TS A B X C').
eapply l9_8_2.
apply H1.
apply one_side_symmetry.
assumption.

assert(TS A B Y C').
eapply l9_8_2.
apply H23.
apply one_side_symmetry.
assumption.
eapply l9_8_1.
apply H35.
assumption.
分离合取式.
subst Y.
apply l12_6 in H29.
eapply one_side_transitivity.
apply H29.
eapply l9_8_1.
apply H1.
assumption.
分离合取式.
subst X.
unfold proj in H9.
分离合取式.
induction H26.
分离合取式.

assert(Par A B Y PY).
apply l12_9_2D with T A.
apply 垂直的对称性.
apply H7.
apply 垂直的右交换性.
Perp.

assert(严格平行 A B Y PY).
induction H29.
assumption.
分离合取式.
apply False_ind.
apply H0.
ColR.
apply l12_6 in H30.
eapply one_side_transitivity.
eapply l9_8_1.
apply H1.
apply H23.
apply one_side_symmetry.
assumption.
分离合取式.
subst Y.
eapply l9_8_1.
apply H1.
assumption.
Qed.


Lemma eqo_one_side : forall A B X Y, eqo A B X A B Y -> OS A B X Y.
Proof.
intros.
apply eqo_eq_o in H.
apply eq_o_one_side.
assumption.
Qed.


Lemma eq_o_refl : forall A B P, ~Col A B P -> eq_o A B P A B P.
Proof.
intros.
unfold eq_o.
repeat split; auto.
intros.
unfold 中点 in H8.
apply M是AA中点则M与A重合 in H6.
subst M.
分离合取式.
assert(proj P A C C1).
eapply proj_col_proj.
apply H3.
apply 垂直推出不重合2 in H0.
auto.
eapply perp2__col.
apply 垂直的交换性.
apply 垂直的对称性.
apply H2.
apply 垂直的交换性.
Perp.
assert(C=C1).
eapply proj_uniqueness.
apply H1.
assumption.
subst C1.
left.
assumption.
Qed.

Lemma eqo_refl : forall A B P, ~Col A B P -> eqo A B P A B P.
Proof.
intros.
apply eq_o_eqo.
apply eq_o_refl.
assumption.
Qed.

Lemma per_id : forall A B B' C, A <> B -> B <> C -> B' <> C -> Per A B C -> Per A B' C -> Col C B B' -> B = B'.
Proof.
intros.
assert(~ Col A B C).
eapply 成直角三点不共线.
assumption.
assumption;
assert(Per B B' C).
eapply (l8_3_直角边共线点也构成直角1 A); try auto.
Col.

assert(A <> B').
intro.
subst B'.
apply H5.
Col.

assert(Per A B B').
eapply (直角边共线点也构成直角2 _ _ C); auto.
Col.
assert(Per A B' B).
eapply (直角边共线点也构成直角2 _ _ C); auto.
Col.
eapply ABC和ACB均直角则B与C重合.
apply H7.
assumption.
Qed.


Lemma proj_one_side : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' -> Col B A A' \/ OS A A' B B'.
Proof.
intros.

induction (共线的决定性 B A A').
left.
assumption.
induction(两点重合的决定性 B B').
subst B'.
right.
apply one_side_reflexivity.
assumption.

assert(Par A A' B B').
unfold proj in *.
分离合取式.
induction H5; induction H4;分离合取式.
eapply l12_9_2D.
apply 垂直的对称性.
apply H8.
Perp.
subst B'.
tauto.
subst A'.
tauto.
subst B'.
tauto.
assert(严格平行 A A' B B').
induction H4.
assumption.
分离合取式.
apply False_ind.
apply H2.
ColR.
right.
eapply l12_6.
assumption.
Qed.


Lemma proj_eq_col : forall A B P Q C, proj A P Q C -> proj B P Q C -> Col A B C.
Proof.
intros.
unfold proj in *.
分离合取式.
induction H2; induction H1; 分离合取式.
apply 等价共线BCA.
eapply perp2__col.
apply 垂直的对称性.
apply 垂直的交换性.
apply H5.
apply 垂直的对称性.
Perp.
subst B.
Col.
subst C.
Col.
subst C.
Col.
Qed.

Lemma proj_par : forall A B A' B' P Q, A <> A' -> B <> B' -> proj A P Q A' -> proj B P Q B' -> Par A A' B B'.
Proof.
intros.
eapply l12_9_2D.
unfold proj in *.
分离合取式.
induction H4; induction H3; 分离合取式.
apply 垂直的对称性.
apply H7.
Perp.
subst A'.
tauto.
subst B'.
tauto.
unfold proj in *.
分离合取式.
induction H4; induction H3; 分离合取式.
apply 垂直的对称性.
apply H5.
subst B'.
tauto.
subst A'.
tauto.
subst A'.
tauto.
Qed.

Lemma proj_not_col : forall A A' P Q, A <> A' -> proj A P Q A' -> ~Col P Q A.
Proof.
intros.
unfold proj in H0.
分离合取式.
induction H1.
分离合取式.
assumption.
分离合取式.
subst A'.
tauto.
Qed.

Lemma proj_comm : forall A B P Q, proj A P Q B -> proj A Q P B.
Proof.
intros.
unfold proj in *.
分离合取式.
induction H0; 分离合取式; split; auto.
left.
repeat split.
intro.
apply H0.
Col.
Perp.
Col.
subst B.
right.
split; Col.
Qed.

Lemma proj_not_eq : forall A B A' B' P Q, A' <> B' -> proj A P Q A' -> proj B P Q B' -> A <> B.
Proof.
intros.
intro.
apply H.
eapply proj_uniqueness.
apply H0.
subst B.
assumption.
Qed.

Lemma proj_not_eq_not_col : forall A B A' B' P Q, A' <> B' -> A <> A' -> proj A P Q A' -> proj B P Q B' -> ~Col A A' B'.
Proof.
intros.
unfold proj in H1.
分离合取式.
induction H3; 分离合取式.
assert(Col P Q B').
apply 等价共线BCA.
eapply proj_col.
apply H2.

induction(两点重合的决定性 P A').
subst P.

assert(Perp A' B' A A').
apply 垂线共线点也构成垂直1 with Q.
auto.
apply 垂直的左交换性.
apply 垂线共线点也构成垂直1 with A'.
auto.
apply 垂直的左交换性.
apply H4.
Col.
Col.
assert(~Col A' A B').
eapply L形垂直推出不共线.
apply 垂直的交换性.
Perp.
intro.
apply H8.
Col.

assert(Perp A' B' A A').
apply 垂线共线点也构成垂直1 with P.
assumption.
apply 垂直的左交换性.
apply 垂线共线点也构成垂直1 with Q.
auto.
assumption.
assumption.
ColR.
assert(~Col A' A B').
eapply L形垂直推出不共线.
apply 垂直的交换性.
Perp.
intro.
apply H9.
Col.
subst A'.
tauto.
Qed.

Lemma proj_par_strict : forall A B A' B' P Q, A <> A' -> B <> B' -> A' <> B' -> proj A P Q A' -> proj B P Q B' -> 严格平行 A A' B B'.
Proof.
intros.
assert(Par A A' B B').
eapply (proj_par A B A' B' P Q); auto.
induction H4.
assumption.
分离合取式.
unfold 严格平行.
repeat split; auto; try apply all_coplanar.
intro.
ex_and H8 X.

assert(~Col P Q A).
eapply proj_not_col.
apply H.
assumption.

assert(~Col P Q B).
eapply proj_not_col.
apply H0.
assumption.

assert(A <> B).
eapply proj_not_eq.
apply H1.
apply H2.
assumption.

assert(Col A' P Q).
eapply proj_col.
apply H2.

assert(Col B' P Q).
eapply proj_col.
apply H3.

apply H1.
eapply (l6_21_两线交点的唯一性 P Q).
apply H11.
apply H0.
Col.
Col.
Col.
Col.
Qed.

Lemma col_proj_col : forall A B A' B' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q B' -> Col A B B'.
Proof.
intros.
induction(两点重合的决定性 A B).
subst B.
Col.
unfold proj in *.
分离合取式.
induction H4; induction H5; 分离合取式.
apply 等价共线CAB.
eapply perp2__col.
apply 垂直的对称性.
apply H6.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
assumption.
apply 垂直的对称性.
apply H8.
Col.
subst A'.
tauto.
subst B'.
Col.
subst B'.
Col.
Qed.

Lemma col_proj_proj : forall A B A' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q A'.
Proof.
intros.

unfold proj in *.
分离合取式.
induction H2;
分离合取式; split;auto.
induction(共线的决定性 P Q B).
right.
split.
assumption.

induction(两点重合的决定性 A' P).
subst P.
assert(垂直于 A' A' Q A A').
eapply L形垂直转垂直于.
assumption.
eapply l8_14_2_1b_垂点是交点.
apply H6.
Col.
Col.
assert(Perp P A' A A').
eapply 垂线共线点也构成垂直1.
auto.
apply H3.
assumption.

assert(垂直于 A' A' P A A').
eapply L形垂直转垂直于.
Perp.

induction(两点重合的决定性 B P).
subst P.

assert(Perp B Q A B).
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
intro.
subst B.
apply H2.
Col.
apply 垂直的对称性.
apply H3.
Col.
eapply l8_14_2_1b_垂点是交点.
apply H8.
Col.
Col.

assert(Perp P B A B).
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
intro.
subst B.
contradiction.
apply 垂直的对称性.
apply H3.
Col.
Col.
eapply l8_14_2_1b_垂点是交点.
apply H8.
ColR.
Col.
left.
repeat split; auto.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
intro.
subst A'.
contradiction.
apply 垂直的对称性.
apply 垂直的右交换性.
apply H3.
Col.
subst A'.
tauto.
Qed.



Lemma proj_id : forall A B A' B' P Q, A <> A' -> Col A B A' -> proj A P Q A' -> proj B P Q B' -> A'= B'.
Proof.
intros.

assert(proj B P Q A').
eapply col_proj_proj.
apply H.
assumption.
assumption.
eapply proj_uniqueness.
apply H3.
assumption.
Qed.

Lemma proj_diff : forall A P Q A' , proj A P Q A' -> P <> Q.
Proof.
intros.
unfold proj in H.
分离合取式.
assumption.
Qed.


Lemma proj3_col : forall A B C A' B' C' P Q , proj A P Q A' -> proj B P Q B' -> proj C P Q C' -> Col A' B' C'.
Proof.
intros.
unfold proj in *.
分离合取式.

induction H4; induction H3; induction H2; 分离合取式.
eapply (共线的传递性4 P Q); Col.
subst C'.
eapply (共线的传递性4 P Q); Col.
subst B'.
eapply (共线的传递性4 P Q); Col.
subst C'.
subst B'.
eapply (共线的传递性4 P Q); Col.
subst A'.
eapply (共线的传递性4 P Q); Col.
subst C'.
subst A'.
eapply (共线的传递性4 P Q); Col.
subst A'.
subst B'.
eapply (共线的传递性4 P Q); Col.
subst A'.
subst B'.
subst C'.
eapply (共线的传递性4 P Q); Col.
Qed.

Lemma proj3_id : forall A B C C' P Q, A <> B -> Col A B C -> proj A P Q A -> proj B P Q B -> proj C P Q C' -> C = C'.
Proof.
intros.
assert(Col A B C').
eapply (proj3_col A B C A B C' P Q); auto.

assert(HH1:= H1).
assert(HH2:=H2).
assert(HH3:=H3).

unfold proj in HH1.
unfold proj in HH2.
unfold proj in HH3.
分离合取式.
induction H10; induction H8; induction H6; 分离合取式.
apply 垂直推出不重合2 in H15.
tauto.
apply 垂直推出不重合2 in H14.
tauto.
apply 垂直推出不重合2 in H14.
tauto.
apply 垂直推出不重合2 in H13.
tauto.
apply 垂直推出不重合2 in H13.
tauto.
apply 垂直推出不重合2 in H12.
tauto.
assert(Col P A B).
ColR.
assert(Col Q A B).
ColR.


assert(Col P Q C).
eapply (共线的传递性4 A B); Col;


eapply (l8_14_2_1b_bis_交点是垂点 _ _ _ _ C') in H7.
contradiction.
subst C.
reflexivity.
Qed.

Lemma proj_inv_exists : forall P Q A', P <> Q -> Col P Q A'  -> exists A, A <> A' /\ proj A P Q A'.
Proof.
intros.
assert(HH0:= 两点不重合则存在不共线的点 P Q H).
ex_and HH0 X.

induction(两点重合的决定性 A' P).
subst P.

assert(Q <> A').
intro.
apply H.
auto.
apply 等价共线BCA in H0.
assert(~Col Q A' X).
intro.
apply H1.
Col.
assert(HH:= ex_四点成首末边等长双直角S形则对边等长 Q A' A' X A' Q H2 H H0 H3).
ex_and HH A.
exists A.
split.
intro.
subst A'.
apply 等长的对称性 in H5.
apply 等长的同一性 in H5.
contradiction.
eapply per_proj; auto.
apply 角ABB成直角.
Col.
assert(HH:= ex_四点成首末边等长双直角S形则对边等长 P Q A' X P Q H H H0 H1).
ex_and HH A.
exists A.
split.
intro.
subst A'.
apply 等长的对称性 in H4.
apply 等长的同一性 in H4.
contradiction.
apply per_proj; auto.
apply 直角边共线点也构成直角2 with P.
auto.
assumption.
Col.
Qed.

Lemma proj_perp_id : forall A B C A' B' P Q, A <> C -> Col A B C -> 
                                                         proj A P Q A' -> proj B P Q B' -> proj C P Q A' ->
                                                         A' = B'.
Proof.
intros.

induction(两点重合的决定性 A A').
subst A'.

apply proj_id with C B P Q; Col.

assert(Col A C A').
eapply proj_eq_col.
apply H1.
assumption.
assert(Col A B A').
ColR.

eapply proj_id.
apply H4.
apply H6.
apply H1.
assumption.
Qed.

Lemma proj_diff_not_col : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' ->  (A' <> B' <-> ~Col A B A').
Proof.
intros.
split.
intro.

intro.
assert(proj B P Q A').
eapply (col_proj_proj A); auto.
apply H2.
eapply proj_uniqueness.
apply H4.
assumption.
intro.
intro.
subst B'.
apply H2.
eapply (proj_eq_col _ _ P Q); auto.
Qed.

Lemma proj_diff_not_col_inv : forall A B A' B' P Q, A <> A' -> proj A P Q A' -> proj B P Q B' ->  (A' = B' <-> Col A B A').
Proof.
intros.
split.
intro.
subst B'.
eapply (proj_eq_col A B P Q A'); auto.
intro.
eapply (proj_id A B A' B' P Q); auto.
Qed.

Lemma proj_preserves_bet1 : forall A B C B' C' P Q, Bet A B C -> 
                                                         proj A P Q A -> proj B P Q B' -> proj C P Q C' ->
                                                         Bet A B' C'.
Proof.
intros.
induction(两点重合的决定性 A B).
subst B.
assert(A = B').
eapply proj_uniqueness.
apply H0.
assumption.
subst B'.
apply AAB中间性.
induction(两点重合的决定性 B C).
subst C.
assert(B' = C').
eapply proj_uniqueness.
apply H1.
assumption.
subst C'.
apply ABB中间性.
assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H.
contradiction.

assert(P <> Q).
eapply proj_diff.
apply H0.
assert(Col A P Q).
eapply proj_col.
apply H0.
assert(Col B' P Q).
eapply proj_col.
apply H1.
assert(Col C' P Q).
eapply proj_col.
apply H2.

assert(Col A B C).
eapply 中间性蕴含共线1.
assumption.

induction(两点重合的决定性 B B').
subst B'.

assert(C = C').

apply (proj3_id A B C C' P Q); Col.
subst C'.
assumption.

induction (两点重合的决定性 A C').
subst C'.

assert(Col P A B').
ColR.
assert(proj B P Q A).
apply col_proj_proj with C.
auto.
Col.
assumption.
assert(A = B').
eapply proj_uniqueness.
apply H13.
assumption.
subst B'.
apply A是AA中点.

induction(两点重合的决定性 B' C').
subst C'.
apply ABB中间性.

assert(HH:= proj_not_eq_not_col B C B' C' P Q H13 H11 H1 H2).

assert(A <> B').
intro.
subst B'.

assert(Col B C C').
apply col_proj_col with A P Q; Col.
apply HH.
ColR.

assert(HH1:= proj_one_side B C B' C' P Q H11 H1 H2).

assert(Col A B' C').
eapply proj3_col.
apply H0.
apply H1.
apply H2.
induction HH1.

apply False_ind.
apply HH.
assert(Col A B B').
ColR.
ColR.

assert(TS B B' A C).
unfold TS.
repeat split.
assert(~Col B B' A).
eapply proj_not_eq_not_col; auto.
apply H1.
apply H0.
intro.
apply H17.
Col.
intro.
apply HH.
apply 等价共线CAB.
eapply (共线的传递性2 _ A).
auto.
Col.
ColR.
exists B.
split; Col.

assert(TS B B' A C').
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H17.
assumption.
unfold TS in H18.
分离合取式.
ex_and H20 BB.

assert(BB= B').
apply (l6_21_两线交点的唯一性 B B' C' A); Col.

subst BB.
assumption.
Qed.

Lemma proj_preserves_bet : forall A B C A' B' C' P Q, Bet A B C -> 
                                                         proj A P Q A' -> proj B P Q B' -> proj C P Q C' ->
                                                         Bet A' B' C'.
Proof.
intros.


induction(两点重合的决定性 A B).
subst B.
assert(A' = B').
eapply proj_uniqueness.
apply H0.
assumption.
subst B'.
apply AAB中间性.
induction(两点重合的决定性 B C).
subst C.
assert(B' = C').
eapply proj_uniqueness.
apply H1.
assumption.
subst C'.
apply ABB中间性.
assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H.
contradiction.

induction (两点重合的决定性 A' C').
subst C'.

assert(A' = B').
apply proj_perp_id with A B C P Q; Col.
subst B'.
apply A是AA中点.

assert(P <> Q).
eapply proj_diff.
apply H0.
assert(Col A' P Q).
eapply proj_col.
apply H0.
assert(Col B' P Q).
eapply proj_col.
apply H1.
assert(Col C' P Q).
eapply proj_col.
apply H2.

assert(Col A B C).
eapply 中间性蕴含共线1.
assumption.

induction (两点重合的决定性 A A').
subst A'.
eapply (proj_preserves_bet1 A B C _ _ P Q); assumption.

assert(~Col A P Q).
intro.

apply proj_not_col in H0.
apply H0.
Col.
assumption.

induction (两点重合的决定性 B B').
subst B.

assert(C <> C').
intro.
subst C'.
apply H13.
assert(Col B' C P).
ColR.
assert(Col B' C Q).
ColR.
eapply (共线的传递性4 B' C); Col.
apply 等价共线BCA in H9.

assert(~Col C P Q).
intro.
apply proj_not_col in H2.
apply H2.
Col.
assumption.

assert(HH:= proj_inv_exists P Q B' H7 H9).
ex_and HH B.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H16 H17 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H16 H17 H2).
destruct HH.

assert(HH:= proj_one_side B A B' A' P Q H16 H17 H0).
induction HH.
assert(B' = A').
apply H19.
Col.
subst B'.
apply AAB中间性.

assert(HH:= proj_one_side B C B' C' P Q H16 H17 H2).
induction HH.

assert(B' = C').
apply H21.
Col.
subst B'.
apply ABB中间性.

(*********************************************)


assert(HH:=proj_diff_not_col_inv B A B' A' P Q H16 H17 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H16 H17 H2).
destruct HH.

assert(TS B B' A C).
unfold TS.
repeat split.

intro.
assert(B' = A').
apply H25.
Col.
subst B'.

assert(Col A' B C).
ColR.
assert(A' = C').
apply H27.
Col.
contradiction.

intro.
assert(B' = C').
apply H27.
Col.
subst B'.

assert(Col C' A C).
ColR.
assert(C' = A').
apply H25.
ColR.
subst C'.
tauto.

exists B'.
split; Col.


assert(TS B B' A' C).
eapply l9_8_2.
apply H28.
assumption.
assert(TS B B' C' A').
eapply l9_8_2.
apply l9_2.
apply H29.
assumption.
unfold TS in H30.
分离合取式.
ex_and H32 BB.

assert(BB= B').
apply (l6_21_两线交点的唯一性 B B' A' C'); Col.
apply (proj3_col A C B A' C' B' P Q); auto.
subst BB.
Between.

induction(两点重合的决定性 C C').
subst C'.

apply 中间性的对称性.
eapply (proj_preserves_bet1 C B A _ _ P Q); try assumption.
Between.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H14 H1 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H14 H1 H2).
destruct HH.

assert(HH:= proj_one_side B A B' A' P Q H14 H1 H0).
induction HH.
assert(B' = A').
apply H17.
Col.
subst B'.
apply AAB中间性.

assert(HH:= proj_one_side B C B' C' P Q H14 H1 H2).
induction HH.

assert(B' = C').
apply H19.
Col.
subst B'.
apply ABB中间性.

assert(HH:=proj_diff_not_col_inv B A B' A' P Q H14 H1 H0).
destruct HH.

assert(HH:=proj_diff_not_col_inv B C B' C' P Q H14 H1 H2).
destruct HH.

assert(TS B B' A C).
unfold TS.
repeat split.

intro.
assert(B' = A').
apply H23.
Col.
subst B'.

assert(Col A' B C).
ColR.
assert(A' = C').
apply H25.
Col.
contradiction.

intro.
assert(B' = C').
apply H25.
Col.
subst B'.

assert(Col C' A C).
ColR.
assert(C' = A').
apply H23.
ColR.
subst C'.
tauto.

exists B.
split; Col.


assert(TS B B' A' C).
eapply l9_8_2.
apply H26.
assumption.
assert(TS B B' C' A').
eapply l9_8_2.
apply l9_2.
apply H27.
assumption.
unfold TS in H28.
分离合取式.
ex_and H30 BB.

assert(BB= B').
apply (l6_21_两线交点的唯一性 B B' A' C'); Col.
apply (proj3_col A C B A' C' B' P Q); auto.
subst BB.
Between.
Qed.

Lemma one_side_eq_o : forall A B C D, A <> B -> OS A B C D -> eq_o A B C A B D.
Proof.
intros.
assert(HH:= H0).
unfold OS in HH.
ex_and HH P.
unfold TS in H2.
assert(~ Col D A B).
分离合取式.
assumption.
分离合取式.
unfold TS in H1.
assert(~ Col C A B).
分离合取式.
assumption.
分离合取式.
clear H7 H8 H4 H5.
unfold eq_o.
repeat split.
intro.
apply H6.
Col.
intro.
apply H3.
Col.
intros.
apply M是AA中点则M与A重合 in H11.
subst M.
assert(HH:=H13).
unfold 中点 in HH.
分离合取式.

assert(Col A C0 C1).
eapply perp2__col.
apply 垂直的对称性.
apply 垂直的交换性.
apply H4.
apply 垂直的对称性.
Perp.

assert(C1 <> A).
apply 垂直推出不重合2 in H7.
assumption.

assert(C0 <> A).
apply 垂直推出不重合2 in H4.
assumption.

left.
induction H16.
eapply 中间性的交换传递性1.
apply 中间性的对称性.
apply H16.
assumption.
induction H16.
eapply 中间性的外传递性1.
apply H16.
assumption.
assumption.


assert(~Col C1 A B).
eapply L形垂直推出不共线 in H7.
intro.
apply H7.
Col.

assert(~Col C0 A B).
eapply L形垂直推出不共线 in H4.
intro.
apply H4.
Col.

assert(TS A B C1 C0).
unfold TS.
repeat split; auto.

exists A.
split; Col.

assert(proj B A C1 A).
unfold proj.
split.
auto.
left.
repeat split.
intro.
apply H19.
Col.
apply 垂直的交换性.
Perp.
Col.

assert(proj C A C1 C0).
eapply proj_col_proj.
apply H5.
auto.
apply 中间性蕴含共线1 in H16.
Col.

assert( HH:=proj_one_side B C A C0 A C1).
assert(Col C B A \/ OS B A C C0).
apply HH;
auto.
induction H24.
apply False_ind.
apply H6.
Col.

assert( HH1:=proj_one_side B D A C1 A C1).
assert(Col D B A \/ OS B A D C1).
apply HH1;
auto.
induction H25.
apply False_ind.
apply H3.
Col.
clear HH HH1.
assert(OS A B C0 C1).
eapply one_side_transitivity.
apply one_side_symmetry.
apply invert_one_side.
apply H24.
eapply one_side_transitivity.
apply H0.
apply invert_one_side.
assumption.
apply l9_9 in H21.
apply one_side_symmetry in H26.
contradiction.
Qed.


Lemma out_preserves_eq_o : forall A B B' P, ~Col A B  P -> Out A B B' -> eq_o A B P A B' P.
Proof.
intros.
assert(A <> B /\ A <> B').

unfold Out in H0.
分离合取式.
split; auto.
分离合取式.
unfold eq_o.
repeat split.
assumption.
apply out_col in H0.
intro.
apply H.
ColR.
intros.
apply M是AA中点则M与A重合 in H9.
subst M.

assert(A <> C).
apply 垂直推出不重合2 in H3.
auto.
assert(A <> C1).
apply 垂直推出不重合2 in H5.
auto.

assert(Perp A B C1 A).
eapply 垂线共线点也构成垂直1.
assumption.
apply H5.
apply out_col in H0.
Col.

assert(Col A C C1).
eapply perp2__col.
apply 垂直的对称性.
apply 垂直的交换性.
apply H3.
apply 垂直的交换性.
Perp.

assert(proj B A C1 A).
unfold proj.
split; auto.
left.
repeat split.
intro.
apply L形垂直推出不共线 in H14.
apply H14.
Col.
apply 垂直的交换性.
Perp.
Col.

assert(proj P A C C1).
eapply proj_col_proj.
apply H6.
assumption.
Col.
assert(C= C1).
eapply proj_uniqueness.
apply H4.
assumption.
subst C1.
clear H17 H6 H14.

left.
apply midpoint_bet.
assumption.
Qed.

Lemma 等长的同一性_inv : forall A B C, A <> B -> ~Cong A B C C.
Proof.
intros.
intro.
apply H.
eapply 等长的同一性.
apply H0.
Qed.

Lemma 中点蕴含共线 : forall A B A' B' M, A <> B -> 中点 M A A' -> 中点 M B B' -> Col A B B' -> A' <> B' /\ Col A A' B' /\ Col B A' B'.
Proof.
intros.
assert(A' <> B').
intro.
apply H.
assert(Cong A' B' A B).
eapply l7_13_同中点组两侧等长.
apply H0.
assumption.
apply 等长的对称性 in H4.
subst B'.
apply 等长的同一性 in H4.
assumption.

assert(HH0:= H0).
assert(HH1:= H1).
unfold 中点 in HH0.
unfold 中点 in HH1.
分离合取式.

assert(Col M A A').
apply 中间性蕴含共线1 in H6.
Col.
assert(Col M B B').
apply 中间性蕴含共线1 in H4.
Col.

induction(两点重合的决定性 B B').
subst B'.
apply M是AA中点则M与A重合 in H1.
subst M.
Col5.

assert(Col A A' B').

assert(Col B M A).
eapply 共线的传递性2.
apply H10.
Col.
Col.

assert(Col A M B').

eapply 共线的传递性2.
apply H.
Col.
Col.

induction(两点重合的决定性 A M).
subst M.
apply 等长的对称性 in H7.
apply 等长的同一性 in H7.
subst A'.
Col.

eapply 共线的传递性2.
apply H13.
Col.
Col.
repeat split;
Col.

induction(两点重合的决定性 A B').
subst B'.
assert(A'=B).
eapply 中点组的唯一性2; [|apply H1].
apply M是AB中点则M是BA中点.
assumption.
subst A'.
Col.
ColR.
Qed.

Lemma midpoint_par : forall A B A' B' M, A <> B -> 中点 M A A' -> 中点 M B B' -> Par A B A' B'.
Proof.
intros.

assert(A' <> B').
intro.
apply H.
assert(Cong A' B' A B).
eapply l7_13_同中点组两侧等长.
apply H0.
assumption.
apply 等长的对称性 in H3.
subst B'.
apply 等长的同一性 in H3.
assumption.

induction(共线的决定性 A B B').
assert(A' <> B' /\ Col A A' B' /\ Col B A' B').
eapply (中点蕴含共线 _ _ _ _ M); auto.

unfold Par.
right.
split; auto.

assert(HH0:= H0).
assert(HH1:= H1).
unfold 中点 in HH0.
unfold 中点 in HH1.
分离合取式.

assert(Col M A A').
apply 中间性蕴含共线1 in H6.
Col.
assert(Col M B B').
apply 中间性蕴含共线1 in H4.
Col.

unfold Par.
left.
unfold 严格平行.
repeat split; auto; try apply all_coplanar.
intro.
ex_and H10 X.

prolong X M X' M X.
assert(Col A' B' X').
eapply mid_preserves_col.
apply 等价共线BCA.
apply H10.
apply H0.
apply H1.
unfold 中点.
split.
assumption.
apply 等长的左交换性.
Cong.

assert(Col B' X X').
eapply (共线的传递性2 _ A').
auto.
Col.
Col.
induction(两点重合的决定性 X X').
subst X'.
apply 中间性的同一律 in H12.
subst X.

apply H3.
induction(两点重合的决定性 B M).
subst M.
apply 等长的对称性 in H5.
apply 等长的同一性 in H5.
subst B'.
Col.
apply 等价共线CAB.
apply (共线的传递性2 _ M); Col.

assert(Col X M B').
apply 中间性蕴含共线1 in H12.
apply (共线的传递性2 _ X'); Col.

assert(Col X' M B').
apply 中间性蕴含共线1 in H12.
apply (共线的传递性2 _ X); Col.

assert(Col M B X).
apply 共线的传递性2 with B'.
intro.
subst B'.
apply 等长的同一性 in H5.
subst B.
apply H3.
Col.
Col.
Col.

assert(Col X M A).
apply 共线的传递性2 with B.
intro.
subst X.
assert(Cong M X' M B').
eapply 等长的传递性.
apply H13.
Cong.
assert (HH:=共线点间距相同要么重合要么中点 M X' B' H18 H20).
induction HH.
subst X'.
apply H3.
apply 等价共线CAB.
apply (共线的传递性2 _ M).
intro.
subst M.
apply 等长的同一性 in H13.
contradiction.
Col.
Col.

assert(Col M B A').
ColR.
induction(两点重合的决定性 M A').
subst A'.
apply 等长的同一性 in H7.
subst A.
Col.
ColR.
assert(X'= B).
eapply 中点组的唯一性2.
apply H21.
assumption.
subst X'.
tauto.
Col.
Col.
apply H3.
apply (共线的传递性4 X M).
intro.
subst X.
apply 等长的同一性 in H13.
subst X'.
tauto.
Col.
Col.
Col.
Qed.

Lemma midpoint_par_strict : forall A B A' B' M, ~ Col A B B' -> 中点 M A A' -> 中点 M B B' -> 严格平行 A B A' B'.
Proof.
intros.
assert (A <> B).
apply 不共线则不重合 in H; 分离合取式; assumption.
assert(Par A B A' B').
eapply (midpoint_par A B A' B' M); assumption.
induction H3.
assumption.
分离合取式.
apply False_ind.

assert(HH:=中点蕴含共线 B' A' B A M).
assert(B <> A /\ Col B' B A /\ Col A' B A).
apply HH.
auto.
apply M是AB中点则M是BA中点.
assumption.
apply M是AB中点则M是BA中点.
assumption.
Col.
分离合取式.
apply H.
Col.
Qed.

Lemma 长度小于等于的左交换性 : forall A B C D, Le A B C D -> Le B A C D.
Proof.
intros.
unfold Le in *.
ex_and H P.
exists P.
split.
assumption.
Cong.
Qed.

Lemma 长度小于等于的右交换性 : forall A B C D, Le A B C D -> Le A B D C.
Proof.
intros.
induction(两点重合的决定性 D C).
subst D.
apply AB小于等于CC推出A与B重合 in H.
subst B.
eapply AA小于等于CD.

induction(两点重合的决定性 A B).
subst B.
apply AA小于等于CD.

assert(HH:=由一点往一方向构造等长线段_3 D C A B H0 H1).
ex_and HH P'.
unfold Out in H2.
分离合取式.
induction H5.

assert(Le D C A B).
eapply l5_5_2.
exists P'.
split; auto.
apply 长度小于等于的左交换性 in H6.
assert(Cong A B C D).
apply 长度小于等于的反对称性.
auto.
auto.
unfold Le.
exists C.
split.
apply ABB中间性.
Cong.
unfold Le.
exists P'.
split.
assumption.
Cong.
Qed.

Lemma 长度小于等于的交换性 : forall A B C D, Le A B C D -> Le B A D C.
Proof.
intros.
apply 长度小于等于的左交换性.
apply 长度小于等于的右交换性.
assumption.
Qed.

Lemma le_cong_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le A B A' B' -> Cong B C B' C' -> Le A C A' C'.
Proof.
intros.
eapply l5_5_2.
unfold Le in H1.
ex_and H1 P.
prolong A C T P B'.
exists T.
split.
assumption.

assert(Bet A B T).
eapply 中间性的交换传递性2.
apply H.
assumption.

apply 两组连续三点分段等则全体等 with B P.
apply H6.
eapply 中间性的交换传递性2.
apply H1.
assumption.
assumption.
apply 等长的左交换性.
eapply 两组连续三点分段等则全体等 with C B'.
apply 中间性的对称性.
eapply 中间性的交换传递性1.
apply H.
assumption.
eapply 中间性的交换传递性1.
apply H1.
assumption.
Cong.
Cong.
Qed.


Lemma cong_le_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le B C B' C' -> Cong A B A' B' -> Le A C A' C'.
Proof.
intros.
apply 长度小于等于的交换性.
eapply le_cong_le.
apply 中间性的对称性.
apply H.
apply 中间性的对称性.
apply H0.
apply 长度小于等于的交换性.
assumption.
Cong.
Qed.


Lemma bet_le_le : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le A B A' B' -> Le B C B' C' -> Le A C A' C'.
Proof.
intros.
assert(HH1:=H1).
assert(HH2:=H2).
unfold Le in HH1.
unfold Le in HH2.
ex_and HH1 X.
ex_and HH2 Y.
assert(Le A C A' Y).
eapply le_cong_le with B B'.
apply H.
(* assumption. *)

eapply 中间性的内传递性1.
apply H0.
assumption.
assumption.
assumption.

induction (两点重合的决定性 B' Y).
subst Y.

assert(Le A' B' A' C').
unfold Le.
exists B'.
split.
assumption.
apply 等长的自反性.
eapply 长度小于等于的传递性.
apply H7.
assumption.

assert(Bet A' Y C').
eapply 中间性的外传递性1 with B'.

eapply 中间性的内传递性1.
apply H0.
assumption.
assumption.
auto.
eapply 长度小于等于的传递性.
apply H7.
unfold Le.
exists Y.
split.
assumption.
apply 等长的自反性.
Qed.


Lemma bet_double_bet : forall A B C B' C', 中点 B' A B -> 中点 C' A C -> Bet A B' C' -> Bet A B C.
Proof.
intros.
unfold 中点 in *.
分离合取式.
assert(Le A B' A C').
unfold Le.
exists B'.
split.
assumption.
apply 等长的自反性.
assert (Le B' B C' C).
eapply l5_6_等长保持小于等于关系.
apply H4.
assumption.
assumption.
assert(Le A B A C).
eapply bet_le_le.
apply H.
apply H0.
assumption.
assumption.

induction (两点重合的决定性 A B').
subst B'.
apply 等长的对称性 in H3.
apply 等长的同一性 in H3.
subst B.
apply AAB中间性.

assert( A <> C').
intro.
subst C'.
apply AB小于等于CC推出A与B重合 in H4.
contradiction.

assert(A <> B).
intro.
subst B.
apply 中间性的同一律 in H.
contradiction.
assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H0.
contradiction.

assert(Out A B C).

assert(Bet A B C' \/ Bet A C' B).
eapply l5_1.
apply H7.
assumption.
assumption.
induction H11.

eapply l6_7.
apply bet_out.
auto.
apply H11.
apply bet_out.
auto.
assumption.

assert(Bet A B C \/ Bet A C B).
apply l5_1 with C'.
auto.
assumption.
assumption.
induction H12.
apply bet_out.
auto.
assumption.
apply l6_6.
apply bet_out.
auto.
assumption.
eapply l6_13_1.
assumption.
assumption.
Qed.


Lemma bet_half_bet : forall A B C B' C', Bet A B C  -> 中点 B' A B -> 中点 C' A C -> Bet A B' C'.
Proof.
intros.
assert(HH0:= H0).
assert(HH1:= H1).
unfold 中点 in H0.
unfold 中点 in H1.
分离合取式.

induction(两点重合的决定性 A B).
subst B.
apply 中间性的同一律 in H0.
subst B'.
apply AAB中间性.
assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H1.
subst C'.
apply 中间性的同一律 in H.
contradiction.
assert(A <> B').
intro.
subst B'.
apply 等长的对称性 in H3.
apply 等长的同一性 in H3.
contradiction.
assert(A <> C').
intro.
subst C'.
apply 等长的对称性 in H2.
apply 等长的同一性 in H2.
contradiction.

assert(Col A B' C').
apply 中间性蕴含共线1 in H0.
apply 中间性蕴含共线1 in H1.
apply 中间性蕴含共线1 in H.
ColR.
induction H8.
assumption.
induction H8.
apply 中间性的对称性 in H8.

assert(Bet A C B).
eapply bet_double_bet.
apply HH1.
apply HH0.
assumption.

assert(B = C).
eapply 双中间性推出点重合.
apply 中间性的对称性.
apply H9.
Between.
subst C.
assert(B' = C').
eapply 中点的唯一性1.
apply HH0.
assumption.
subst C'.
apply ABB中间性.

(***********************************)

assert(Bet A B' C).
eapply 中间性的交换传递性2.
apply H0.
assumption.

assert(Out A B' C').
unfold Out.
repeat split; auto.
eapply l5_3.
apply H9.
assumption.
eapply l6_4_1 in H10.
分离合取式.
apply 中间性的对称性 in H8.
contradiction.
Qed.

Lemma midpoint_preserves_bet : forall A B C B' C', 中点 B' A B -> 中点 C' A C -> (Bet A B C <-> Bet A B' C').
Proof.
intros.
split.
intro.
eapply bet_half_bet.
apply H1.
assumption.
assumption.
intro.
eapply bet_double_bet.
apply H.
apply H0.
assumption.
Qed.

Lemma symmetry_preseves_bet1 : forall A B M A' B', 中点 M A A' -> 中点 M B B' -> Bet M A B -> Bet M A' B'.
Proof.
intros.

eapply l7_15; eauto with midpoint.
Qed.

Lemma symmetry_preseves_bet2 : forall A B M A' B', 中点 M A A' -> 中点 M B B' -> Bet M A' B' -> Bet M A B.
Proof.
intros.
eapply l7_15.
apply A是AA中点.
apply M是AB中点则M是BA中点.
apply H.
apply M是AB中点则M是BA中点.
apply H0.
assumption.
Qed.

Lemma symmetry_preserves_bet : forall A B M A' B', 中点 M A A' -> 中点 M B B' -> (Bet M A' B' <-> Bet M A B).
Proof.
intros.
split.
apply symmetry_preseves_bet2;
assumption.
intro.
eapply (symmetry_preseves_bet1 A B);
assumption.
Qed.

Lemma par_cong_mid : forall A B A' B', Par A B A' B' -> Cong A B A' B' -> exists M,  中点 M A A' /\ 中点 M B B' \/ 中点 M A B' /\ 中点 M B A'.
Proof.
intros.
induction H.

(*******Cas general**********)


assert(HH:= cop__one_or_two_sides A A' B B').
assert(HH0:= H).
unfold 严格平行 in HH0.
分离合取式.
assert(TS A A' B B' \/ OS A A' B B').
apply HH.
Cop.
intro.
apply H2.
exists A'.
split;Col.
intro.
apply H2.
exists A.
split; Col.

induction H3.
clear HH.
assert(HH:= H3).
unfold TS in HH.
assert(~ Col B A A').
分离合取式.
assumption.
分离合取式.
ex_and H7 M.
exists M.
left.

assert(B <> B').
intro.
subst B'.
apply 中间性的同一律 in H8.
subst M.
apply H2.
exists B.
split; Col.

induction (两点重合的决定性 B M).
subst M.
contradiction.

induction (两点重合的决定性 B' M).
subst M.
apply False_ind.
apply H6.
Col.

assert(A <> A').
intro.
subst A'.
apply False_ind.
apply H6.
Col.

assert(A <> M).
intro.
subst M.
apply H2.
exists B'.
split.
apply 中间性蕴含共线1 in H8.
Col.
Col.

assert(A' <> M).
intro.
subst M.
apply H2.
exists B.
apply 中间性蕴含共线1 in H8.
split.
Col.
Col.

(****************)

assert(HH:=(中点的存在性 A A')).
ex_and HH X.

prolong B X B'' B X.
assert(中点 X B B'').
unfold 中点.
split.
assumption.
Cong.

(*

assert(~ Col B A A').
intro.
apply H8.

apply 中间性蕴含共线1 in H10.
assert(Col B' A M).
eapply (共线的传递性2 _ B).
auto.
Col.
Col.
ColR.
*)

assert(严格平行 B A B'' A').
apply (midpoint_par_strict B A B'' A' X); auto.

assert(Col B'' B' A' /\ Col A' B' A').
apply(parallel_uniqueness B A B' A' B'' A' A').

apply par_comm.
unfold Par.
left.
assumption.
Col.
unfold Par.
left.
assumption.
Col.
分离合取式.

assert(Cong A B A' B'').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H15.
apply M是AB中点则M是BA中点.
assumption.
assert(Cong A' B' A' B'').
eapply 等长的传递性.
apply 等长的对称性.
apply H0.
assumption.

assert(B' = B'' \/ 中点 A' B' B'').
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.
induction H24.

(***************)

subst B''.

assert(X = M).
eapply (l6_21_两线交点的唯一性 A A' B B'); Col.
subst X.
split; auto.

assert(TS A A' B B'').
unfold TS.
repeat split; auto.
intro.
apply H6.
apply 等价共线BCA.
eapply (共线的传递性2 _ B'').
intro.
subst B''.
apply M是AB中点则M是BA中点 in H24.
apply A是AB中点则A与B重合 in H24.
apply par_strict_distinct in H; 分离合取式; auto.
Col.
Col.
exists X.
split.

unfold 中点 in H15.
分离合取式.
apply 中间性蕴含共线1 in H15.
Col.
assumption.

assert(OS A A' B' B'').
eapply l9_8_1.
apply l9_2.
apply H3.
apply l9_2.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H6.
Col.
intro.
apply H6.

apply 等价共线BCA.
eapply (共线的传递性2 _ B'').
intro.
subst B''.
apply M是AB中点则M是BA中点 in H24.
apply A是AB中点则A与B重合 in H24.
apply par_strict_distinct in H; 分离合取式; auto.
Col.
Col.

exists A'.
split.
Col.
unfold 中点 in H24.
分离合取式.
assumption.
apply l9_9 in H27.
contradiction.

clear HH H1.


(****************)

assert(HH:=(中点的存在性 A' B)).
ex_and HH X.
exists X.
right.

prolong A X B'' A X.
assert(中点 X A B'').
unfold 中点.
split.
assumption.
Cong.

assert(~Col A B A').
intro.
apply H2.
exists A'.
split; Col.

(*


assert(HH:= H5).
unfold OS in HH.
ex_and HH T.


assert(~Col A A' B).
unfold TS in H9.
分离合取式.
intro.
apply H11.
Col.

assert(~Col A A' B').
unfold TS in H10.
分离合取式.
intro.
apply H12.
Col.


assert(~Col B A B').
intro.
apply H4.
exists B'.
split;
Col.
*)

assert(严格平行  A B B'' A').
apply (midpoint_par_strict A B  B'' A' X).
assumption.
assumption.
apply M是AB中点则M是BA中点.
assumption.

assert(Col B'' B' A' /\ Col A' B' A').
apply (parallel_uniqueness B A B' A' B'' A' A').

(*
assert (Col A' A' B' /\ Col B'' A' B').
Col.
*)
apply par_comm.
unfold Par.
left.
assumption.
Col.
apply par_left_comm.
unfold Par.
left.
assumption.
Col.
分离合取式.

assert(Cong A B  B'' A').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H6.
assumption.
assert(Cong A' B' A' B'').
eapply 等长的传递性.
apply 等长的对称性.
apply H0.
Cong.
assert(B' = B'' \/ 中点 A' B' B'').
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.

induction H13.
subst B''.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.

assert(OS A A' X B'').

eapply (out_one_side_1 _ _ X B'').
intro.
apply H7.
apply 等价共线BCA.
eapply (共线的传递性2 _ X).
intro.
subst X.
apply A是AB中点则A与B重合 in H1.
subst A'.
apply H2.
exists B.
split; Col.
Col.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
Col.
Col.
unfold Out.
repeat split.
intro.
subst X.
apply 等长的同一性 in H5.
subst B''.
unfold 严格平行 in H8.
分离合取式.
apply H8.
exists A.
split; Col.
intro.
subst B''.
unfold 严格平行 in H8.
分离合取式.
apply H14.
exists A.
split; Col.
unfold 中点 in H6.
分离合取式.
left.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H2.
exists A.
split; Col.

unfold OS in H14.
ex_and H14 T.
unfold TS in H15.
分离合取式.
assumption.
exists A'.
split.
Col.
unfold 中点 in H13.
分离合取式.
assumption.

assert(TS A A' X B').
eapply l9_8_2.
apply l9_2.
apply H15.
apply one_side_symmetry.
assumption.

assert(OS A A' X B).

eapply (out_one_side_1).
intro.
apply H7.
apply 等价共线BCA.
eapply (共线的传递性2 _ X).
intro.
subst X.
apply A是AB中点则A与B重合 in H1.
subst A'.
apply H2.
exists B.
split; Col.
Col.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
Col.
apply ABB型共线;assumption.
unfold Out.
repeat split.
intro.
subst X.
unfold TS in H16.
分离合取式.
apply H16.
Col.
intro.
subst A'.
unfold 严格平行 in H8.
分离合取式.
apply H17.
exists B.
split; Col.
unfold 中点 in H1.
分离合取式.
left.
assumption.

assert(OS A A' X B').
eapply one_side_transitivity.
apply H17.
assumption.
apply l9_9 in H16.
contradiction.

分离合取式.

induction (两点重合的决定性 A A').
subst A'.
assert(B = B' \/ 中点 A B B').
eapply 共线点间距相同要么重合要么中点; auto.
induction H4.
subst B'.
assert( HH:= 中点的存在性 A B).
ex_and HH M.
exists M.
right.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.
exists A.
left.
split.
apply A是AA中点.
assumption.

induction (两点重合的决定性 B B').
subst B'.
assert(A = A' \/ 中点 B A A').
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.
induction H5.
subst A'.
assert( HH:= 中点的存在性 A B).
ex_and HH M.
exists M.
right.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.
exists B.
left.
split.
assumption.
apply A是AA中点.

induction (两点重合的决定性 A B').
subst B'.
assert(B = A' \/ 中点 A B A').
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.
induction H6.
subst A'.
assert( HH:= 中点的存在性 A B).
ex_and HH M.
exists M.
left.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.
exists A.
right.
split.
apply A是AA中点.
assumption.

induction (两点重合的决定性 A' B).
subst A'.
assert(A = B' \/ 中点 B A B').
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.
induction H7.
subst B'.
assert( HH:= 中点的存在性 A B).
ex_and HH M.
exists M.
left.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.
exists B.
right.
split.
assumption.
apply A是AA中点.

assert(Col A B A').
ColR.
assert(Col A B B').
ColR.

induction H9.
induction H3.

assert( HH:= 中点的存在性 A' B).
ex_and HH M.
exists M.
right.
split.

assert(Bet B M B').

apply 中间性的交换传递性2 with A'.
Between.
assumption.

assert(Bet A M B').
eapply 中间性的内传递性2.
apply H9.
assumption.
assert(Cong A M B' M).
eapply (两组连续三点分段等则全体等 A  B _  _ A').
eapply 中间性的内传递性1.
apply H9.
assumption.
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H3.
unfold 中点 in H10.
分离合取式.
assumption.
Cong.
unfold 中点 in H10.
分离合取式.
apply 等长的左交换性.
Cong.
unfold 中点.
split.
assumption.
Cong.
apply M是AB中点则M是BA中点.
assumption.

induction H3.

assert( HH:= 中点的存在性 B B').
ex_and HH M.
exists M.
left.
split.

assert(Bet A' M B).
eapply 中间性的内传递性2.
apply H3.
unfold 中点 in H10.
分离合取式.
Between.
assert(Bet M B A).
eapply 中间性的交换传递性1.
unfold 中点 in H10.
分离合取式.
apply 中间性的对称性.
apply H10.
Between.
assert(Bet A' M A).
eapply 中间性的外传递性2.
apply H11.
assumption.
intro.
subst M.
apply A是AB中点则A与B重合 in H10.
contradiction.
assert(Cong A M A' M).
eapply 两组连续三点分段等则全体等.
apply 中间性的对称性.
apply H12.
eapply 中间性的内传递性1.
apply H3.

unfold 中点 in H10.
分离合取式.
Between.
assumption.
unfold 中点 in H10.
分离合取式.
Cong.
unfold 中点.
split.
Between.
Cong.
assumption.

assert(Bet B A' A).
eapply (bet_cong_bet B').
auto.
Between.
Between.
Cong.

assert( HH:= 中点的存在性 A' B).
ex_and HH M.
exists M.
right.
split.
assert(Bet B M A).
eapply 中间性的交换传递性2.
unfold 中点 in H11.
分离合取式.
apply 中间性的对称性.
apply H11.
assumption.

assert(Bet B' B M).
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H9.
assumption.

assert(Bet M A' A).
apply (中间性的交换传递性1 B).
Between.
assumption.
assert(Bet B' M A').
eapply 中间性的外传递性1.
apply H13.
unfold 中点 in H11.
分离合取式.
Between.
intro.
subst M.
apply M是AB中点则M是BA中点 in H11.
apply A是AB中点则A与B重合 in H11.
auto.
assert(Bet B' M A).
eapply 中间性的外传递性2.
apply H15.
assumption.
intro.
subst A'.
apply A是AB中点则A与B重合 in H11.
subst M.
tauto.

assert(Cong A M B' M).
eapply l4_3.
apply 中间性的对称性.
apply H12.
apply H15.
Cong.
unfold 中点 in H11.
分离合取式.
Cong.
unfold 中点.
split.
Between.
Cong.
中点.

induction H9.
induction H2.


assert(B' = B /\ A = A').
eapply bet_cong_eq.
assumption.
Between.
Cong.
分离合取式.
contradiction.
induction H2.

assert(Bet B' B A').
eapply bet_cong_bet.
apply H6.
Between.
Between.
Cong.

assert( HH:= 中点的存在性 B B').
ex_and HH M.
exists M.
left.
split.

assert(Bet A' M B').
eapply 中间性的内传递性2.
apply 中间性的对称性.
apply H10.
unfold 中点 in H11.
分离合取式.
assumption.

assert(Bet M B' A).
eapply 中间性的交换传递性1.
unfold 中点 in H11.
分离合取式.
apply H11.
assumption.
assert(Bet A' M A).
eapply 中间性的外传递性2.
apply H12.
assumption.
intro.
subst M.
apply M是AB中点则M是BA中点 in H11.
apply A是AB中点则A与B重合 in H11.
apply sym_equal in H11.
contradiction.

assert(Bet A M B).
eapply 中间性的外传递性1.
apply 中间性的对称性.
apply H13.
unfold 中点 in H11.
分离合取式.
Between.
intro.
subst M.
apply M是AB中点则M是BA中点 in H11.
apply A是AB中点则A与B重合 in H11.
apply sym_equal in H11.
contradiction.

assert(Cong A' M A M).
eapply l4_3.
apply H12.
apply H15.
Cong.
unfold 中点 in H11.
分离合取式.
Cong.
unfold 中点.
split.
Between.
Cong.
assumption.

assert( HH:= 中点的存在性 A B').
ex_and HH M.
exists M.
right.
split.
assumption.

assert(Bet A' A M).
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H2.
unfold 中点 in H10.
分离合取式.
assumption.

assert(Bet A M B).
eapply 中间性的交换传递性2.
unfold 中点 in H10.
分离合取式.
apply H10.
Between.

assert(Bet A' M B).
eapply 中间性的外传递性1.
apply H11.
assumption.
intro.
subst M.
apply A是AB中点则A与B重合 in H10.
contradiction.

assert(Cong B M A' M).
eapply l4_3.
apply 中间性的对称性.
apply H12.
eapply 中间性的内传递性2.
apply 中间性的对称性.
apply H2.
unfold 中点 in H10.
分离合取式.

assumption.
Cong.
unfold 中点 in H10.
分离合取式.
Cong.
unfold 中点.
split.
Between.
Cong.

induction H8.

assert(Bet B' B A').
eapply 中间性的外传递性1.
apply H9.
assumption.
assumption.

assert(B = A' /\ B' = A).
eapply bet_cong_eq.
assumption.
assumption.
Cong.
分离合取式.
subst A'.
tauto.

induction H8.

assert( HH:= 中点的存在性 A A').
ex_and HH M.
exists M.
left.
split.
assumption.

assert(Bet B A' M).
eapply 中间性的内传递性1.
apply H8.
unfold 中点 in H10.
分离合取式.
Between.

assert(Bet B M A).
eapply 中间性的外传递性1.
apply H11.
unfold 中点 in H10.
分离合取式.
Between.
intro.
subst M.
apply M是AB中点则M是BA中点 in H10.
apply A是AB中点则A与B重合 in H10.
subst A'.
tauto.

assert(Bet B M B').
eapply 中间性的交换传递性2.
apply H12.
Between.

assert(Cong B M B' M).
eapply l4_3.
apply H12.

assert(Bet B' A A').
eapply 中间性的内传递性1.
apply H9.
Between.
eapply 中间性的内传递性2.
apply H14.
unfold 中点 in H10.
分离合取式.
Between.
Cong.
unfold 中点 in H10.
分离合取式.
Cong.
unfold 中点.
split.
assumption.
Cong.

assert(Bet A B' A' \/ Bet A A' B').
eapply (l5_2 B).
auto.
Between.
Between.
induction H10.

assert( HH:= 中点的存在性 A B').
ex_and HH M.
exists M.
right.
split.
assumption.

assert(Bet B M B').
eapply 中间性的内传递性2.
apply 中间性的对称性.
apply H9.
unfold 中点 in H11.
分离合取式.
Between.
assert(Bet A' B' M).
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H10.
unfold 中点 in H11.
分离合取式.
Between.

assert(Bet A' M B).
eapply 中间性的外传递性1.
apply H13.
Between.
intro.
subst M.
apply M是AB中点则M是BA中点 in H11.
apply A是AB中点则A与B重合 in H11.
subst B'.
tauto.

assert(Cong M A' M B).
eapply 两组连续三点分段等则全体等.
apply 中间性的对称性.
apply H13.
eapply 中间性的交换传递性1.
unfold 中点 in H11.
分离合取式.
apply 中间性的对称性.
apply H11.
assumption.
unfold 中点 in H11.
分离合取式.
Between.
Cong.
Cong.
unfold 中点.
split.
Between.
Cong.

assert( HH:= 中点的存在性 A A').
ex_and HH M.
exists M.
left.
split.
assumption.

assert(Bet B A M).
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H8.
unfold 中点 in H11.
分离合取式.
Between.
assert(Bet B' M A).
eapply 中间性的内传递性2.
apply 中间性的对称性.
apply H10.
unfold 中点 in H11.
分离合取式.
Between.
assert(Bet B' M B).
eapply 中间性的外传递性2.
apply H13.
Between.
intro.
subst M.
apply A是AB中点则A与B重合 in H11.
contradiction.
assert(Cong B' M B M).
eapply 两组连续三点分段等则全体等.
eapply 中间性的内传递性1.
apply 中间性的对称性.
apply H10.
unfold 中点 in H11.
分离合取式.
Between.
apply H12.
Cong.
unfold 中点 in H11.
分离合取式.
Between.
Cong.
unfold 中点.
split.
Between.
Cong.
Qed.

Lemma per_preserves_bet_aux1 : forall P Q A B C B' C', P <> Q -> Bet A B C ->
                                      Col P Q A ->
                                      Per B B' P -> Col P Q B' ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A -> P <> B' -> P <> C' ->
                                      Bet A B' C'.
Proof.
intros.

induction(两点重合的决定性 B B').
subst B'.

assert(Col A B C').
apply (共线的传递性4 P Q); try auto.

assert(Col P A B).
eapply (共线的传递性2 _ Q); try auto.

assert(Col Q A B).
eapply (共线的传递性2 _ P).
auto.
Col.
Col.

induction(两点重合的决定性 A B).
subst B.
apply AAB中间性.

assert(Col P Q C).
eapply 共线的传递性4.
apply H12.
Col.
Col.
apply 中间性蕴含共线1.
assumption.

assert(Col P C' C).
eapply 共线的传递性2.
apply H.
assumption.
assumption.

assert(P=C' \/ C=C').
eapply l8_9_直角三点共线则必有两点重合.
apply 直角的对称性.
assumption.
assumption.

induction H15.
subst C'.
tauto.
subst C'.
assumption.

(* A=A' et B<>B' *)

induction(两点重合的决定性 A C).
subst C.
apply 中间性的同一律 in H0.
subst B.
assert(B'=C').
apply per_id with A P; auto.
apply (共线的传递性2 _ Q); auto.
subst C'.
apply ABB中间性.

assert(C <> C').
intro.
subst C'.

assert(Col P A C).
eapply (共线的传递性2 _ Q); try auto.

assert(Col A C B').
eapply 共线的传递性4.
apply H.
assumption.
assumption.
assumption.

assert(Col P B' B).
apply (共线的传递性4 A C); Col.
assert(B=B' \/ P=B').
eapply l8_9_直角三点共线则必有两点重合.
assumption.
Col.
induction H14.
subst B'.
tauto.
auto.

induction (两点重合的决定性 A B').
subst B'.
apply AAB中间性.

assert(A <> B).
intro.
subst B.
apply 成直角三点不共线 in H2.
apply H2.
ColR.
assumption.
auto.

induction(共线的决定性 C B B').
assert(C=B).

eapply (l6_21_两线交点的唯一性 B B').
assert(Per B B' A).
eapply (直角边共线点也构成直角2 _ _ P).
auto.
assumption.
ColR.
apply 成直角三点不共线 in H15.
apply H15.
auto.
auto.
apply H13.
Col.
Col.
apply 中间性蕴含共线1.
apply H0.
Col.
subst C.

assert(B'=C').
apply per_id with B P; ColR.
subst C'.
apply ABB中间性.


assert(Perp B' B' B' P \/ Perp B B' B' P).
eapply 垂直于转T形垂直.

apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H15.
apply 垂直推出不重合1 in H15.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply 垂直于转T形垂直.

apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H16.
apply 垂直推出不重合1 in H16.
tauto.

assert(Par B B' C C').
eapply l12_9_2D.
apply H15.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H16.
eapply (共线的传递性2 _ Q);
auto.
unfold Par in H17.

assert(严格平行 B B' C C').
induction H17.
assumption.
分离合取式.
apply False_ind.
apply H14.
ColR.
clear H17.


assert(OS B B' C C').
eapply l12_6.
assumption.

assert(Per B B' A).
eapply (直角边共线点也构成直角2 _ _ P); try auto.
ColR.

induction(两点重合的决定性 A C').
subst C'.

assert(TS B B' A C).
unfold TS.
repeat split; try auto.
apply 成直角三点不共线 in H19.
intro.
apply H19.
Col.
auto.
auto.
exists B.
split.
Col.
assumption.
apply l9_2 in H20.
apply l9_9 in H20.
contradiction.


assert(TS B B' A C).
unfold TS.
repeat split; try auto.
apply 成直角三点不共线 in H19.
intro.
apply H19.
Col.
auto.
auto.
exists B.
split.
Col.
assumption.

assert(TS B B' C' A).

eapply l9_8_2.
apply l9_2.
apply H21.
assumption.


unfold TS in H22.
分离合取式.
ex_and H24 T.


assert(T = B').
apply (l6_21_两线交点的唯一性 B B' A C'); ColR.
subst T.
Between.
Qed.

Lemma perp_not_eq_3 : forall A B C, Perp A B B C -> A <> C.
Proof.
intros.
apply 垂直的交换性 in H.
apply L形垂直转垂直于 in H.
assert(Per A B C).
apply L形垂直于转直角.
Perp.
unfold 垂直于 in H.
分离合取式.
intro.
subst C.
apply ABA直角则A与B重合 in H0.
contradiction.
Qed.


Lemma per_preserves_bet_aux2 : forall P Q A B C A' C', P <> Q -> Bet A B C ->
                                      Per A A' P -> Col P Q A' ->
                                      Col P Q B ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A'-> P <> B -> P <> C' ->
                                      Bet A' B C'.
Proof.
intros.

induction (两点重合的决定性 A A').
subst A'.

assert(Col A B C').
apply (共线的传递性4 P Q); try auto.

assert(Col P A B).
eapply (共线的传递性2 _ Q); try auto.

assert(Col Q A B).
eapply (共线的传递性2 _ P).
auto.
Col.
Col.

induction(两点重合的决定性 A B).
subst B.
apply AAB中间性.

assert(Col P Q C).
eapply 共线的传递性4.
apply H12.
Col.
Col.
apply 中间性蕴含共线1.
assumption.

assert(Col P C' C).
eapply 共线的传递性2.
apply H.
assumption.
assumption.

assert(P=C' \/ C=C').
eapply l8_9_直角三点共线则必有两点重合.
apply 直角的对称性.
assumption.
assumption.

induction H15.
subst C'.
tauto.
subst C'.
assumption.


induction(两点重合的决定性 A C).
subst C.
apply 中间性的同一律 in H0.
subst B.
apply False_ind.
apply H9.

apply l8_9_直角三点共线则必有两点重合 in H1.
induction H1.
assumption.
subst A'.
tauto.
ColR.


assert(~Col P Q A).
intro.
assert (Col A A' P).
ColR.
apply l8_9_直角三点共线则必有两点重合 in H1.
induction H1;tauto.
assumption.

assert(A <> B).
intro.
subst B.
contradiction.

induction (两点重合的决定性 C C').
subst C'.
assert(Col A' B C).
eapply (共线的传递性4 P Q ); assumption.
assert(Col C A' P).
ColR.

assert(B=C).
eapply l6_21_两线交点的唯一性.
apply H11.
apply H12.
Col.
Col.
Col.
Col.
subst C.
apply ABB中间性.

induction(两点重合的决定性 A' C').
subst C'.

assert(Per  A A' B).
apply 直角边共线点也构成直角2 with P; ColR.
assert(Per C A' B).
apply 直角边共线点也构成直角2 with P; ColR.

eapply l8_6 in H14.
subst B.
apply ABB中间性.
apply H15.
Between.

assert(HH:=ex_四点成首末边等长双直角S形则对边等长 P Q B A P Q).
assert(exists T, Per T B P /\ Cong T B P Q /\ OS P Q T A).
apply HH; auto.
ex_and H15 T.
clear HH.

assert(Perp B B B P \/ Perp T B B P).
eapply 垂直于转T形垂直.

apply 直角转L形垂直于.
intro.
subst T.
apply 等长的对称性 in H16.
apply 等长的同一性 in H16.
contradiction.
auto.
auto.
induction H18.
apply 垂直推出不重合1 in H18.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply 垂直于转T形垂直.

apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H19.
apply 垂直推出不重合1 in H19.
tauto.

assert(Par T B C C').
eapply l12_9_2D.
apply H18.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H19.
eapply (共线的传递性2 _ Q);
auto.

assert(Perp A' A' A' P \/ Perp A A' A' P).
eapply 垂直于转T形垂直.

apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H21.
apply 垂直推出不重合1 in H21.
tauto.

assert(Par T B A A').
eapply l12_9_2D.
apply H18.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H21.
eapply (共线的传递性2 _ Q);
auto.

assert(严格平行 T B C C').
induction H20.
assumption.
分离合取式.
apply False_ind.

apply H14.
apply per_id with A P; auto.
apply 直角的对称性.
eapply 直角边共线点也构成直角2 with C.
auto.
apply 直角的对称性.
apply H4.
auto.

apply 等价共线CAB.
apply 共线的传递性2 with B.

assert(~Col P Q C).
intro.
assert (Col C C' P).
ColR.
apply l8_9_直角三点共线则必有两点重合 in H4.
induction H1;tauto.
assumption.

intro.
subst C.
contradiction.
Col.
Col.
ColR.


assert(严格平行 T B A A').
induction H22.
assumption.
分离合取式.
apply False_ind.

apply H14.
eapply sym_equal.
apply per_id with C P; auto.
apply 直角的对称性.
apply 直角边共线点也构成直角2 with A.
auto.
apply 直角的对称性.
apply H1.

apply 等价共线CAB.
apply 共线的传递性2 with B; Col.
ColR.

assert(OS T B C C').
apply l12_6.
assumption.
assert(OS T B A A').
apply l12_6.
assumption.

assert(TS T B A C).
unfold TS.
repeat split.
intro.
unfold 严格平行 in H24.
分离合取式.
apply H28.
exists A.
split.
assumption.
Col.
intro.
unfold 严格平行 in H23.
分离合取式.
apply H28.
exists C.
split.
assumption.
Col.
exists B.
split.
Col.
assumption.

assert(TS T B C' A).
eapply l9_8_2.
apply l9_2.
apply H27.
assumption.

assert(TS T B A' C').
eapply l9_8_2.
apply l9_2.
apply H28.
assumption.
unfold TS in H29.
分离合取式.
ex_and H31 BB.

assert(B=BB).
eapply (l6_21_两线交点的唯一性 T B A' C'); Col.
ColR.
subst BB.
assumption.
Qed.

Lemma per_diff : forall A B A' B' P, A <> B -> ~ Col A B A' ->
                             Per A A' P -> Per B B' P ->
                             A' <> P -> B' <> P -> A' <> B'.
Proof.
intros.
intro.
subst B'.
apply H0.
eapply per2__col.
apply H1.
assumption.
assumption.
Qed.



Lemma per_preserves_bet : forall P Q A B C A' B' C', P <> Q -> Bet A B C ->
                                      Per A A' P -> Col P Q A' ->
                                      Per B B' P -> Col P Q B' ->
                                      Per C C' P -> Col P Q C' ->
                                      P <> A'-> P <> B' -> P <> C' ->
                                      Bet A' B' C'.
Proof.
intros.

induction(两点重合的决定性 A A').
subst A'.
eapply (per_preserves_bet_aux1 P Q A B C B' C'); assumption.

induction(两点重合的决定性 B B').
subst B'.
eapply (per_preserves_bet_aux2 P Q A B C A' C'); assumption.

induction(两点重合的决定性 C C').
subst C'.
assert(HH:=(per_preserves_bet_aux1 P Q C B A B' A')).
apply 中间性的对称性.
apply HH; try assumption.
Between.

induction (两点重合的决定性 A B).
subst B.
assert(A'=B').
eapply (per_id A _ _ P); try auto.
ColR.
subst B'.
apply AAB中间性.

induction (两点重合的决定性 C B).
subst B.
assert(C'=B').
eapply (per_id C _ _ P); try auto.
ColR.
subst B'.
apply ABB中间性.

assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H0.
contradiction.

assert(Perp B' B' B' P \/ Perp B B' B' P).
eapply 垂直于转T形垂直.
apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H16.
apply 垂直推出不重合1 in H16.
tauto.

assert(Perp C' C' C' P \/ Perp C C' C' P).
eapply 垂直于转T形垂直.
apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H17.
apply 垂直推出不重合1 in H17.
tauto.

assert(Perp A' A' A' P \/ Perp A A' A' P).
eapply 垂直于转T形垂直.
apply 直角转L形垂直于.
auto.
auto.
assumption.
induction H18.
apply 垂直推出不重合1 in H18.
tauto.

assert(Par B B' C C').
eapply l12_9_2D.
apply H16.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H17.
eapply (共线的传递性2 _ Q);
auto.

assert(Par B B' A A').
eapply l12_9_2D.
apply H16.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H18.
eapply (共线的传递性2 _ Q);
auto.

(**************************************************************************************************)

assert(Col A B C).
apply 中间性蕴含共线1.
assumption.

induction(两点重合的决定性 A' C').
subst C'.

assert(Col A C A').
eapply per2__col.
apply H1.
auto.
assumption.

assert(Col A B A').
eapply (共线的传递性2 _ C); try auto.
Col.

assert(Per B A' P).
apply 直角的对称性.
eapply (直角边共线点也构成直角2 _ _ A).
auto.
apply 直角的对称性.
assumption.
Col.


assert(A' = B').
eapply (per_id B _ _ P); try auto.
intro.
subst A'.
apply par_right_comm in H20.
apply par_id in H20.

assert(Per P B B').
eapply (直角边共线点也构成直角2 _ _ A).
auto.
apply 直角的对称性.
assumption.
Col.
apply H11.
eapply ABC和ACB均直角则B与C重合.
apply H25.
apply 直角的对称性.
assumption.
ColR.
subst B'.
apply ABB中间性.

(************************************* General case *********************************)

assert(Par A A' C C').
eapply par_trans.
apply par_symmetry.
apply H20.
assumption.

assert(A' <> B').
intro.
subst B'.
apply H22.
assert(Col A B A').
eapply per2__col.
apply H1.
auto.
assumption.
assert(Col C A A').
ColR.
assert(Per P A' C).
eapply (直角边共线点也构成直角2 _ _ A).
auto.
apply 直角的对称性.
assumption.
Col.
apply 直角的对称性 in H26.
apply per_id with C P; auto.
intro.
subst C.
apply 垂直的交换性 in H17.
apply L形垂直推出不共线 in H17.
apply H17.
ColR.
ColR.

assert(C' <> B').
intro.
subst B'.
apply H22.
assert(Col B C C').
eapply per2__col.
apply H3.
auto.
assumption.
assert(Col A C C').
ColR.
assert(Per P C' A).
eapply (直角边共线点也构成直角2 _ _ C).
auto.
apply 直角的对称性.
assumption.
Col.
apply 直角的对称性 in H27.
apply per_id with A P; auto.
ColR.

assert(严格平行 B B' C C').
induction H19.
assumption.
分离合取式.

apply False_ind.

apply H25.

apply per_id with B P; auto.
intro.
subst B.
apply 垂直的交换性 in H16.
apply L形垂直推出不共线 in H16.
apply H16.
ColR.
apply 直角的对称性.
apply (直角边共线点也构成直角2 _ _ C).
auto.
apply 直角的对称性.
assumption.
Col.
ColR.

assert(严格平行 B B' A A').
induction H20.
assumption.
分离合取式.

apply False_ind.

apply H24.

apply per_id with B P; auto.
intro.
subst B.
apply 垂直的交换性 in H16.
apply L形垂直推出不共线 in H16.
apply H16.
ColR.
apply 直角的对称性.
eapply (直角边共线点也构成直角2 _ _ A).
auto.
apply 直角的对称性.
assumption.
Col.
ColR.

assert(OS B B' A A').
apply l12_6.
assumption.
assert(OS B B' C C').
apply l12_6.
assumption.
assert(TS B B' A C).
unfold TS.
repeat split; auto.
intro.
apply H24.
apply per_id with A P; auto.

apply 直角的对称性.
apply 直角边共线点也构成直角2 with B.
auto.
apply 直角的对称性.
apply H3.
Col.
ColR.
intro.
apply H25.
apply per_id with C P; auto.
apply 直角的对称性.
apply 直角边共线点也构成直角2 with B.
auto.
apply 直角的对称性.
apply H3.
Col.
ColR.
exists B.
split.
Col.
assumption.

assert(TS B B' A' C).
eapply l9_8_2.
apply H30.
assumption.
assert(TS B B' A' C').
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H31.
assumption.
unfold TS in H32.
分离合取式.
ex_and H34 BB.

assert(BB = B').
apply (l6_21_两线交点的唯一性 B B' C' A'); ColR.
subst BB.
assumption.
Qed.

Lemma out_preserves_eqo1 : forall A B P B', ~Col A B P -> Out A B B' -> eqo A B P A B' P.
Proof.
intros.
unfold eqo.
repeat split.
assumption.
assert(HH:=H0).
unfold Out in H0.
分离合取式.
apply out_col in HH.
intro.
apply H.
ColR.

intros.

assert(B=B2).
apply (l6_11_uniqueness A A B2 B').
assumption.
assumption.
apply l6_6.
assumption.
apply 等长的自反性.
subst B2.
apply M是AA中点则M与A重合 in H7.
subst M.

assert(Perp A B C1 A).
eapply 垂线共线点也构成垂直1.
intro.
subst B.
apply H.
Col.
apply H3.
apply out_col in H5.
assumption.

assert(A <> C).
apply 垂直推出不重合2 in H1.
auto.

assert(A <> C1).
apply 垂直推出不重合2 in H3.
auto.

assert(Col A C C1).
eapply perp2__col.
apply 垂直的对称性.
apply 垂直的右交换性.
apply H1.
apply 垂直的对称性.
Perp.

induction (两点重合的决定性 P C).
subst P.

apply l8_9_直角三点共线则必有两点重合 in H4.
induction H4.
subst C1.
unfold 中点 in H9.
分离合取式.
left.
assumption.
subst C1.
apply 垂直推出不重合2 in H3.
tauto.
Col.

assert(P <> C1).
intro.
subst P.
apply H14.
apply l8_9_直角三点共线则必有两点重合 in H2.
induction H2.
assumption.
subst C.
tauto.
Col.

assert(C1=C).
apply per_id with P A; Col.
subst C1.
unfold 中点 in H9.
分离合取式.
left.
assumption.
Qed.


Lemma out_preserves_eqo : forall A B P B' P', ~Col A B P -> Out A B B' -> Out A P P' -> eqo A B P A B' P'.
Proof.
intros.

induction (两点重合的决定性 P P').
subst P'.
apply out_preserves_eqo1.
assumption.
assumption.

unfold eqo.
repeat split.
assumption.
intro.
apply H.
assert(Col A B B').
apply out_col.
assumption.
assert(Col A P P').
apply out_col.
assumption.

assert(Col A P B').
apply (共线的传递性2 _ P').
intro.
subst P'.
unfold Out in H1.
分离合取式.
auto.
Col.
Col.
eapply (共线的传递性2 _ B').
intro.
subst B'.
unfold Out in H0.
分离合取式.
auto.
Col.
Col.

intros.

assert(B = B2).
apply (l6_11_uniqueness A A B2 B').
assumption.
assumption.
apply l6_6.
assumption.
apply 等长的自反性.
subst B2.

apply M是AA中点则M与A重合 in H9.
subst M.

assert(A <> C).
apply 垂直推出不重合2 in H3.
auto.
assert(A <> C1).
apply 垂直推出不重合2 in H5.
auto.

assert(Perp A B C1 A).
eapply 垂线共线点也构成垂直1.
intro.
subst B.
apply H.
Col.
apply H5.
apply out_col.
apply l6_6.
assumption.

assert(Col A C C1).

eapply perp2__col.
apply 垂直的对称性.
apply 垂直的交换性.
apply H3.
apply 垂直的交换性.
Perp.

induction(两点重合的决定性 P C).
subst P.
assert(P'=C1).

apply l8_9_直角三点共线则必有两点重合 in H6.
induction H6.
assumption.
contradiction.
assert(HH:= H1).
unfold Out in H1.
分离合取式.
apply out_col in HH.
ColR.
subst P'.

left.

unfold Out in H1.
分离合取式.
induction H17.
eapply 中间性的交换传递性1.
apply 中间性的对称性.
apply H17.
apply midpoint_bet.
assumption.
eapply 中间性的外传递性1.
apply 中间性的对称性.
apply H17.
apply midpoint_bet.
assumption.
assumption.

assert(~Col P C A).
apply 成直角三点不共线.
assumption.
auto.
assumption.

assert(C <> C1).
intro.
subst C1.
assert(Col P P' C).
eapply per2__col.
apply H4.
auto.
assumption.

apply H2.
apply (l6_21_两线交点的唯一性 A P C P); Col.

assert(HH:=每组共线三点都有另一共线点 A C C1 H15).
ex_and HH D.

left.
unfold Out in H1.
分离合取式.

induction H24.
assert(Bet A C C1).
apply (per_preserves_bet D A A P P' A C C1); Col.
apply 直角的对称性.
apply 角ABB成直角.
apply 直角边共线点也构成直角2 with A; Col.
apply 直角边共线点也构成直角2 with A; ColR.
ColR.
eapply 中间性的交换传递性1.
apply 中间性的对称性.
apply H25.
apply midpoint_bet.
assumption.

assert(Bet A C1 C).
apply (per_preserves_bet D A A P' P A C1 C); Col.
apply 直角的对称性.
apply 角ABB成直角.
apply 直角边共线点也构成直角2 with A; ColR.
ColR.
apply 直角边共线点也构成直角2 with A; ColR.
apply 中间性的对称性.
apply 中间性的外传递性2 with C1; Between.
Qed.


Lemma per_one_side : forall A B P Q C C', A <> P -> C' <> P -> ~Col A B C -> Col P Q A -> Col P Q C' -> Perp A B P Q -> Per C C' P -> OS A B C C'.
Proof.
intros.
assert(A <> B).
apply 垂直推出不重合1 in H4.
assumption.

assert(P <> Q).
apply 垂直推出不重合2 in H4.
assumption.

induction (两点重合的决定性 C C').
subst C'.
apply one_side_reflexivity.
intro.
apply H1.
Col.

assert(Perp C C' C' P).
eapply 直角转L形垂直于 in H5.
eapply 垂直于转T形垂直 in H5.
induction H5.
apply 垂直推出不重合1 in H5.
tauto.
assumption.
auto.
auto.

assert(Perp C C' P Q).
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
assumption.
apply 垂直的对称性.
apply 垂直的右交换性.
apply H9.
Col.
assert(Par C C' A B).
eapply l12_9_2D.
apply H10.
assumption.

assert(严格平行 C C' A B).
induction H11.
assumption.
分离合取式.
apply False_ind.
apply H1.
Col.
eapply l12_6.
apply par_strict_symmetry.
assumption.
Qed.


Lemma one_side_eqo : forall A B X Y, OS A B X Y -> eqo A B X A B Y.
Proof.
intros.
unfold eqo.
repeat split.
eapply one_side_not_col123.
apply H.
apply one_side_symmetry in H.
eapply one_side_not_col123.
apply H.

intros.
apply M是AA中点则M与A重合 in H6.
subst M.

induction(两点重合的决定性 C C1).
subst C1.
left.
apply midpoint_bet.
assumption.

assert(A <> C).
apply 垂直推出不重合2 in H0.
auto.

assert(A <> C1).
apply 垂直推出不重合2 in H2.
auto.

assert(A <> C /\ A <> C1 /\ C <> C1).
repeat split; auto.

assert(Col A C C1).
eapply perp2__col.
apply 垂直的交换性.
apply 垂直的对称性.
apply H0.
apply 垂直的交换性.
Perp.

assert(HH:=每组共线三点都有另一共线点 A C C1 H13).
ex_and HH D.

assert(Perp A B D C).
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的对称性.
apply H0.
Col.

assert(~Col A B X).
unfold OS in H.
ex_and H T.
unfold TS in H.
分离合取式.
intro.
apply H.
Col.

assert(~Col A B Y).
unfold OS in H.
ex_and H T.
unfold TS in H22.
分离合取式.
intro.
apply H22.
Col.

assert(OS A B X C).
eapply (per_one_side A B D); auto.
apply  等价共线CBA.
apply H17.
Col.
assumption.
eapply 直角边共线点也构成直角2; [|apply H1|].
auto.
Col.

assert(OS A B Y C1).
eapply (per_one_side A B D); auto.
apply 等价共线CBA.
apply H17.
apply 等价共线CAB.
eapply (共线的传递性2 _ A);Col.
assumption.
eapply 直角边共线点也构成直角2; [|apply H3|].
auto.
apply 等价共线CAB.
eapply (共线的传递性2 _ C);
Col.

assert(OS A B C C1).
eapply one_side_transitivity.
apply one_side_symmetry.
apply H23.
eapply one_side_transitivity.
apply H.
assumption.

assert(A <> B).
apply 垂直推出不重合1 in H0.
assumption.

assert(~ Col C1 A B).
unfold OS in H24.
ex_and H24 T.
unfold TS in H27.
分离合取式.
assumption.

assert(TS A B C1 C').
unfold TS.
repeat split; auto.

intro.
unfold 中点 in H8.
分离合取式.

assert(C'=A).
eapply (l6_21_两线交点的唯一性 A B C1 A); Col.
subst C'.
apply 等长的同一性 in H29.
subst C1.
tauto.
exists A.
unfold 中点 in H8.
分离合取式.
split; auto.
Col.

assert(TS A B C C').
eapply l9_8_2.
apply H28.
apply one_side_symmetry.
assumption.

assert(Col A C C').
eapply (共线的传递性2 _ C1).
assumption.
Col.
unfold 中点 in H8.
分离合取式.
apply 中间性蕴含共线1 in H8.
Col.

unfold TS in H29.
分离合取式.
ex_and H32 AA.
assert(AA=A).
apply (l6_21_两线交点的唯一性 A B C' C); Col.
intro.
subst C'.
apply 中间性的同一律 in H33.
subst AA.
apply H31.
assumption.

subst AA.
left.
assumption.
Qed.

End Orientation.