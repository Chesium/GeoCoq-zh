Require Export GeoCoq.Highschool.circumcenter.

Section 共圆.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Definition 共圆 A B C D := 共面 A B C D /\ exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D.

Lemma concyclic_aux : forall A B C D, 共圆 A B C D ->
  exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D /\ 共面 A B C O.
Proof.
  intros A B C D [HCop [O1]]; spliter.
  destruct (共线的决定性 A B C).
    exists O1; repeat split; Cop.
  destruct (l11_62_existence A B C O1) as [O []].
  exists O.
  repeat split; try apply cong2_per2__cong with O1 O1; finish.
Qed.

Lemma concyclic_trans : forall A B C D E,
 ~ Col A B C ->
 共圆 A B C D  -> 共圆 A B C E -> 共圆 A B D E.
Proof.
intros.
split.
unfold 共圆 in *; spliter; CopR.
apply concyclic_aux in H0.
apply concyclic_aux in H1.
decompose [ex and] H0;clear H0.
decompose [ex and] H1;clear H1.
exists x.
repeat split;Cong.
assert (x=x0).
assert_diffs.
apply is_circumcenter_uniqueness with A B C;try assumption.
repeat split; [CongR..|Cop].
repeat split; [CongR..|Cop].
subst.
Cong.
Qed.

Lemma concyclic_perm_1: forall A B C D,
  共圆 A B C D -> 共圆 A B D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_2 : forall A B C D,
  共圆 A B C D -> 共圆 A C B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_3 : forall A B C D,
  共圆 A B C D -> 共圆 A C D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_4 : forall A B C D,
  共圆 A B C D -> 共圆 A D B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_5 : forall A B C D,
  共圆 A B C D -> 共圆 A D C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_6 : forall A B C D,
  共圆 A B C D -> 共圆 B A C D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_7 : forall A B C D,
  共圆 A B C D -> 共圆 B A D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_8 : forall A B C D,
  共圆 A B C D -> 共圆 B C A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_9 : forall A B C D,
  共圆 A B C D -> 共圆 B C D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_10 : forall A B C D,
  共圆 A B C D -> 共圆 B D A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_11 : forall A B C D,
  共圆 A B C D -> 共圆 B D C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_12 : forall A B C D,
  共圆 A B C D -> 共圆 C A B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_13 : forall A B C D,
  共圆 A B C D -> 共圆 C A D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_14 : forall A B C D,
  共圆 A B C D -> 共圆 C B A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_15 : forall A B C D,
  共圆 A B C D -> 共圆 C B D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_16 : forall A B C D,
  共圆 A B C D -> 共圆 C D A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_17 : forall A B C D,
  共圆 A B C D -> 共圆 C D B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_18 : forall A B C D,
  共圆 A B C D -> 共圆 D A B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_19 : forall A B C D,
  共圆 A B C D -> 共圆 D A C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_20 : forall A B C D,
  共圆 A B C D -> 共圆 D B A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_21 : forall A B C D,
  共圆 A B C D -> 共圆 D B C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_22 : forall A B C D,
  共圆 A B C D -> 共圆 D C A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_perm_23 : forall A B C D,
  共圆 A B C D -> 共圆 D C B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|spliter; exists X; repeat split; CongR..].
Qed.

Lemma concyclic_1123 : forall A B C,
 ~ Col A B C ->
 共圆 A A B C.
Proof.
intros A B C HABC.
unfold 共圆.
split.
apply coplanar_trivial.
destruct (exists_circumcenter A B C HABC) as [G HG].
exists G.
apply circumcenter_cong in HG;spliter;repeat split;Cong.
Qed.

End 共圆.
