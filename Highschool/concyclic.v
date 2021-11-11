Require Export GeoCoq.Highschool.circumcenter.

Section 共圆.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Definition 共圆 A B C D := 共面 A B C D /\ exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D.

Lemma 共圆定义_辅助 : forall A B C D, 共圆 A B C D ->
  exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D /\ 共面 A B C O.
Proof.
  intros A B C D [HCop [O1]]; 分离合取式.
  destruct (共线的决定性 A B C).
    exists O1; repeat split; Cop.
  destruct (l11_62_existence A B C O1) as [O []].
  exists O.
  repeat split; try apply cong2_per2__cong with O1 O1; finish.
Qed.

Lemma 共圆的传递性 : forall A B C D E,
 ~ Col A B C ->
 共圆 A B C D  -> 共圆 A B C E -> 共圆 A B D E.
Proof.
intros.
split.
unfold 共圆 in *; 分离合取式; CopR.
apply 共圆定义_辅助 in H0.
apply 共圆定义_辅助 in H1.
decompose [ex and] H0;clear H0.
decompose [ex and] H1;clear H1.
exists x.
repeat split;Cong.
assert (x=x0).
统计不重合点.
apply 外心的唯一性 with A B C;try assumption.
repeat split; [CongR..|Cop].
repeat split; [CongR..|Cop].
subst.
Cong.
Qed.

Lemma 等价共圆ABDC: forall A B C D,
  共圆 A B C D -> 共圆 A B D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆ACBD : forall A B C D,
  共圆 A B C D -> 共圆 A C B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆ACDB : forall A B C D,
  共圆 A B C D -> 共圆 A C D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆ADBC : forall A B C D,
  共圆 A B C D -> 共圆 A D B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆ADCB : forall A B C D,
  共圆 A B C D -> 共圆 A D C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BACD : forall A B C D,
  共圆 A B C D -> 共圆 B A C D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BADC : forall A B C D,
  共圆 A B C D -> 共圆 B A D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BCAD : forall A B C D,
  共圆 A B C D -> 共圆 B C A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BCDA : forall A B C D,
  共圆 A B C D -> 共圆 B C D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BDAC : forall A B C D,
  共圆 A B C D -> 共圆 B D A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆BDCA : forall A B C D,
  共圆 A B C D -> 共圆 B D C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CABD : forall A B C D,
  共圆 A B C D -> 共圆 C A B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CADB : forall A B C D,
  共圆 A B C D -> 共圆 C A D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CBAD : forall A B C D,
  共圆 A B C D -> 共圆 C B A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CBDA : forall A B C D,
  共圆 A B C D -> 共圆 C B D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CDAB : forall A B C D,
  共圆 A B C D -> 共圆 C D A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆CDBA : forall A B C D,
  共圆 A B C D -> 共圆 C D B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DABC : forall A B C D,
  共圆 A B C D -> 共圆 D A B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DACB : forall A B C D,
  共圆 A B C D -> 共圆 D A C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DBAC : forall A B C D,
  共圆 A B C D -> 共圆 D B A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DBCA : forall A B C D,
  共圆 A B C D -> 共圆 D B C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DCAB : forall A B C D,
  共圆 A B C D -> 共圆 D C A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma 等价共圆DCBA : forall A B C D,
  共圆 A B C D -> 共圆 D C B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; [Cop|分离合取式; exists X; repeat split; CongR..].
Qed.

Lemma AABC共圆 : forall A B C,
 ~ Col A B C ->
 共圆 A A B C.
Proof.
intros A B C HABC.
unfold 共圆.
split.
apply AABC共面.
destruct (外心的存在性 A B C HABC) as [G HG].
exists G.
apply 外心与三角形顶点距离相等 in HG;分离合取式;repeat split;Cong.
Qed.

End 共圆.
