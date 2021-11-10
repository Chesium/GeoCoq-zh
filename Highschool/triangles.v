Require Export GeoCoq.Tarski_dev.Ch12_parallel.
Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section Triangles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Section ABC.

Variable A B C : Tpoint.

Definition 等腰三角形 A B C :=
 Cong A B B C.

Lemma 等腰三角形的对称性 :
  等腰三角形 A B C ->
  等腰三角形 C B A.
Proof.
unfold 等腰三角形.
intros.
Cong.
Qed.

Lemma 等腰三角形底角相等 :
  A<>C -> A<>B ->
  等腰三角形 A B C ->
  等角 C A B A C B.
Proof.
intros.
apply 三角形全等推角等1.
auto.
auto.
unfold 三角形全等.
unfold 等腰三角形 in H.
repeat split;Cong.
Qed.

Lemma 底角相等的三角形是等腰三角形 :
 ~ Col A B C ->
 等角 C A B A C B ->
 等腰三角形 A B C. 
Proof.
intros.
assert (Cong B A B C)
 by (apply l11_44_1_b;finish;等角).
unfold 等腰三角形.
Cong.
Qed.

(** In a triangle 等腰三角形 in A the altitude wrt. A, is also the bisector and median. *)

Lemma 等腰三角形底边垂线也是底边中线 :
 forall H,
 等腰三角形 A B C ->
 Col H A C -> 
 Perp H B A C ->
 ~ Col A B C /\ A<>H /\ C<>H /\ 中点 H A C /\ 等角 H B A H B C.
Proof.
intros.
统计不重合点.
assert (~ Col A B C).
 {
   intro;apply 垂直推出不共线 in H2.
   destruct H2;apply H2;ColR.
 }
统计不重合点. 
assert (A<>H).
 { (** these point are distinct
      because otherwise the hypothenuse is not larger than the side *)
 intro.
 treat_equalities.
 assert (Lt A B B C /\ Lt A C B C).
 apply (l11_46 B A C);Col; left;apply L形垂直转直角2;auto.
 spliter.
 unfold 等腰三角形 in *.
 apply (等长推出不小于 A B B C);auto.
 }
assert (C<>H).
 {
 intro.
 treat_equalities.
 assert (Lt C B B A /\ Lt C A B A).
 apply (l11_46 B C A);Col; left;apply L形垂直转直角2;finish.
 spliter.
 unfold 等腰三角形 in *.
 apply (等长推出不小于 C B B A);finish.
 } 
assert (垂直于 H A C B H)
 by (apply l8_14_2_1b_bis_交点是垂点;finish).
assert (Per A H B) by (apply 垂直于转直角1 with C H;finish).
assert (Per C H B) by (apply 垂直于转直角3 with A H;finish). 
(* We prove that A H B and C H B are congruent triangles *)
assert (Cong H A H C /\ 等角 H A B H C B /\ 等角 H B A H B C)
 by (apply (cong2_per2__cong_conga2 A H B C H B);finish).
spliter.
assert (中点 H A C)
 by (apply 不重合共线点间距相同则为中点组1;finish).
auto.
Qed.

Definition 等边三角形 A B C :=
 Cong A B B C /\ Cong B C C A.

Definition 严格等边三角形 A B C :=
 等边三角形 A B C /\ A <> B.

Lemma 严格等边三角形蕴含等边三角形 :
 严格等边三角形 A B C ->
 等边三角形 A B C.
Proof.
unfold 严格等边三角形 in *. tauto.
Qed.

Lemma 等边三角形三边等长:
  等边三角形 A B C ->
  Cong A B B C /\ Cong B C C A /\ Cong C A A B.
Proof.
unfold 等边三角形;intros;intuition Cong.
assert (T:=等长的传递性 A B B C C A H0 H1).
Cong.
Qed.

Lemma 等价等边三角形BCA :
 等边三角形 A B C ->
 等边三角形 B C A.
Proof.
intro.
apply 等边三角形三边等长 in H.
unfold 等边三角形.
intuition Cong.
Qed.

Lemma 等价等边三角形BAC :
 等边三角形 A B C ->
 等边三角形 B A C.
Proof.
intro.
apply 等边三角形三边等长 in H.
unfold 等边三角形.
intuition Cong.
Qed.

Lemma 等价等边三角形CBA :
 等边三角形 A B C ->
 等边三角形 C B A.
Proof.
intro.
apply 等边三角形三边等长 in H.
unfold 等边三角形.
intuition Cong.
Qed.

Lemma 等价等边三角形ACB :
 等边三角形 A B C ->
 等边三角形 A C B.
Proof.
intro.
apply 等边三角形三边等长 in H.
unfold 等边三角形.
intuition Cong.
Qed.

Lemma 等价等边三角形CAB :
 等边三角形 A B C ->
 等边三角形 C A B.
Proof.
intro.
apply 等边三角形三边等长 in H.
unfold 等边三角形.
intuition Cong.
Qed.

Hint Resolve 等价等边三角形BAC 等价等边三角形ACB
 等价等边三角形CAB 等价等边三角形BCA 等价等边三角形CBA : 等边三角形.

Lemma 等边转ABC等腰 :
  等边三角形 A B C ->
  等腰三角形 A B C.
Proof.
unfold 等边三角形, 等腰三角形.
tauto.
Qed.

Lemma 等边转BCA等腰 :
  等边三角形 A B C ->
  等腰三角形 B C A.
Proof.
unfold 等边三角形, 等腰三角形.
tauto.
Qed.

Lemma 等边转CAB等腰 :
  等边三角形 A B C ->
  等腰三角形 C A B.
Proof.
intros.
apply 等边三角形三边等长 in H.
unfold 等腰三角形.
tauto.
Qed.

Hint Resolve 等边转ABC等腰 等边转BCA等腰 等边转CAB等腰 : 等边三角形.

Lemma 严格等边三角形三顶点不重合 :
 严格等边三角形 A B C ->
 A <> B /\ B <> C /\ A <> C.
Proof.
intros.
unfold 严格等边三角形, 等边三角形 in H.
decompose [and] H;clear H.
repeat split;Cong.
eauto using 与不同点等长之点不同.
eapply 与不同点等长之点不同.
assert (T:=等长的传递性 A B B C C A H2 H3).
apply H1.
assert (T:=等长的传递性 A B B C C A H2 H3).
Cong.
Qed.

Hint Resolve 严格等边三角形三顶点不重合 : 等边三角形.

Lemma 等价严格等边三角形ACB :
 严格等边三角形 A B C ->
 严格等边三角形 A C B.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
unfold 严格等边三角形 in *.
intuition (eauto with 等边三角形).
Qed.

Lemma 等价严格等边三角形BAC :
 严格等边三角形 A B C ->
 严格等边三角形 B A C.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
unfold 严格等边三角形 in *.
intuition (eauto with 等边三角形).
Qed.

Lemma 等价严格等边三角形BCA :
 严格等边三角形 A B C ->
 严格等边三角形 B C A.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
unfold 严格等边三角形 in *.
intuition (eauto with 等边三角形).
Qed.

Lemma 等价严格等边三角形CAB :
 严格等边三角形 A B C ->
 严格等边三角形 C A B.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
unfold 严格等边三角形 in *.
intuition (eauto with 等边三角形).
Qed.

Lemma 等价严格等边三角形CBA :
 严格等边三角形 A B C ->
 严格等边三角形 C B A.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
unfold 严格等边三角形 in *.
intuition (eauto with 等边三角形).
Qed.

Hint Resolve 等价严格等边三角形ACB 等价严格等边三角形BAC
等价严格等边三角形BCA 等价严格等边三角形CAB 等价严格等边三角形CBA : 等边三角形.

Lemma 严格等边三角形三顶点不共线 : 
 严格等边三角形 A B C -> ~ Col A B C.
Proof.
intros.
assert (T:=(严格等边三角形三顶点不重合 H)).
unfold 严格等边三角形 in *.
unfold 等边三角形 in *.
spliter.
intro.
assert (中点 B A C) by (apply (不重合共线点间距相同则为中点组1 B A C);finish).
assert (中点 C A B) by (apply (不重合共线点间距相同则为中点组1 C A B);finish).
apply 严格中点组换排列则否 with C A B;auto.
Qed.

Lemma 严格等边三角形AC等角 :
 严格等边三角形 A B C ->
 等角 C A B A C B.
Proof.
intros.
assert (T:= 严格等边三角形三顶点不重合 H).
apply 严格等边三角形蕴含等边三角形 in H.
apply 等边转ABC等腰 in H.
apply 等腰三角形底角相等.
tauto.
tauto.
assumption.
Qed.

End ABC.

Lemma 严格等边三角形AB等角 :
 forall A B C,
 严格等边三角形 A B C ->
 等角 B A C A B C.
Proof.
intros.
apply 等价严格等边三角形ACB in H.
apply 严格等边三角形AC等角 in H.
assumption.
Qed.

Lemma 严格等边三角形BC等角 :
 forall A B C,
 严格等边三角形 A B C ->
 等角 C B A B C A.
Proof.
intros.
apply 等价严格等边三角形BAC in H.
apply 严格等边三角形AC等角 in H.
assumption.
Qed.

Lemma 三角相等则为等边三角形 :
 forall A B C, 
 ~ Col A B C ->
 等角 B A C A B C ->
 等角 A B C B C A ->
 等边三角形 A B C.
Proof.
intros.
assert (等腰三角形 B C A)
 by (apply 底角相等的三角形是等腰三角形;等角;Col).
assert (等腰三角形 C A B)
 by (apply 底角相等的三角形是等腰三角形;等角;Col).
unfold 等腰三角形 in *.
unfold 等边三角形.
split;eCong.
Qed.



End Triangles.