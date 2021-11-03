Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.

Section Varignon.

Context `{TE:塔斯基公理系统_欧几里得几何}.

(** This is the usual proof presented in classroom based on
the midpoint theorem but this proof suffers from two problems.
It needs the fact that IJK are not collinear, 
which is not always the case when the quadrilateral is not convex.
It also needs the fact that A is different from C, and B is different from D.
The original proof by Varignon suffer from the same problem.
The original proof can be found page 138, Corollary IV:
http://polib.univ-lille3.fr/documents/B590092101_000000011.489_IMT.pdf
*)

Lemma varignon :
 forall A B C D I J K L,
  A<>C -> B<>D -> ~ Col I J K ->
  中点 I A B ->
  中点 J B C ->
  中点 K C D ->
  中点 L A D ->
  平行四边形 I J K L.
Proof.
intros.
assert_diffs.
assert (Par I L B D) (** Applying the midpoint theorem in the triangle BDA. *)
  by perm_apply (triangle_mid_par B D A L I).
assert (Par J K B D) (** Applying the midpoint theorem in the triangle BDC. *)
  by perm_apply (triangle_mid_par B D C K J).
assert (Par I L J K) (** Transitivity of parallelism *)
  by (apply par_trans with B D;finish).
assert (Par I J A C) (** Applying the midpoint theorem in the triangle ACB. *)
  by perm_apply (triangle_mid_par A C B J I). 
assert (Par L K A C) (** Applying the midpoint theorem in the triangle ACD. *)
  by perm_apply (triangle_mid_par A C D K L).
assert (Par I J K L) (** Transitivity of parallelism *)
  by (apply par_trans with A C;finish).
apply par_2_plg;finish. (** If in the opposite side of quadrilatral are parallel and two opposite side are distinct
                            then it is a parallelogram. *)
Qed.

(** We propose here a more complex proof to simplify the ndg. 
If we know that a quadrilateral has its pairs of opposite side congruent and parallel
 then it is a parallelogram. *)


Lemma varignon_aux_aux :
 forall A B C D I J K L,
  A<>C ->
  J<>L -> 
  中点 I A B ->
  中点 J B C ->
  中点 K C D ->
  中点 L A D ->
  平行四边形 I J K L.
Proof.
intros.
induction (两点重合的决定性 B D).
treat_equalities.
apply plg_trivial.
intro;treat_equalities;intuition.
Name X the midpoint of B and D.
assert_diffs.

assert (Par B D L I /\ Cong B X L I)
  by (apply (triangle_mid_par_cong_1 A B D X L I);finish).
assert (Par B D K J /\ Cong B X K J)
  by (apply (triangle_mid_par_cong_1 C B D X K J);finish).
spliter.
assert (Par I L J K)
  by (eapply par_trans with B D;finish).
assert (Cong I L J K)
  by (eapply 等长的传递性 with B X;finish).

Name X' the midpoint of A and C.
assert (Par A C J I /\ Cong A X' J I)
  by (apply (triangle_mid_par_cong_1 B A C X' J  I);finish).
assert (Par A C K L /\ Cong A X' K L)
  by (apply (triangle_mid_par_cong_1 D A C X' K L);finish).
spliter.
assert (Par I J K L)
  by (eapply par_trans with A C;finish).
assert (Cong I J K L)
   by (eapply 等长的传递性 with A X';finish).
apply par_par_cong_cong_parallelogram;finish.
Qed.


Lemma varignon_aux :
 forall A B C D I J K L,
  (A<>C \/ B<>D) ->
  J<>L ->
  中点 I A B ->
  中点 J B C ->
  中点 K C D ->
  中点 L A D ->
  平行四边形 I J K L.
Proof.
intros.
induction H.
eauto using varignon_aux_aux.

induction (两点重合的决定性 A C).
treat_equalities.
apply plg_trivial1.
intro;treat_equalities;intuition.

Name X the midpoint of B and D.
assert_diffs.

assert (Par B D L I /\ Cong B X L I)
  by (apply (triangle_mid_par_cong_1 A B D X L I);finish).
assert (Par B D K J /\ Cong B X K J)
  by (apply (triangle_mid_par_cong_1 C B D X K J);finish).
spliter.
assert (Par I L J K)
  by (eapply par_trans with B D;finish).
assert (Cong I L J K)
  by (eapply 等长的传递性 with B X;finish).

Name X' the midpoint of A and C.
assert (Par A C J I /\ Cong A X' J I)
  by (apply (triangle_mid_par_cong_1 B A C X' J  I);finish).
assert (Par A C K L /\ Cong A X' K L)
  by (apply (triangle_mid_par_cong_1 D A C X' K L);finish).
spliter.
assert (Par I J K L)
  by (eapply par_trans with A C;finish).
assert (Cong I J K L)
   by (eapply 等长的传递性 with A X';finish).
apply par_par_cong_cong_parallelogram;finish.
Qed.

Lemma varignon' :
 forall A B C D I J K L,
  (A<>C \/ B<>D) ->
  中点 I A B ->
  中点 J B C ->
  中点 K C D ->
  中点 L A D ->
  平行四边形 I J K L.
Proof.
intros.
induction (两点重合的决定性 J L).
subst.
unfold 平行四边形.
right.
unfold 退化平行四边形.
assert_congs_perm.
Name X the midpoint of B and D.
induction (两点重合的决定性 A B).
 treat_equalities.
 assert_cols.
 repeat split;Cong;Col; intuition.
induction (两点重合的决定性 A D).
 treat_equalities.
 induction (两点重合的决定性 X K).
  treat_equalities.
  intuition.
 assert_cols.
 assert (Cong X L K L).
 assert (Par B L L K /\
       Par B C K X /\
       Par L C L X /\
       Cong B X K L /\
       Cong L X K L /\
       Cong B L K X /\ Cong C L K X /\ Cong L K L X /\ Cong C K L X).
  apply (triangle_mid_par_flat_cong B L C K L X);Col;中点.
   intro;treat_equalities. intuition.
   intro;treat_equalities. intuition.
   spliter.
   Cong.
 repeat split.
 show_distinct L X . intuition.
 assert_diffs.
 ColR.
 Col.
 auto.
 auto.
 left;auto.
induction (两点重合的决定性 B D).
 treat_equalities. intuition.
assert (中点 L I K).
assert (Par A B L X /\
       Par A D X I /\
       Par B D L I /\
       Cong A I X L /\
       Cong B I X L /\
       Cong A L X I /\ Cong D L X I /\ Cong B X L I /\ Cong D X L I).
apply (triangle_mid_par_cong A B D X L I);auto.
spliter.
induction (两点重合的决定性 C D).
 treat_equalities.
 intuition.
assert_diffs.
induction (两点重合的决定性 B C).
 treat_equalities.
 assert_cols.
 apply cong_col_mid.
  auto.
  ColR.
 Cong.
assert (Par B C X K /\
       Par B D K L /\
       Par C D X L /\
       Cong B L K X /\
       Cong C L K X /\
       Cong B X K L /\ Cong D X K L /\ Cong C K X L /\ Cong D K X L).
apply (triangle_mid_par_cong B C D K X L);auto.
spliter.
induction (两点重合的决定性 I K).
  treat_equalities.
  assert (平行四边形 A D B C) by (apply mid_plg with I;中点).
  assert (平行四边形 A B D C) by (apply mid_plg with L;中点).
  exfalso.
  apply Plg_perm in H35.
  apply Plg_perm in H39.
  spliter.
  apply (plg_not_comm_1 B D A C);auto.

apply cong_col_mid.
 auto.
 assert (Par I L K L).
  apply par_trans with B D;Par.
 apply 等价共线CAB, par_id; Par.
CongR.
repeat split;Col;Cong.
left.
intro.
treat_equalities.
intuition.

apply (varignon_aux A B C D);auto.
Qed.



End Varignon.
