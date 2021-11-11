  (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section L13_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Pappus Desargues *)

Lemma per2_col_eq : forall A P P' B, A <> P -> A <> P' -> Per A P B -> Per A P' B -> Col P A P' -> P = P'.
Proof.
intros.
induction(两点重合的决定性 P B).
subst B.
assert( A = P' \/ P = P').
apply(l8_9_直角三点共线则必有两点重合 A P' P H2); Col.
induction H4.
contradiction.
assumption.
induction(两点重合的决定性 P' B).
subst B.
assert(A = P \/ P' = P).
apply(l8_9_直角三点共线则必有两点重合 A P P' H1); Col.
induction H5; auto.
contradiction.

apply 直角转L形垂直于 in H1; auto.
apply 直角转L形垂直于 in H2; auto.

apply 垂直于的交换性 in H1.
apply 垂直于的交换性 in H2.
apply 垂直于转T形垂直 in H1.
apply 垂直于转T形垂直 in H2.
induction H1; induction H2.
apply(l8_18_过一点垂线之垂点的唯一性 P A B P P'); Col.
apply L形垂直推出不共线; auto.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 A P' B P' P); Perp.
Col.
apply 垂直推出不重合 in H2.
tauto.
apply 垂直推出不重合 in H1.
tauto.
apply 垂直推出不重合 in H1.
tauto.
Qed.

Lemma per2_preserves_diff : forall O A B A' B', O <> A' -> O <> B' -> Col O A' B' -> Per O A' A -> Per O B' B -> A' <> B' -> A <> B.

Proof.
intros.
intro.
subst B.
apply H4.
apply(per2_col_eq O A' B' A);Col.
Qed.

Lemma per23_preserves_bet : forall A B C B' C', Bet A B C -> A <> B' -> A <> C' -> Col A B' C' -> Per A B' B -> Per A C' C -> Bet A B' C'.
Proof.
intros.
assert(HC:Col A B C).
apply 中间性蕴含共线1 in H; Col.

induction(两点重合的决定性 B B').
subst B'.

assert(Col A C' C).
ColR.

assert(A = C' \/ C = C').
apply l8_9_直角三点共线则必有两点重合; auto.
induction H6.
contradiction.
subst C'.
assumption.

assert(A <> C).
intro.
subst C.
apply ABA直角则A与B重合 in H4.
contradiction.

assert(C <> C').
intro.
subst C'.

assert(Col A B' B).
ColR.

assert(A = B' \/ B = B').
apply l8_9_直角三点共线则必有两点重合; auto.
induction H8; contradiction.

assert(Perp A B' B' B).
apply 直角转L形垂直于 in H3; auto.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3; Perp.
apply 垂直推出不重合 in H3.
tauto.

assert(Perp A C' C' C).
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4; Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' A B');Perp; Cop.
apply 垂直的对称性.
apply(垂线共线点也构成垂直1 _ C'); Perp.
ColR.

induction(两点重合的决定性 B C).
subst C.
assert(B' = C').
apply(per2_col_eq A B' C' B); Perp.
Col.
subst C'.
Between.

assert(~Col A B' B).
apply 成直角三点不共线 in H3; auto.

assert(~Col A C' C).
apply 成直角三点不共线 in H4; auto.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.

assert(Col B C B').
apply cop_per2__col with A; Perp.
exists C; left; split; Col.
apply H13; ColR.

induction H10.
apply l12_6 in H10.

assert(TS B B' A C).
repeat split;auto.
intro.
assert(A = B' \/ B = B').
apply l8_9_直角三点共线则必有两点重合; Col.
induction H12; tauto.
intro.
apply H13; ColR.
exists B.
split; Col.

assert(TS B B' A C').
apply l9_2.
apply(l9_8_2 B B' C C' A); auto.
apply l9_2.
assumption.
unfold TS in H16.
分离合取式.
ex_and H18 T.
assert(T = B').
apply 中间性蕴含共线1 in H19.
apply (l6_21_两线交点的唯一性 B B' A B'); Col.
ColR.
subst T.
assumption.
分离合取式.
apply False_ind.
apply H12.
ColR.
Qed.

Lemma per23_preserves_bet_inv : forall A B C B' C', Bet A B' C' -> A <> B' -> Col A B C -> Per A B' B -> Per A C' C -> Bet A B C.
Proof.
intros.

induction(两点重合的决定性 B B').
subst B'.
assert(Col A C' C).
apply 中间性蕴含共线1 in H.
ColR.
assert(A = C' \/ C = C').
apply(l8_9_直角三点共线则必有两点重合 A C' C); auto.
induction H5.
subst C'.
apply 中间性的同一律 in H.
contradiction.
subst C'.
assumption.

assert(Perp A B' B' B).
apply 直角转L形垂直于 in H2.
apply 垂直于的交换性 in H2.
apply 垂直于转T形垂直 in H2.
induction H2.
Perp.
apply 垂直推出不重合 in H2.
tauto.
auto.
auto.


assert(Perp A C' C' C).
apply 直角转L形垂直于 in H3.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
Perp.
apply 垂直推出不重合 in H3.
tauto.
intro.
subst C'.
apply 中间性的同一律 in H.
contradiction.
intro.
subst C'.
induction(两点重合的决定性 A C).
subst C.
apply 中间性的同一律 in H.
contradiction.
assert(Col A B' B).
apply 中间性蕴含共线1 in H.
ColR.
assert(A = B' \/ B = B').
apply(l8_9_直角三点共线则必有两点重合 A B' B); auto.
induction H8;contradiction.

assert(Perp A B' C' C).
apply 中间性蕴含共线1 in H.
apply(垂线共线点也构成垂直1 _ C'); Col.

assert( Par B' B C' C).
apply(l12_9 B' B C' C A B'); Cop.
Perp.
Perp.

induction(两点重合的决定性 B C).
subst C.
Between.

induction H8.
assert(B' <> C').
intro.
subst C'.
apply H8.
exists B'.
split; Col.


assert(HH:=l12_6 B' B C' C H8).

assert(TS B' B A C').
repeat split; auto.
intro.
assert(A = B' \/ B = B').
apply(l8_9_直角三点共线则必有两点重合 A B' B); auto.
induction H12;contradiction.
intro.
assert(Col A B' B).
assert_cols.
ColR.
assert(A = B' \/ B = B').
apply(l8_9_直角三点共线则必有两点重合 A B' B); auto.
induction H13;contradiction.
exists B'.
split; Col.

assert(TS B' B C A).
apply(l9_8_2 B' B C' C A); auto.
apply l9_2.
assumption.
unfold TS in H12.
分离合取式.
ex_and H14 T.

assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H15.
subst T.
contradiction.

assert (T = B).
assert_cols.
apply (l6_21_两线交点的唯一性 A C B' B); Col.
intro.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9_直角三点共线则必有两点重合 A B' B); auto.
induction H21;contradiction.
subst T.
Between.


分离合取式.
assert_cols.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9_直角三点共线则必有两点重合 A B' B); auto.
induction H15;contradiction.
Qed.



Lemma per13_preserves_bet : forall A B C A' C', Bet A B C -> B <> A' -> B <> C' -> Col A' B C' -> Per B A' A -> Per B C' C -> Bet A' B C'.
Proof.
intros.
assert(Col A B C).
apply 中间性蕴含共线1 in H.
Col.

induction(两点重合的决定性 A A').
subst A'.
assert(Col B C' C).
ColR.

assert(B = C' \/ C = C').
apply l8_9_直角三点共线则必有两点重合; auto.
induction H7.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col A A' B).
ColR.
assert(B = A' \/ A = A').
apply l8_9_直角三点共线则必有两点重合; Col.
induction H8; tauto.

assert(Perp B A' A' A).
apply 直角转L形垂直于 in H3; auto.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
Perp.
apply 垂直推出不重合 in H3.
tauto.

assert(Perp B C' C' C).
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4.
Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A'); Perp; Cop.
apply 垂直的对称性.
apply(垂线共线点也构成垂直1 _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A A' B).
apply 成直角三点不共线 in H3; auto.
intro.
apply H3.
Col.

assert(~Col C C' B).
apply 成直角三点不共线 in H4; auto.
intro.
apply H4.
Col.

assert(OS A A' B C).
apply out_one_side.
left; auto.
repeat split.
intro.
subst A.
unfold OS in H10.
ex_and H10 X.
unfold TS in H13.
分离合取式.
apply H13.
Col.
intro.
subst C.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
分离合取式.
apply H10.
Col.
left.
assumption.

assert(OS C C' B A).
apply out_one_side.
left; auto.
repeat split.
intro.
subst C.
apply H12.
Col.
intro.
subst C.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
分离合取式.
apply H10.
Col.
left.
Between.

assert(OS A A' B C').
apply(one_side_transitivity _ _ _ C); auto.
assert(OS C C' B A').
apply(one_side_transitivity _ _ _ A); auto.

apply invert_one_side in H15.
apply invert_one_side in H16.
assert(HP:= col_one_side_out A' A B C' H2 H15).
assert(Out C' B A').
apply(col_one_side_out C' C B A'); Col.

unfold Out in *.
分离合取式.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (双中间性推出点重合 _ _ B); Between.
分离合取式.

induction(两点重合的决定性 A C).
subst C.
apply 中间性的同一律 in H.
subst B.
clean_duplicated_hyps.
clean_trivial_hyps.
apply ABA直角则A与B重合 in H4.
contradiction.
assert(Col B C' C).
ColR.
apply 成直角三点不共线 in H4; auto.
contradiction.
Qed.

Lemma per13_preserves_bet_inv : forall A B C A' C', Bet A' B C' -> B <> A' -> B <> C' ->  Col A B C  -> Per B A' A -> Per B C' C -> Bet A B C.
Proof.
intros.
assert(Col A' B C').
apply 中间性蕴含共线1 in H.
Col.

induction(两点重合的决定性 A A').
subst A'.
assert(Col B C' C).
ColR.
assert(HH:=l8_9_直角三点共线则必有两点重合 B C' C H4 H6 ).
induction HH.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col B A' A).
ColR.
assert(HH:=l8_9_直角三点共线则必有两点重合 B A' A H3 H7).
induction HH;
contradiction.

assert(Perp B A' A' A).
apply 直角转L形垂直于 in H3; auto.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
Perp.
apply 垂直推出不重合 in H3.
tauto.

assert(Perp B C' C' C).
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4.
Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A'); Perp; Cop.
apply 垂直的对称性.
apply(垂线共线点也构成垂直1 _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A' A B).
apply 成直角三点不共线 in H3; auto.
intro.
apply H3.
Col.

assert(~Col C' C B).
apply 成直角三点不共线 in H4; auto.
intro.
apply H4.
Col.

assert(OS A' A B C').
apply out_one_side.
left; auto.
repeat split.
intro.
subst A'.
apply H11.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
分离合取式.
apply H10.
Col.
left.
assumption.

assert(OS C' C B A').
apply out_one_side.
left; auto.
repeat split.
intro.
subst C'.
apply H12.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
分离合取式.
apply H10.
Col.
left.
Between.

assert(OS A' A B C).
apply(one_side_transitivity _ _ _ C'); auto.
apply invert_one_side.
apply one_side_symmetry.
assumption.

assert(OS C C' B A).
apply(one_side_transitivity _ _ _ A'); auto.
apply invert_one_side.
assumption.
apply one_side_symmetry.
assumption.

apply invert_one_side in H15.

assert(HP:= col_one_side_out A A' B C H2 H15).

assert(Out C B A).
apply(col_one_side_out C C' B A); Col.

unfold Out in *.
分离合取式.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (双中间性推出点重合 _ _ B); Between.

(****************************)

分离合取式.
assert(Perp A' C' A A').
apply (垂线共线点也构成垂直1 _ B); Perp.
intro.
subst C'.
apply 中间性的同一律 in H.
subst A'.
apply 垂直推出不重合 in H9.
tauto.
apply L形垂直推出不共线 in H14.

apply False_ind.
apply H14.
ColR.
Qed.

Lemma per3_preserves_bet1 : forall O A B C A' B' C', Col O A B -> Bet A B C -> O <> A' -> O <> B' -> O <> C'
                                                    -> Per O A' A -> Per O B' B -> Per O C' C
                                                    -> Col A' B' C' -> Col O A' B' -> Bet A' B' C'.

Proof.
intros O A B C A' B' C'.
intro HC.
intros.

induction(两点重合的决定性 A B).
subst B.
assert(A' = B').
apply(per2_col_eq O A' B' A H0 H1 H3 H4); Col.
subst B'.
Between.

induction (两点重合的决定性 A A').
subst A'.
induction(两点重合的决定性 B B').
subst B'.
assert(Col O C C').
apply 中间性蕴含共线1 in H.
ColR.

assert(C = C').
apply 中间性蕴含共线1 in H.
assert(O = C' \/ C = C').
apply(l8_9_直角三点共线则必有两点重合 O C' C H5); Col.
induction H10.
contradiction.
assumption.
subst C'.
assumption.

induction(两点重合的决定性 A B').
subst B'.
Between.

assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H.
contradiction.

assert( ~ Col O B' B).
apply(成直角三点不共线 O B' B H1); auto.

assert(C <> C').
intro.
subst C'.
clean_trivial_hyps.
apply H12.
apply 中间性蕴含共线1 in H.
ColR.

assert(Perp B B' O A).

apply 直角转L形垂直于 in H4; auto.
apply 垂直于转T形垂直 in H4.
induction H4.
apply 垂直推出不重合 in H4.
tauto.
apply 垂直的对称性.
apply 垂直的右交换性.
apply(垂线共线点也构成垂直1 O B' B' B A); auto.
Col.

assert(Perp C C' O A).

apply 直角转L形垂直于 in H5; auto.
apply 垂直于转T形垂直 in H5.
induction H5.
apply 垂直推出不重合 in H5.
tauto.
apply 垂直的对称性.
apply 垂直的右交换性.
apply(垂线共线点也构成垂直1 O C' C' C A); auto.
apply 中间性蕴含共线1 in H.
ColR.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A); Cop.
induction H16.

assert(HH:=l12_6 B B' C C' H16).

assert(TS B B' A C).
unfold TS.
repeat split; Col.
assert(~Col B' A B).
apply(L形垂直推出不共线).
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 A O B B' B'); Col.
Perp.
intro.
apply H17.
Col.
intro.
apply H16.
exists C.
split; Col.
exists B.
split; Col.
assert(TS B B' C' A).
apply(l9_8_2 B B' C C' A).

apply l9_2.
assumption.
assumption.
unfold TS in H18.
分离合取式.
ex_and H20 T.
assert(B'=T).
apply (l6_21_两线交点的唯一性 B B' A C'); Col.
intro.
subst C'.
apply 中间性的同一律 in H21.
subst T.
contradiction.
subst T.
apply 中间性的对称性.
assumption.
分离合取式.

assert(Per O C' B).
apply(直角边共线点也构成直角2 O C' C B); Col.
assert(B'=C').
apply(per2_col_eq O B' C' B); Col.
ColR.
subst C'.
Between.

(*-------------------------------*)

induction(两点重合的决定性 A' B').
subst B'.
Between.

induction(两点重合的决定性 B C).
subst C.
assert(B' = C').
apply(per2_col_eq O B' C' B); auto.
ColR.
subst C'.
Between.

induction(两点重合的决定性 B B').
subst B'.
induction(两点重合的决定性 A' B).
subst B.
Between.

assert(C <> C').
intro.
subst C'.

assert( ~ Col O A' A).
apply(成直角三点不共线 O A' A ); auto.
apply H13.
apply 中间性蕴含共线1 in H.
ColR.

assert(Perp A A' O A').
apply 直角转L形垂直于 in H3; auto.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
Perp.
apply 垂直推出不重合 in H3.
tauto.

assert(Perp C C' O A').
apply 直角转L形垂直于 in H5; auto.
apply 垂直于的交换性 in H5.
apply 垂直于转T形垂直 in H5.
induction H5.
apply 垂直的对称性.
apply (垂线共线点也构成垂直1 _ C'); auto.
Perp.
ColR.
apply 垂直推出不重合 in H5.
tauto.

assert(Col O A A').
ColR.
assert(Par A A' C C').
apply(l12_9 A A' C C' O A'); Cop.
induction H17.


assert(HH:=l12_6 A A' C C' H17).

(*--------------------------------*)
assert(OS C C' A A').
apply(l12_6 C C' A A').
Par.
assert(OS C C' A B).
apply(out_one_side C C' A B).
left.
intro.
apply H17.
exists A.
split; Col.
unfold Out.
repeat split; auto.
intro.
subst C.
apply 中间性的同一律 in H.
contradiction.
right.
Between.

assert(OS C C' A' B).
apply(one_side_transitivity C C' A' A); auto.
apply one_side_symmetry.
assumption.

assert(Out C' B A').
induction H6.
unfold Out.
repeat split.
intro.
subst C'.
clean_trivial_hyps.
unfold OS in H18.
ex_and H18 T.
unfold TS in H4.
分离合取式.
apply H4.
Col.
intro.
subst C'.
apply H17.
exists A'.
split; Col.
left.
Between.

induction H6.

assert(TS C C' B A').
unfold TS.
repeat split.
intro.
unfold OS in H19.
ex_and H19 T.
unfold TS in H22.
分离合取式.
contradiction.
intro.
apply H17.
exists A'.
split; Col.
exists C'.
split; Col.
apply one_side_symmetry in H20.
apply l9_9_bis in H20.
contradiction.

unfold Out.
repeat split.
intro.
subst C'.
apply H17.
exists A.
apply 中间性蕴含共线1 in H.
split; Col.
intro.
subst C'.
apply H17.
exists A'.
split; Col.
right; auto.

(*****************************)

assert(Out A' B C').
induction H6.
unfold Out.
repeat split.
intro.
subst A'.
clean_trivial_hyps.
apply H17.
exists C.
apply 中间性蕴含共线1 in H.
split; Col.
intro.
subst C'.
unfold Out in H21.
tauto.
left.
auto.

induction H6.
unfold Out in H21.
分离合取式.
unfold Out.
repeat split.
intro.
subst A'.
apply H17.
exists C.
apply 中间性蕴含共线1 in H.
split; Col.
auto.
induction H23.
left.
Between.

apply False_ind.
apply H22.
apply (双中间性推出点重合 _ _ B); Between.

(***************************)

assert(OS A A' B C).
apply(out_one_side A A' B C).
right.
intro.
apply H17.
exists C.
split; Col.
unfold Out.
repeat split; auto.
intro.
subst C.
apply 中间性的同一律 in H.
contradiction.

assert(OS A A' C' B).
apply(one_side_transitivity A A' C' C);
apply one_side_symmetry; auto.


(***********************)
assert(TS A A' B C').
unfold TS.
repeat split.
intro.
unfold OS in H22.
ex_and H22 T.
unfold TS in H22.
分离合取式.
contradiction.
intro.
apply H17.
exists C'.
split; Col.
exists A'.
split; Col.
Between.
apply one_side_symmetry in H23.
apply l9_9_bis in H23.
contradiction.

unfold Out in *.
分离合取式.
clean_duplicated_hyps.

induction H26; induction H24.
assumption.
apply False_ind.
apply H21.
apply(双中间性推出点重合 _ _ A'); Between.
apply False_ind.
apply H10.
apply(双中间性推出点重合 _ _ C'); Between.
apply False_ind.
apply H25.
apply(双中间性推出点重合 _ _ B); Between.
分离合取式.


assert(~Col O C' C).
apply(成直角三点不共线); auto.
apply False_ind.
apply H21.

assert(A<>C).
intro.
subst C.
apply 中间性的同一律 in H.
subst B.
tauto.
apply 中间性蕴含共线1 in H.
ColR.

(********************************)

assert(Perp A A' O A').
apply 直角转L形垂直于 in H3; auto.
apply 垂直于的交换性 in H3.
apply 垂直于转T形垂直 in H3.
induction H3.
Perp.
apply 垂直推出不重合 in H3.
tauto.

assert(Perp B B' O A').
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4.
apply 垂直的对称性.
apply (垂线共线点也构成垂直1 _ B'); Col.
Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par A A' B B').
apply(l12_9 A A' B B' O A'); Cop.

induction H15.
assert(HH:=l12_6 A A' B B' H15).



assert(TS B B' A C).
unfold TS.
repeat split; Col.
intro.
apply H15.
exists A.
split; Col.
intro.
apply H11.
apply (l6_21_两线交点的唯一性 B B' A C); Col.
intro.
apply H15.
exists A.
split; Col.
intro.
subst C.
apply 中间性的同一律 in H.
subst B.
tauto.
exists B.
split; Col.

assert(OS B B' A A').
apply(l12_6 B B' A A').
Par.

assert(HP:= l9_8_2 B B' A A' C H16 H17).


induction(两点重合的决定性 C C').
subst C'.
unfold TS in HP.
分离合取式.
ex_and H20 T.

assert(T = B').
apply (l6_21_两线交点的唯一性 B B' A' C); Col.
intro.
subst A'.
apply 中间性的同一律 in H21.
subst T.
contradiction.
subst T.
assumption.

assert(Perp C C' O A').
apply 直角转L形垂直于 in H5; auto.
apply 垂直于的交换性 in H5.
apply 垂直于转T形垂直 in H5.
induction H5.
apply 垂直的对称性.
apply (垂线共线点也构成垂直1 _ C'); Perp.
ColR.
apply 垂直推出不重合 in H5.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A'); auto.
exists O.
left.
split; ColR.
exists C'.
left.
split; ColR.
exists B'.
left.
split; Col.
exists B'.
left.
split; Col.
induction H20.

assert(HQ:=l12_6 B B' C C' H20).

assert(TS B B' C' A').
apply(l9_8_2 B B' C C' A'); auto.
apply l9_2.
assumption.
unfold TS in H21.
分离合取式.
ex_and H23 T.
assert(T = B').
apply (l6_21_两线交点的唯一性 B B' A' C'); Col.
intro.
subst C'.
apply 中间性的同一律 in H24.
subst T.
contradiction.
subst T.
Between.
分离合取式.
unfold TS in HP.
分离合取式.
apply False_ind.
apply H25.
ColR.
分离合取式.

apply 垂直的左交换性 in H13.
apply L形垂直推出不共线 in H13.
apply False_ind.
apply H13.
ColR.
Qed.


Lemma per3_preserves_bet2_aux : forall O A B C B' C', Col O A C -> A <> C' ->
                               Bet A B' C' -> O <> A -> O <> B' -> O <> C'
                               -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A C' -> Bet A B C.
Proof.
intros O A B C B' C'.
intro HX.
intros.
induction(两点重合的决定性 A B).
subst B.
Between.
induction(两点重合的决定性 B C).
subst C.
Between.

assert(Col O A B').
apply 中间性蕴含共线1 in H0.
ColR.
assert(Col O B' C').
apply 中间性蕴含共线1 in H0.
ColR.

induction(两点重合的决定性 B B').
subst B'.
assert(Col O C C').
apply 中间性蕴含共线1 in H0.
ColR.
assert(C = C').
apply(直角边共线点也构成直角2_eq C C' O); Col; Perp.
subst C'.
assumption.
assert(C <> C').
intro.
subst C'.
apply 成直角三点不共线 in H4; auto.
apply H4.
ColR.

assert(Perp O A C C').
apply 直角转L形垂直于 in H5; auto.
apply 垂直于的交换性 in H5.
apply 垂直于转T形垂直 in H5.
induction H5.
apply (垂线共线点也构成垂直1 _ C'); Col; Perp.
apply 垂直推出不重合 in H5.
tauto.

assert(Perp O A B B').
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4.
apply (垂线共线点也构成垂直1 _ B'); Col; Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A); [Cop..|Perp|Perp].

induction H16.
assert(HH:=l12_6 B B' C C' H16).
assert(TS B B' A C').
repeat split.
intro.
assert(Per B B' A).
apply(直角边共线点也构成直角2 B B' O A); Col; Perp.
apply 成直角三点不共线 in H18; auto.
apply H18.
Col.
intro.
subst B'.
clean_trivial_hyps.
apply H16.
exists C.
split; Col.
intro.
apply H16.
exists C'.
split; Col.
exists B'.
split; Col.

assert(TS B B' C A).
apply(l9_8_2 B B' C' C A).
apply l9_2; auto.
apply one_side_symmetry; auto.
unfold TS in H18.
分离合取式.
ex_and H20 T.
assert(B = T).
apply (l6_21_两线交点的唯一性 A C B' B); Col.
assert(A <> C).
intro.
subst C.
apply 中间性的同一律 in H21.
subst T.
contradiction.
intro.
apply 中间性蕴含共线1 in H0.
apply H19.
ColR.
subst T.
Between.

分离合取式.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.
assert(Perp O B' C B').
apply(垂线共线点也构成垂直1 O A C B' B'); Col.
apply 垂直的左交换性 in H0.
apply L形垂直推出不共线 in H0.
apply H0.
ColR.

assert(Per C C' B').
apply(直角边共线点也构成直角2 C C' O B'); Col; Perp.
apply 成直角三点不共线 in H21; auto.
apply False_ind.
apply H21.
Col.
Qed.

Lemma per3_preserves_bet2 : forall O A B C A' B' C', Col O A C -> A' <> C' ->
                               Bet A' B' C' -> O <> A' -> O <> B' -> O <> C'
                               -> Per O A' A -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A' C' -> Bet A B C.

Proof.
intros O A B C A' B' C'.
intro HX.
intros.
induction(两点重合的决定性 A A').
subst A'.
apply (per3_preserves_bet2_aux O A B C B' C');auto.
induction(两点重合的决定性 C C').
subst C'.
apply 中间性的对称性.
apply(per3_preserves_bet2_aux O C B A B' A'); Col; Between.

assert(Perp O A' C C').
apply 直角转L形垂直于 in H6; auto.
apply 垂直于的交换性 in H6.
apply 垂直于转T形垂直 in H6.
induction H6.
apply (垂线共线点也构成垂直1 _ C'); Col; Perp.
apply 垂直推出不重合 in H6.
tauto.

assert(Perp O A' A A').
apply 直角转L形垂直于 in H4; auto.
apply 垂直于的交换性 in H4.
apply 垂直于转T形垂直 in H4.
induction H4.
Perp.
apply 垂直推出不重合 in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' O A'); [Cop..|Perp|Perp].

induction H13.
assert(HH:=l12_6 A A' C C' H13).
apply par_strict_symmetry in H13.
assert(HP:=l12_6 C C' A A' H13).

induction(两点重合的决定性 B B').
subst B'.

assert(OS A' A B C').
apply out_one_side.
right.
intro.
apply H13.
exists C'.
split; Col.
repeat split.
intro.
subst A'.
apply H13.
exists C.
split; Col.
auto.
left; auto.
apply invert_one_side in H14.
assert(OS A A' B C).
apply (one_side_transitivity _ _ _ C').
assumption.
apply one_side_symmetry.
assumption.

assert(Out A B C).
apply (col_one_side_out A A');auto.

assert(OS C' C B A').
apply out_one_side.
right.
intro.
apply H13.
exists A'.
split; Col.
repeat split.
intro.
subst C'.
apply H13.
exists A.
split; Col.
auto.
left; Between.
apply invert_one_side in H17.
assert(OS C C' B A).
apply (one_side_transitivity _ _ _ A').
assumption.
apply one_side_symmetry.
assumption.
apply one_side_symmetry in H18.

assert(Out C A B).
apply (col_one_side_out C C');Col.
unfold Out in *.
分离合取式.


induction H23; induction H21.
assumption.
assumption.
assert(A = C).
apply (双中间性推出点重合 A C B); auto.
subst C.
apply False_ind.
apply H13.
exists A.
split; Col.
assert(B = C).
apply (双中间性推出点重合 B C A); Between.
subst C.
Between.

(****************************************************************************************)

assert(Perp O A' B B').
apply 直角转L形垂直于 in H5; auto.
apply 垂直于的交换性 in H5.
apply 垂直于转T形垂直 in H5.
induction H5.
apply (垂线共线点也构成垂直1 _ B'); Col; Perp.
apply 中间性蕴含共线1 in H0.
ColR.
apply 垂直推出不重合 in H5.
tauto.

assert(Par B B' A A').
apply(l12_9 B B' A A' O A'); Perp.
exists O.
left.
统计不重合点.
split; ColR.
exists A'.
left.
split; Col.
exists B'.
left.
split; ColR.
exists A'.
left.
split; Col.

induction H16.
assert(HQ:=l12_6 B B' A A' H16).

assert(Par B B' C C').
apply(l12_9 B B' C C' O A'); Perp.
exists O.
left.
统计不重合点.
split; ColR.
exists C'.
left.
split; Col.
exists B'.
left.
统计不重合点.
split; ColR.
exists A'.
left.
split; Col.
induction H17.
assert(HR:=l12_6 B B' C C' H17).

assert(TS B B' A' C').
repeat split; auto.
intro.
apply H16.
exists A'.
split; Col.
intro.
apply H17.
exists C'.
split; Col.
exists B'.
split; Col.
apply one_side_symmetry in HQ.
assert(HH1:= l9_8_2 B B' A' A C' H18 HQ).
apply l9_2 in HH1.
apply one_side_symmetry in HR.
assert(HH2:= l9_8_2 B B' C' C A HH1 HR).
unfold TS in HH2.
分离合取式.
ex_and H21 T.
assert(B = T).
apply (l6_21_两线交点的唯一性 B B' A C); Col.
intro.
subst C.
apply H13.
exists A.
split; Col.
subst T.
Between.
分离合取式.

induction(两点重合的决定性 B C).
subst C.
Between.
assert(Col A C C').
ColR.
apply False_ind.
apply H13.
exists A.
split; Col.
分离合取式.

induction(两点重合的决定性 A B).
subst B.
Between.
assert(Col C A A').
ColR.
apply False_ind.
apply H13.
exists C.
split; Col.
分离合取式.

assert(A <> C).
intro.
subst C.
apply H.
apply(per2_col_eq O A' C' A); Col.

assert(Col O C C').
ColR.
apply False_ind.
apply 成直角三点不共线 in H6; auto.
apply H6.
Col.
Qed.


Lemma symmetry_preserves_per : forall A P B A' P', Per B P A -> 中点 B A A' -> 中点 B P P'
                                                   -> Per B P' A'.
Proof.
intros.
assert(HS:=构造对称点 A P).
ex_and HS C.
assert(HS:=构造对称点 C B).
ex_and HS C'.

assert(HH:= 对称保持中点 A P C A' P' C' B H0 H1 H3 H2).
unfold Per.
exists C'.
split.
assumption.
unfold Per in H.
ex_and H X.
assert(X = C).
apply(中点组的唯一性1 A P X C); auto.
subst X.
unfold 中点 in *.
分离合取式.
apply (等长的传递性 _ _ B A).
Cong.
apply(等长的传递性 _ _ B C).
assumption.
Cong.
Qed.

Lemma l13_1_aux : forall A B C P Q R,
   ~ Col A B C -> 中点 P B C -> 中点 Q A C -> 中点 R A B ->
   exists X, exists Y, 垂直于 R X Y A B /\ Perp X Y P Q /\ 共面 A B C X /\ 共面 A B C Y.
Proof.
intros A B C P Q R HC MBC MAC MAB.
assert(Q <> C).
intro.
subst Q.
unfold 中点 in MAC.
分离合取式.
apply 等长的同一性 in H0.
subst C.
apply HC.
Col.
assert(P <> C).
intro.
subst P.
unfold 中点 in MBC.
分离合取式.
apply 等长的同一性 in H1.
subst C.
apply HC.
Col.

assert(D1:Q<>R).
intro.
subst R.
assert(B=C).
apply(中点组的唯一性1 A Q); auto.
subst C.
apply M是AA中点则M与A重合 in MBC.
contradiction.

assert(D2:R <> B).
intro.
subst R.
unfold 中点 in MAB.
分离合取式.
apply 等长的同一性 in H2.
subst B.
apply HC.
Col.

assert(~Col P Q C).
intro.
apply HC.
unfold 中点 in *.
分离合取式.
apply 中间性蕴含共线1 in H2.
apply 中间性蕴含共线1 in H4.
apply 中间性蕴含共线1 in H6.
ColR.

assert(HH:= l8_18_过一点垂线之垂点的存在性 P Q C H1).
ex_and HH C'.

assert(HS1:=构造对称点 C' Q).
ex_and HS1 A'.
assert(HS1:=构造对称点 C' P).
ex_and HS1 B'.

assert(Cong C C' B B').
apply(l7_13_同中点组两侧等长 P C C' B B' MBC); 中点.
assert(Cong C C' A A').
apply(l7_13_同中点组两侧等长 Q C C' A A'); 中点.

assert(Per P B' B).
induction(两点重合的决定性 P C').
subst C'.
unfold 中点 in H5.
分离合取式.
apply 等长的对称性 in H8.
apply 等长的同一性 in H8.
subst B'.
apply 直角的对称性.
apply 角ABB成直角.

apply(symmetry_preserves_per C C' P B B'); 中点.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的左交换性.
apply (垂线共线点也构成垂直1 _ Q); Col.

assert(Per Q A' A).
induction(两点重合的决定性 Q C').
subst C'.
unfold 中点 in H4.
分离合取式.
apply 等长的对称性 in H9.
apply 等长的同一性 in H9.
subst A'.
apply 直角的对称性.
apply 角ABB成直角.
apply(symmetry_preserves_per C C' Q A A'); 中点.
apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.
apply 垂直的左交换性.
apply (垂线共线点也构成垂直1 _ P); Col.
Perp.

assert(Cl1: Col A' C' Q).
unfold 中点 in H4.
分离合取式.
apply 中间性蕴含共线1 in H4.
Col.

assert(Cl2: Col B' C' P).
unfold 中点 in H5.
分离合取式.
apply 中间性蕴含共线1 in H5.
Col.

assert(NE0: P <> Q).
apply 垂直推出不重合 in H3; tauto.

assert(NE1 : A' <> B').
intro.
subst B'.
apply NE0.
apply (中点的唯一性1 C' A'); auto.

assert(Cl3: Col A' B' P).
induction(两点重合的决定性 P C').
subst P.
unfold 中点 in  H5.
分离合取式.
apply 等长的对称性 in H10.
apply 等长的同一性 in H10.
subst C'.
Col.
induction(两点重合的决定性 Q C').
subst Q.
unfold 中点 in  H4.
分离合取式.
apply 等长的对称性 in H11.
apply 等长的同一性 in H11.
subst C'.
Col.
ColR.

assert(Cl4: Col A' B' Q).
induction(两点重合的决定性 P C').
subst P.
unfold 中点 in  H5.
分离合取式.
apply 等长的对称性 in H10.
apply 等长的同一性 in H10.
subst C'.
Col.
induction(两点重合的决定性 Q C').
subst Q.
unfold 中点 in  H4.
分离合取式.
apply 等长的对称性 in H11.
apply 等长的同一性 in H11.
subst C'.
Col.
ColR.

assert(Cl5:Col A' B' C').
ColR.

assert(NE2 : C <> C').
apply 垂直推出不重合 in H3.
tauto.

assert(NE3: A <> A').
intro.
subst A'.
apply 等长的同一性 in H7.
contradiction.

assert(NE4: B <> B').
intro.
subst B'.
apply 等长的同一性 in H6.
contradiction.

assert(Per P A' A).
induction(两点重合的决定性 A' Q).
subst Q.
unfold 中点 in H4.
分离合取式.
apply 等长的同一性 in H10.
subst C'.
clean_trivial_hyps.
apply 垂直的左交换性 in H3.
apply L形垂直转垂直于 in H3.
apply 垂直于的交换性 in H3.
apply L形垂直于转直角 in H3.
unfold 中点 in MAC.
分离合取式.
apply 中间性蕴含共线1 in H2.
apply (直角边共线点也构成直角2 P A' C A); Col.
apply 直角的对称性.
apply (直角边共线点也构成直角2 A A' Q P); Perp.
ColR.

assert(Per Q B' B).
induction(两点重合的决定性 B' P).
subst P.
unfold 中点 in H5.
分离合取式.
apply 等长的同一性 in H11.
subst C'.
clean_trivial_hyps.
apply L形垂直转垂直于 in H3.
apply 垂直于的交换性 in H3.
apply L形垂直于转直角 in H3.
unfold 中点 in MBC.
分离合取式.
apply 中间性蕴含共线1 in H2.
apply (直角边共线点也构成直角2 Q B' C B); Col.
apply 直角的对称性.
apply (直角边共线点也构成直角2 B B' P Q); Perp.
ColR.

assert(Per A' B' B).
apply 直角的对称性.
induction(两点重合的决定性 B' P).
subst P.
unfold 中点 in H5.
分离合取式.
apply 等长的同一性 in H12.
subst C'.
clean_trivial_hyps.
apply(直角边共线点也构成直角2 B B' Q A'); Col; Perp.
apply(直角边共线点也构成直角2 B B' P A'); Col; Perp.

assert(Per B' A' A).
apply 直角的对称性.
induction(两点重合的决定性 A' Q).
subst Q.
unfold 中点 in H4.
分离合取式.
apply 等长的同一性 in H13.
subst C'.
clean_trivial_hyps.
apply(直角边共线点也构成直角2 A A' P B'); Col; Perp.
apply(直角边共线点也构成直角2 A A' Q B'); Col; Perp.


assert(NC1 : ~Col A' B' A).
apply 成直角三点不共线 in H13; auto.
intro.
apply H13.
Col.

assert(NC2 : ~Col A' B' B).
apply 成直角三点不共线 in H12; auto.

(****************************************)

assert(HM:=中点的存在性 A' B').
ex_and HM X.

assert(HP:=l10_15 A' B' X A).
destruct HP as [y []]; Col.

assert(HH:=ex_sym X y A).
ex_and HH B''.

assert( X <> y).
apply 垂直推出不重合 in H15.
分离合取式.
auto.


assert(对称 B'' A X y).
unfold 对称.
left.
repeat split;auto.
ex_and H18 M.
exists M.
split; Col.

assert(对称 A' B' X y).
unfold 对称.
left.
split; auto.
repeat split.
exists X.
split; [中点|Col].
left.
Perp.
apply l10_4 in H20.

assert(HH:= l10_10 X y B''  B' A A' H20 H21).

assert(Per A' B' B'').
unfold 对称 in *.
induction H20; induction H21.
分离合取式.

apply(image_spec_preserves_per B' A' A A' B' B'' X y); auto.
apply l10_4_spec.
assumption.
分离合取式.
contradiction.
分离合取式.
contradiction.
分离合取式.
contradiction.

unfold 对称 in H21.
induction H21.
分离合取式.
unfold 严格对称 in H23.


assert(OS A' B' A B'').
induction H17.
assert(Par A' B' A B'').
assert(共面 A y A' X).
apply col_cop__cop with B'; Col; Cop.
assert(共面 A y B' X).
apply col_cop__cop with A'; Col; Cop.
assert(~ Col A X y).
intro.
assert(A=B'').
apply (image_id X y); Col.
统计不重合点.
auto.
apply(l12_9 A' B' A B'' X y); Perp.
Cop.
apply coplanar_trans_1 with A; Cop.
Cop.
apply coplanar_trans_1 with A; Cop.
induction H24.
apply( l12_6 A' B' A B'' H24).
分离合取式.

apply 成直角三点不共线 in H22; auto.
apply False_ind.
apply H22.
ColR.
intro.
subst B''.
apply 等长的对称性 in HH.
apply 等长的同一性 in HH.
subst A'.
apply 等长的同一性 in H7.
subst C'.
tauto.

subst B''.
apply one_side_reflexivity.
intro.
apply NC1.
Col.

assert(OS A' B' A B).
unfold OS.
exists C.
split.
unfold TS.
repeat split; Col.
intro.
apply H1.
ColR.
exists Q.
split; Col.
unfold 中点 in MAC.
tauto.
unfold TS.
repeat split; Col.
intro.
apply H1.
ColR.
exists P.
split; Col.
unfold 中点 in MBC.
tauto.

(*********************************)


assert( Col B B'' B').
apply cop_per2__col with A'; Perp.
apply 等价共面ACDB.
apply coplanar_trans_1 with A; Col; Cop.
assert(Cong B B' A A').
apply 等长的传递性 with C C'; Cong.

assert(B = B'' \/ 中点 B' B B'').
apply( 共线点间距相同要么重合要么中点); Col.

apply 等长的传递性 with A A'; Cong.
induction H28.
subst B''.

exists R.
exists X.

ex_and H18 M.
assert(R = M).
apply (中点的唯一性1 A B); auto.
subst M.

assert(A <> B).
intro.
subst B.
apply HC; Col.

assert(Col R A B).
unfold 中点 in MAB.
分离合取式.
apply 中间性蕴含共线1 in H31.
Col.

assert(X <> R).
intro.
subst X.
assert(Par A B A' B').
assert(共面 A y A' R).
apply col_cop__cop with B'; Col; Cop.
assert(共面 A y B' R).
apply col_cop__cop with A'; Col; Cop.
assert(~ Col A R y).
intro.
assert(A=B).
apply (image_id R y); Col.
统计不重合点.
auto.
apply(l12_9 A B A' B' R y); Perp.
Cop.
Cop.
apply coplanar_trans_1 with A; Cop.
apply coplanar_trans_1 with A; Cop.
induction H17.
Perp.
contradiction.
induction H32.
apply H32.
exists R.

unfold 中点 in H14.
分离合取式.
apply 中间性蕴含共线1 in H14.
split; Col.
分离合取式.
apply NC1.
Col.

split.

apply(l8_14_2_1b_bis_交点是垂点 R X A B R); Col.
induction H17.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ y); auto.
contradiction.

split.

apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ y);auto.
apply 垂直的对称性.
induction(两点重合的决定性 B' P).
subst P.
apply(垂线共线点也构成垂直1 _ A');auto.
Perp.
Col.
apply(垂线共线点也构成垂直1 _ B');auto.
apply 垂直的左交换性.

apply(垂线共线点也构成垂直1 _ A');auto.
Perp.
Col.
ColR.

split.
exists R.
left.
split; Col.
assert(Col P Q X).
ColR.
apply coplanar_pseudo_trans with P Q C; Cop.

assert(TS A' B' B B'').
unfold TS.
repeat split; auto.
intro.
apply NC2; Col.
intro.
apply 成直角三点不共线 in H22; auto.
apply H22.
Col.
intro.
subst B''.
unfold 中点 in H28.
分离合取式.
apply 等长的同一性 in H30.
subst B'.
unfold OS in H24.
ex_and H24 T.
unfold TS in H30.
分离合取式.
apply H30.
Col.
exists B'.
split; Col.
unfold 中点 in H28.
tauto.
assert(OS A' B' B B'').
apply (one_side_transitivity A' B' B A ).
apply one_side_symmetry.
assumption.
assumption.
apply l9_9 in H29.
contradiction.
分离合取式.
contradiction.
Qed.

Lemma l13_1 : forall A B C P Q R,
   ~ Col A B C -> 中点 P B C -> 中点 Q A C -> 中点 R A B ->
   exists X, exists Y, 垂直于 R X Y A B /\ Perp X Y P Q.
Proof.
intros.
destruct (l13_1_aux A B C P Q R) as [X [Y]]; trivial.
分离合取式.
exists X.
exists Y.
split; assumption.
Qed.



Lemma per_lt : forall A B C, A <> B ->  C <> B -> Per A B C -> Lt A B A C /\ Lt C B A C.
  Proof.
    intros.
    assert(Lt B A A C /\ Lt B C A C).
      apply( l11_46_非锐角三角形中大角对边最长 A B C); auto.
    分离合取式.
    split; apply 长度小于的左交换性; assumption.
  Qed.

Lemma cong_四点成首末边等长双垂直S形则对边等长a : forall A B C P,  Cong A B C B -> Perp A C B P -> 等角 A B P C B P /\ TS B P A C.
Proof.
    intros.
    assert(A <> C /\ B <> P).
      split.
        apply 垂直推出不重合1 in H0.
        assumption.
      apply 垂直推出不重合2 in H0.
      assumption.
    分离合取式.
    assert(A <> B).
      intro.
      subst B.
      apply 等长的对称性 in H.
      apply 等长的同一性 in H.
      apply H1.
      auto.
    assert(C <> B).
      intro.
      subst B.
      apply 等长的同一性 in H.
      contradiction.
    induction(共线的决定性 A B C).
      assert(~ Col B A P).
        apply L形垂直推出不共线.
        apply 垂直的交换性.
        apply (垂线共线点也构成垂直1 _ C); Col.
      assert(Per P B A).
        apply L形垂直于转直角.
        apply 垂直于的交换性.
        apply L形垂直转垂直于.
        apply 垂直的对称性.
        eapply (垂线共线点也构成垂直1 _ C); Col.
      assert(Per P B C).
        apply L形垂直于转直角.
        apply 垂直于的交换性.
        apply L形垂直转垂直于.
        apply 垂直的对称性.
        eapply (垂线共线点也构成垂直1 _ A); Col.
        Perp.
      apply 直角的对称性 in H7.
      apply 直角的对称性 in H8.
      split.
        apply l11_16_直角相等; auto.
      assert( A = C \/ 中点 B A C).
        eapply 共线点间距相同要么重合要么中点; Cong.
      induction H9.
        contradiction.
      unfold TS.
      repeat split.
        auto.
        intro.
        apply H6.
        Col.
        intro.
        apply H6.
        ColR.
      exists B.
      unfold 中点 in H9.
      分离合取式.
      split; [Col|Between].
    assert(HH:= H0).
    unfold Perp in HH.
    ex_and HH T.
    apply 垂点是交点 in H6.
    分离合取式.
    assert(B <> T).
      intro.
      subst T.
      apply H5.
      Col.
    assert(Perp B T A C).
      apply (垂线共线点也构成垂直1 _ P); Perp.
    assert(A <> T).
      intro.
      subst T.
      apply 垂直的交换性 in H9.
      apply L形垂直转垂直于 in H9.
      apply 垂直于的交换性 in H9.
      apply L形垂直于转直角 in H9.
      assert(Lt B A B C /\ Lt C A B C).
        apply( per_lt B A C); auto.
      分离合取式.
      unfold Lt in H10.
      分离合取式.
      apply H12.
      Cong.
    assert(C <> T).
      intro.
      subst T.
      apply 垂直的左交换性 in H9.
      apply L形垂直转垂直于 in H9.
      apply 垂直于的交换性 in H9.
      apply L形垂直于转直角 in H9.
      assert(Lt B C B A /\ Lt A C B A).
        apply( per_lt B C A); auto.
      分离合取式.
      unfold Lt in H11.
      分离合取式.
      apply H13.
      Cong.
    assert(垂直于 T B T T A).
      apply 垂直于的交换性.
      apply L形垂直转垂直于.
      apply 垂直的对称性.
      apply (垂线共线点也构成垂直1 _ C).
        assumption.
        apply 垂直的对称性.
        apply 垂直的左交换性.
        apply (垂线共线点也构成垂直1 _ P); Perp.
      Col.
    assert(垂直于 T B T T C).
      apply 垂直于的交换性.
      apply L形垂直转垂直于.
      apply 垂直的对称性.
      apply (垂线共线点也构成垂直1 _ A).
        assumption.
        apply 垂直的对称性.
        apply 垂直的左交换性.
        apply (垂线共线点也构成垂直1 _ P); Perp.
      Col.
    assert(Cong T A T C /\ 等角 T A B T C B /\ 等角 T B A T B C).
      apply( l11_52 A T B C T B); Cong.
        eapply l11_16_直角相等; auto.
          apply L形垂直于转直角.
          apply 垂直于的交换性.
          apply 垂直于的对称性.
          assumption.
        apply L形垂直于转直角.
        apply 垂直于的交换性.
        apply 垂直于的对称性.
        assumption.
      assert(Lt B T B A /\ Lt A T B A).
        apply( per_lt B T A); auto.
        apply L形垂直于转直角.
        assumption.
      分离合取式.
      apply 长度小于等于的交换性.
      unfold Lt in H14.
      分离合取式.
      assumption.
    分离合取式.
    split.
      induction(中间性的决定性 P B T).
        apply 等角的交换性.
        eapply l11_13; auto.
          apply H16.
          Between.
        Between.
      apply 等角的交换性.
      assert(Out B T P).
        unfold Out.
        repeat split; auto.
        induction H7.
          right.
          assumption.
        induction H7.
          left.
          Between.
        apply 中间性的对称性 in H7.
        contradiction.
      eapply l11_10.
        apply H16.
        apply l6_6.
        assumption.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
      apply out_trivial.
      auto.
    assert(A = C \/ 中点 T A C).
      apply 共线点间距相同要么重合要么中点; Col.
    induction H17.
      contradiction.
    unfold TS.
    repeat split; Col.
      assert(~ Col T A B).
        apply L形垂直推出不共线.
        apply 垂直于转T形垂直 in H12.
        induction H12.
          apply 垂直推出不重合1 in H12.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
      assert(~ Col T C B).
        apply L形垂直推出不共线.
        apply 垂直于转T形垂直 in H13.
        induction H13.
          apply 垂直推出不重合1 in H13.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
    exists T.
    apply midpoint_bet in H17.
    split; Col.
Qed.




Lemma perp_per_bet : forall A B C P, ~Col A B C -> Col A P C -> Per A B C -> 垂直于 P P B A C -> Bet A P C.
Proof.
intros.
assert( A <> C).
intro.
subst C.
apply H.
Col.
assert(Bet A P C /\ A <> P /\ C <> P).
apply(l11_47 A C B P); auto.
Perp.
tauto.
Qed.





Lemma ts_per_per_ts : forall A B C D, TS A B C D -> Per B C A -> Per B D A -> TS C D A B.
Proof.
intros.
assert(HTS:= H).
    unfold TS in H.
    assert (~ Col C A B).
      分离合取式.
      assumption.
    分离合取式.
    clear H.
    assert (A <> B).
      intro.
      subst B.
      Col.
    ex_and H4 P.
    统计不重合点.
    show_distinct C D.
contradiction.

unfold TS.
repeat split; auto.
intro.
assert(A = P).
apply 中间性蕴含共线1 in H5.
apply (l6_21_两线交点的唯一性 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq A C D B); Perp.
Col.
intro.
assert(B = P).
apply 中间性蕴含共线1 in H5.
apply (l6_21_两线交点的唯一性 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq B C D A); Col.
exists P.
split.
Col.

assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_过一点垂线之垂点的存在性 A B C); Col.
ex_and H7 C'.

assert(exists X : Tpoint, Col A B X /\ Perp A B D X).
apply(l8_18_过一点垂线之垂点的存在性 A B D); Col.
ex_and H12 D'.

assert( A <> C').
intro.
subst C'.
apply L形垂直转垂直于 in H8.
apply 垂直于的交换性 in H8.
apply L形垂直于转直角 in H8.
assert(A = C).
apply (ABC和ACB均直角则B与C重合 B); Perp.
subst C.
tauto.

assert( A <> D').
intro.
subst D'.
apply L形垂直转垂直于 in H14.
apply 垂直于的交换性 in H14.
apply L形垂直于转直角 in H14.
assert(A = D).
apply (ABC和ACB均直角则B与C重合 B); Perp.
subst D.
tauto.


assert(Bet A C' B).
apply(perp_per_bet A C B C'); Col.
Perp.
assert(Perp A C' C' C).
apply(垂线共线点也构成垂直1 _ B); Col; Perp.
apply 垂直于的对称性.
apply 垂直于的右交换性.
apply(l8_15_1_垂线顶点在该线上则其为垂点 A B C C'); auto.

assert(Bet A D' B).
apply(perp_per_bet A D B D'); Col.
Perp.
assert(Perp A D' D' D).
apply(垂线共线点也构成垂直1 _ B); Col; Perp.
apply 垂直于的对称性.
apply 垂直于的右交换性.
apply(l8_15_1_垂线顶点在该线上则其为垂点 A B D D'); auto.

induction(两点重合的决定性 C' P).
subst C'.
assumption.

induction(两点重合的决定性 D' P).
subst D'.
assumption.

induction(两点重合的决定性 A P).
subst P.
Between.
induction(两点重合的决定性 B P).
subst P.
Between.

assert(Bet C' P D').
apply(per13_preserves_bet C P D C' D'); Col.
ColR.
assert(Perp P C' C' C).
apply(垂线共线点也构成垂直1 _ A);auto.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ B);Perp.
Col.
ColR.
apply 垂直的交换性 in H24.
apply L形垂直转垂直于 in H24.
apply 垂直于的交换性 in H24.
apply L形垂直于转直角 in H24.
assumption.

assert(Perp P D' D' D).
apply(垂线共线点也构成垂直1 _ A);auto.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ B);Perp.
Col.
ColR.
apply 垂直的交换性 in H24.
apply L形垂直转垂直于 in H24.
apply 垂直于的交换性 in H24.
apply L形垂直于转直角 in H24.
assumption.

apply bet3__bet with C' D'; assumption.
Qed.


Lemma l13_2_1 : forall A B C D E, TS A B C D -> Per B C A -> Per B D A -> Col C D E
    -> Perp A E C D -> 等角 C A B D A B
    -> 等角 B A C D A E /\ 等角 B A D C A E /\ Bet C E D.
Proof.
    intros.
    intros.
    assert(HH:= H).
    unfold TS in HH.
    assert (~ Col C A B).
      分离合取式.
      assumption.
    分离合取式.
    assert(A <> C /\ A <> B /\ A <> D).
      unfold 等角 in H4.
      分离合取式.
      repeat split; auto.
    分离合取式.
    assert(Cong B C B D /\ Cong A C A D /\ 等角 C B A D B A).
      apply(l11_50_2 B A C B A D).
        intro.
        apply H6.
        Col.
        eapply l11_16_直角相等; auto.
          apply 直角的对称性.
          auto.
          intro.
          subst C.
          apply H6.
          Col.
          apply 直角的对称性.
          auto.
        intro.
        subst D.
        apply H7.
        Col.
        apply 等角的交换性.
        auto.
      Cong.
    分离合取式.
    assert(Perp C D A B).
      apply( cong_conga_perp C A D B); Cong.
    assert(Col A B E).
      apply cop_perp2__col with C D.
        exists E.
        left.
        split; Col.
        apply 垂直的对称性.
        apply H15.
      auto.
    assert(TS C D A B).
      apply ts_per_per_ts; auto.
    unfold TS in H17.
    分离合取式.
    ex_and H19 T1.
    ex_and H8 T.
    assert(T = T1).
      apply 中间性蕴含共线1 in H20.
      apply 中间性蕴含共线1 in H21.
      统计不重合点.
      apply (l6_21_两线交点的唯一性 A B C D); Col.
    subst T1.
    assert(T = E).
      统计不重合点.
      apply (l6_21_两线交点的唯一性 A B C D); Col.
    subst T.
    split.
      apply 等角的左交换性.
      apply l11_10 with C B D B; try apply out_trivial; auto.
      repeat split; auto.
      intro.
      subst E.
      contradiction.
    split.
      apply 等角的对称性.
      apply 等角的右交换性.
      apply l11_10 with C B D B; try apply out_trivial; auto.
        repeat split; auto.
        intro.
        subst E.
        contradiction.
    assumption.
Qed.


  Lemma 广义三角形中位线平行于第三边 : forall A B C P Q, ~Col A B C -> 中点 P B C -> 中点 Q A C -> 严格平行 A B Q P.
  Proof.
  intros.
   assert(HM:= 中点的存在性 A B).
   ex_and HM R.
   assert(HH:= l13_1_aux A B C P Q R H H0 H1 H2).
   ex_and HH X.
   ex_and H3 Y.
assert(共面 X Y A P /\ 共面 X Y A Q /\ 共面 X Y B P /\ 共面 X Y B Q).
  assert(共面 A B C A).
  exists A.
  left.
  split; Col.
  assert(共面 A B C B).
  exists B.
  left.
  split; Col.
  assert(共面 A B C P).
  exists B.
  left.
  split; Col.
  assert(共面 A B C Q).
  exists A.
  left.
  split; Col.
  repeat split; apply coplanar_pseudo_trans with A B C; assumption.
分离合取式.
assert(HH:= 垂点是交点 X Y A B R H3).
分离合取式.
   apply 垂直于转T形垂直 in H3.
unfold 中点 in H2.
分离合取式.
apply 中间性蕴含共线1 in H2.
assert(X <> Y).
apply 垂直推出不重合 in H4.
tauto.

   induction H3.
   assert(Perp Y X A B).
apply (垂线共线点也构成垂直1 _ R); Perp.
Col.
apply 垂直的左交换性 in H15.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H16.
Par.
分离合取式.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21_两线交点的唯一性 A B C P); Col.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold 中点 in H0.
分离合取式.
apply 等长的对称性 in H21.
apply 等长的同一性 in H21.
subst C.
contradiction.

assert(Perp X Y A B).
apply (垂线共线点也构成垂直1 _ R); Perp.
Col.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H16.
Par.
分离合取式.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21_两线交点的唯一性 A B C P); Col.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold 中点 in H0.
分离合取式.
apply 等长的对称性 in H21.
apply 等长的同一性 in H21.
subst C.
contradiction.
Qed.

Lemma cop4_perp_in2__col : forall A B A' B' X Y P,
  共面 X Y A A' -> 共面 X Y A B' ->
  共面 X Y B A' -> 共面 X Y B B' ->
  垂直于 P A B X Y -> 垂直于 P A' B' X Y  -> Col A B A'.
Proof.
intros.
assert(HP1:= H3).
assert(HP2:=H4).
assert(Col A B P /\ Col X Y P).
apply 垂点是交点 in H3.
分离合取式.
split; Col.
分离合取式.
unfold 垂直于 in H3.
unfold 垂直于 in H4.
分离合取式.
induction(两点重合的决定性 A P);
induction(两点重合的决定性 P X).
subst A.
subst X.
assert(Per B P Y).
apply(H14 B Y); Col.
assert(Per A' P Y).
apply(H10 A' Y); Col.
apply 等价共线CAB.
apply cop_per2__col with Y; Cop.
subst A.
assert(Per B P X).
apply(H14 B X); Col.
assert(Per A' P X).
apply(H10 A' X); Col.
apply 等价共线CAB.
apply cop_per2__col with X; auto.
apply 等价共面CABD.
apply col_cop__cop with Y; Col; Cop.
subst X.
assert(Per A P Y).
apply(H14 A Y); Col.
induction(两点重合的决定性 P A').
subst A'.
assert(Per B' P Y).
apply(H10 B' Y); Col.
assert(Col A B' P).
apply cop_per2__col with Y; Cop.
ColR.

assert(Per A' P Y).
apply(H10 A' Y); Col.
assert(Col A A' P).
apply cop_per2__col with Y; Cop.
ColR.

assert(Per A P X).
apply(H14 A X); Col.
induction(两点重合的决定性 P A').
subst A'.
assert(Per B' P X).
apply(H10 B' X); Col.
assert(Col A B' P).
apply cop_per2__col with X; auto.
apply 等价共面CABD.
apply col_cop__cop with Y; Col; Cop.
ColR.

assert(Per A' P X).
apply(H10 A' X); Col.
assert(Col A A' P).
apply cop_per2__col with X; auto.
apply 等价共面CABD.
apply col_cop__cop with Y; Col; Cop.
ColR.
Qed.


Lemma l13_2 : forall A B C D E, TS A B C D -> Per B C A -> Per B D A -> Col C D E -> Perp A E C D
    -> 等角 B A C D A E /\ 等角 B A D C A E /\ Bet C E D.
Proof.
    intros.
    assert(HH:= H).
    unfold TS in HH.
    assert(~ Col C A B).
      分离合取式.
      assumption.
    分离合取式.
    assert(C <> D).
      intro.
      subst D.
      assert(OS A B C C).
        apply one_side_reflexivity.
        assumption.
      apply l9_9 in H.
      contradiction.
    assert(exists C', 等角 B A C D A C' /\ OS D A C' B).
      apply(给定角一边可作出与给定点同侧一点构成等角_非平角 B A C D A B).
        intro.
        apply H5.
        Col.
      intro.
      apply H6.
      Col.
    ex_and H9 E'.
    assert(A <> B /\ A <> C /\ A <> D).
      unfold 等角 in H9.
      分离合取式; auto.
    分离合取式.
    assert(HH:=l11_22 C A E' B D A B E').
    assert(HH1:=ts_per_per_ts A B C D H H0 H1).
    unfold TS in HH1.
    assert (~ Col A C D).
      分离合取式.
      assumption.
    分离合取式.
    ex_and H7 T.
    ex_and H17 T2.
    assert(T = T2).
      apply (l6_21_两线交点的唯一性 A B C D); Col.
    subst T2.
    assert(在角内 B D A C).
      unfold 在角内.
      repeat split; auto.
      exists T.
      split.
        Between.
      right.
      unfold Out.
      repeat split.
        intro.
        subst T.
        assert(~ Col C D A /\ Per A E D).
          apply(l8_16_1_共线四点和一垂直推另一直角 C D A D E H2).
            Col.
          apply 垂直的对称性.
          assumption.
        分离合取式.
        apply H20.
        Col.
        auto.
      left.
      assumption.
    assert(角度小于等于 C A B C A D).
      unfold 角度小于等于.
      exists B.
      split.
        apply l11_24_在角内的对称性.
        assumption.
      apply 同角相等; auto.
    assert(在角内 E' D A C).
      eapply lea_in_angle.
        apply 角度小于等于的交换性.
        eapply l11_30_等角保持小于等于.
        apply H21.
        apply 等角的交换性.
        assumption.
        apply 同角相等; auto.
      assert(HH1:=ts_per_per_ts A B C D H H0 H1).
      assert(OS D A C B).
        apply ts_ts_os.
          apply invert_two_sides.
          assumption.
        apply l9_2.
        assumption.
      eapply one_side_transitivity.
        apply H22.
      apply one_side_symmetry.
      assumption.
    unfold 在角内 in H22.
    分离合取式.
    ex_and H25 E''.
    induction H26.
      subst E''.
      apply False_ind.
      apply H15.
      apply 中间性蕴含共线1 in H25.
      Col.
    assert(等角 B A C D A E'').
      apply (l11_10 B A C D A E'); try apply out_trivial; auto.
    assert(A <> T).
      intro.
      subst T.
      apply H15.
      Col.
    induction(两点重合的决定性 E'' T).
      subst E''.
      apply l13_2_1; auto.
      eapply l11_10.
        apply 等角的左交换性.
        apply H27.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      unfold Out.
      repeat split; auto.
    assert(D <> E'').
      intro.
      subst E''.
      apply 等角的对称性 in H27.
      apply 零角的等角推出外共线 in H27.
      apply out_col in H27.
      apply H5.
      Col.
    assert(C <> E'').
      intro.
      subst E''.
      assert(OS C A B D).
        apply invert_one_side.
        apply ts_ts_os.
          assumption.
        apply ts_per_per_ts; auto.
      assert(Out A B D).
        apply(conga_os__out C A B D).
          apply 等角的交换性.
          assumption.
        assumption.
      apply out_col in H32.
      apply H6.
      Col.
    assert(A <> E'').
      intro.
      subst E''.
      unfold Out in H26.
      tauto.
    assert(~ Col E'' A B).
      intro.
      apply H29.
      apply 中间性蕴含共线1 in H25.
      apply (l6_21_两线交点的唯一性 A B C D); Col.
    assert(等角 C A E'' D A B).
      apply (l11_22 C A E'' B D A B E'').
      split.
        induction(one_side_dec A B C E'').
          right.
          split.
            auto.
          unfold OS.
          exists C.
          split.
            unfold TS.
            repeat split.
              auto.
              intro.
              apply H15.
              apply 中间性蕴含共线1 in H25.
              apply 等价共线BCA.
              eapply (共线的传递性2 _ E''); Col.
              intro.
              apply 中间性蕴含共线1 in H25.
              apply H15.
              apply 等价共线CAB.
              eapply (共线的传递性2 _ E''); Col.
            exists E''.
            split; Col.
          assert(TS A E'' T C).
            unfold TS.
            repeat split.
              auto.
              intro.
              apply H29.
              apply (l6_21_两线交点的唯一性 A B C D);Col.
              eapply (共线的传递性2 _ T); Col.
              apply 中间性蕴含共线1 in H25.
              Col.
              intro.
              apply H15.
              ColR.
            exists E''.
            split.
              Col.
            assert(Bet C T E'' \/ Bet C E'' T).
              eapply l5_3.
                apply H18.
              Between.
            induction H35.
              assert(TS A B C E'').
                unfold TS.
                repeat split; auto.
                exists T.
                split.
                  Col.
                auto.
              apply l9_9 in H36.
              contradiction.
            Between.
          eapply (l9_5 _ _ T _ A); Col.
          unfold Out.
          repeat split; auto.
        left.
        apply cop_nos__ts in H34; auto.
        split.
          auto.
        assert(OS A B D E'').
          eapply l9_8_1.
            apply l9_2.
            apply H.
          apply l9_2.
          assumption.
        assert(TS A E'' T D).
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H33.
            apply 等价共线CAB.
            apply(共线的传递性2 _ T); Col.
            intro.
            apply 中间性蕴含共线1 in H25.
            apply H15.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ E''); Col.
          exists E''.
          split.
            Col.
          assert(Bet D T E'' \/ Bet D E'' T).
            eapply l5_3.
              apply 中间性的对称性.
              apply H18.
            assumption.
          induction H36.
            assert(TS A B D E'').
              unfold TS.
              repeat split; auto.
              exists T.
              split; Col.
            apply l9_9 in H37.
            contradiction.
          Between.
        apply l9_2.
        eapply (l9_5 _ _ T _ A).
          auto.
          Col.
        unfold Out.
        repeat split; auto.
        apply col_cop__cop with D; Col; Cop.

      split.
        apply 等角的左交换性.
        auto.
      apply 等角的右交换性.
      apply 同角相等; auto.
    (***********************)
    prolong B C C' B C.
    prolong B D D' B D.
    assert(三角形全等 B A D D' A D).
      apply 直角的对称性 in H1.
      unfold Per in H1.
      ex_and H1 D''.
      assert(中点 D B D').
        unfold 中点.
        split; Cong.
      assert(D' = D'').
        eapply 中点组的唯一性1.
          apply H40.
        auto.
      subst D''.
      repeat split; Cong.
    assert(等角 B A D D' A D).
      apply 三角形全等推角等1; auto.
    assert(三角形全等 B A C C' A C).
      apply 直角的对称性 in H0.
      unfold Per in H0.
      ex_and H0 C''.
      assert(中点 C B C').
        unfold 中点.
        split; Cong.
      assert(C' = C'').
        eapply 中点组的唯一性1.
          apply H42.
        auto.
      subst C''.
      repeat split; Cong.
    assert(等角 B A C C' A C).
      apply 三角形全等推角等1; auto.
    assert(等角 E'' A C' D' A E'').
      apply l11_22 with C D.
      split.
        clear HH.
        (***************************************************)
        left.
        assert(OS C A D E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold Out.
          repeat split; auto.
          right.
          Between.
        assert(OS C A B D).
          apply 角内点和一端点在角另一边同侧.
            intro.
            apply H15.
            Col.
            intro.
            apply H5.
            Col.
          apply l11_24_在角内的对称性.
          auto.
        assert(TS C A B C').
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H5.
            Col.
            intro.
            apply H5.
            apply 中间性蕴含共线1 in H35.
            assert(C <> C').
              intro.
              subst C'.
              apply 等长的对称性 in H36.
              apply 等长的同一性 in H36.
              subst C.
              apply H16.
              Col.
            eapply (共线的传递性2 _ C'); Col.
          exists C.
          split; Col.
        assert(OS C A B E'').
          eapply one_side_transitivity.
            apply H44.
          auto.
        assert(OS D A C E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold Out.
          repeat split; auto.
        assert(OS D A B C).
          apply 角内点和一端点在角另一边同侧.
            intro.
            apply H15.
            Col.
            intro.
            apply H6.
            Col.
          auto.
        assert(TS D A B D').
          unfold TS.
          repeat split.
            auto.
            intro.
            apply H6.
            Col.
            intro.
            apply H6.
            apply 中间性蕴含共线1 in H37.
            assert(D <> D').
              intro.
              subst D'.
              apply 等长的对称性 in H38.
              apply 等长的同一性 in H38.
              subst D.
              apply H16.
              Col.
            eapply (共线的传递性2 _ D'); Col.
          exists D.
          split; Col.
        assert(OS D A B E'').
          eapply one_side_transitivity.
            apply H48.
          auto.
        split.
          apply invert_two_sides.
          eapply l9_8_2.
            apply H45.
          auto.
        apply invert_two_sides.
        apply l9_2.
        eapply l9_8_2.
          apply H49.
        auto.
      split.
        eapply 角等的传递性.
          apply 等角的交换性.
          apply H34.
        apply H40.
      apply 等角的对称性.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H27.
      apply 等角的右交换性.
      auto.
    assert(D' <> B).
      intro.
      subst D'.
      apply 中间性的同一律 in H37.
      subst D.
      apply H16.
      Col.
    assert(C' <> B).
      intro.
      subst C'.
      apply 中间性的同一律 in H35.
      subst C.
      apply H16.
      Col.
    assert(~ Col C' D' B).
      intro.
      apply H16.
      apply 中间性蕴含共线1 in H35.
      apply  中间性蕴含共线1 in H37.
      assert(Col C' B D).
        ColR.
      ColR.
    assert(严格平行 C' D' C D).
      apply(广义三角形中位线平行于第三边 C' D' B D C).
        auto.
        unfold 中点.
        split.
          Between.
        Cong.
      unfold 中点.
      split.
        Between.
      Cong.
    assert(TS A E'' C D).
      unfold TS.
      repeat split.
        auto.
        intro.
        apply H15.
        apply 中间性蕴含共线1 in H25.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ E''); Col.
        intro.
        apply H15.
        apply 中间性蕴含共线1 in H25.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ E''); Col.
      exists E''.
      split; Col.
      Between.
    assert(TS B A C D).
      apply 角端点在角内点与顶点连线两侧.
        intro.
        apply H5.
        Col.
        intro.
        apply H6.
        Col.
      apply l11_24_在角内的对称性.
      assumption.
    assert (OS A B C C').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold Out.
      repeat split; auto.
      intro.
      subst C.
      apply H5.
      Col.
    assert (OS A B D D').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold Out.
      repeat split; auto.
      intro.
      subst D.
      apply H6.
      Col.
    apply invert_two_sides in H49.
    assert(TS A B C' D).
      eapply l9_8_2.
        apply H49.
      auto.
    assert(TS A B C' D').
      apply l9_2.
      eapply l9_8_2.
        apply l9_2.
        apply H52.
      auto.
    assert(Perp  C' D' A E'').
      apply cong_conga_perp.
        apply 等角的右交换性 in H43.
        apply conga_cop__or_out_ts in H43.
        induction H43.
          assert(OS A B C' D').
            eapply (out_one_side_1 _ _ _ _ A); Col.
            intro.
            assert(B <> C').
              intro.
              subst C'.
              apply H46.
              Col.
            apply H5.
            apply 等价共线BCA.
            eapply 共线的传递性2.
              apply H55.
              apply 中间性蕴含共线1 in H35.
              Col.
            Col.
          apply l9_9 in H53.
          contradiction.
        apply invert_two_sides.
        assumption.
        apply coplanar_pseudo_trans with B C D; Cop.
        unfold 三角形全等 in *.
        分离合取式.
        apply 等长的传递性 with B A; Cong.
      apply 等角的左交换性.
      assumption.


assert(Cong A C' A B).
apply 直角的对称性 in H0.
unfold Per in H0.
ex_and H0 C''.
assert(C' = C'').
apply(中点组的唯一性1 B C C' C''); auto.
split; Cong.
subst C''.
Cong.

assert(Cong A D' A B).
apply 直角的对称性 in H1.
unfold Per in H1.
ex_and H1 D''.
assert(D' = D'').
apply(中点组的唯一性1 B D D' D''); auto.
split; Cong.
subst D''.
Cong.

assert(Cong A C' A D').
apply 等长的传递性 with A B; Cong.

assert(HM:=中点的存在性 C' D').
ex_and HM R.
assert(exists X Y : Tpoint, 垂直于 R X Y C' D' /\ Perp X Y D C /\ 共面 C' D' B X /\ 共面 C' D' B Y).
apply l13_1_aux; auto.
split; Between; Cong.
split; Between; Cong.
ex_and H59 X.
ex_and H60 Y.

assert(HXY:X <> Y).
apply 垂直推出不重合 in H60.
tauto.

assert(Perp C D A E'').

induction(两点重合的决定性 A R).
subst R.

assert(垂直于 A C' D' A E'').
assert_cols.
apply(l8_14_2_1b_bis_交点是垂点 C' D' A E'' A); Col.

assert(共面 B C' D' E'').
apply coplanar_pseudo_trans with B C D; Cop.
assert(共面 C' D' X E'').
apply coplanar_trans_1 with B; Col; Cop.
assert(共面 C' D' Y E'').
apply coplanar_trans_1 with B; Col; Cop.
assert(共面 C' D' X A).
exists A.
left.
split; Col.
assert(共面 C' D' Y A).
exists A.
left.
split; Col.
assert(Col X Y A).
apply(cop4_perp_in2__col X Y A E'' C' D' A); Perp.
assert(Col X Y E'').
apply(cop4_perp_in2__col X Y E'' A C' D' A); Perp.
apply 垂直的对称性.
induction(两点重合的决定性 Y A).
subst Y.
apply(垂线共线点也构成垂直1 _ X).
auto.
Perp.
Col.
apply(垂线共线点也构成垂直1 _ Y).
auto.
apply 垂直的左交换性.
apply (垂线共线点也构成垂直1 _ X); Col.
Perp.
ColR.

assert(R <> C').
intro.
subst R.
unfold 中点 in H58.
分离合取式.
apply 等长的对称性 in H64.
apply 等长的同一性 in H64.
subst D'.
apply 垂直推出不重合 in H54.
tauto.

assert(Per A R C').
unfold Per.
exists D'.
split; auto.
apply 直角转L形垂直于 in H65; auto.
apply 垂直于的对称性 in H65.
apply 垂直于转T形垂直 in H65.
induction H65.
apply 垂直的交换性 in H65.
assert(Perp C' D' R A).
apply(垂线共线点也构成垂直1 _ R).
intro.
subst D'.
apply 垂直推出不重合 in H54.
tauto.
assumption.
assert_cols.
Col.

assert(垂直于 R C' D' R A).
apply(l8_14_2_1b_bis_交点是垂点 C' D' R A R); Col.
assert_cols.
Col.

assert(共面 C' D' X A).
apply coplanar_trans_1 with B; Cop; Col.
assert(共面 C' D' Y A).
apply coplanar_trans_1 with B; Cop; Col.
assert(共面 C' D' X R).
exists R.
left.
split; Col.
assert(共面 C' D' Y R).
exists R.
left.
split; Col.
assert( Col X Y A).
apply(cop4_perp_in2__col X Y A R C' D' R); Perp.
assert( Col X Y R).
apply(cop4_perp_in2__col X Y R A C' D' R); Perp.

assert(Col A E'' R).
apply(cop_perp2__col A E'' R C' D'); Perp.
exists R.
left.
split; Col.

assert(Col A R X).
ColR.
assert(Col A R Y).
ColR.


apply 垂直的对称性.
induction(两点重合的决定性 X A).
subst X.
apply (垂线共线点也构成垂直1 _ Y); Perp.
ColR.
apply (垂线共线点也构成垂直1 _ X); Col; Perp.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ Y); Perp.
ColR.
apply 垂直推出不重合 in H65.
tauto.

    assert(Col A E E'').
      apply cop_perp2__col with C D; Perp.
      exists E.
      left.
      split; Col.
    assert(E'' = E).
      apply (l6_21_两线交点的唯一性 C D A E); Col.
      apply 垂直推出不重合1 in H3.
      assumption.
    subst E''.
    split.
      auto.
    split.
      apply 等角的对称性.
      apply 等角的右交换性.
      auto.
    Between.
Qed.

Lemma perp2_refl : forall A B P, A <> B -> Perp2 A B A B P.
Proof.
    intros.
    induction(共线的决定性 A B P).
      assert(HH:=两点不重合则存在不共线的点 A B H).
      ex_and HH X.
      assert(HH:=l10_15 A B P X  H0 H1).
      ex_and HH Q.
      unfold Perp2.
      exists Q.
      exists P.
      split; Perp.
      Col.
    assert(HH:=l8_18_过一点垂线之垂点的存在性 A B P H0).
    ex_and HH Q.
    unfold Perp2.
    exists P.
    exists Q.
    split; Perp.
    Col.
Qed.


Lemma perp2_sym : forall A B C D P, Perp2 A B C D P -> Perp2 C D A B P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_left_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A C D P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_right_comm : forall A B C D P, Perp2 A B C D P -> Perp2 A B D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_pseudo_trans : forall A B C D E F P, Perp2 A B C D P -> Perp2 C D E F P -> ~ Col C D P ->
  Perp2 A B E F P.
Proof.
    intros.
    unfold Perp2 in *.
    ex_and H X.
    ex_and H2 Y.
    ex_and H0 X'.
    ex_and H4 Y'.
    assert(Par X Y X' Y').
      assert(共面 P C D X).
      induction(两点重合的决定性 X P).
        subst.
        exists P.
        left.
        split; Col.
      apply 等价共面BCDA.
      apply 垂直蕴含共面.
      apply 垂线共线点也构成垂直1 with Y; Col.
      assert(共面 P C D Y).
      induction(两点重合的决定性 Y P).
        subst.
        exists P.
        left.
        split; Col.
      apply 等价共面BCDA.
      apply 垂直蕴含共面.
      apply 垂线共线点也构成垂直1 with X; Perp; Col.
      assert(共面 P C D X').
      induction(两点重合的决定性 X' P).
        subst.
        exists P.
        left.
        split; Col.
      apply 等价共面BCDA.
      apply 垂直蕴含共面.
      apply 垂线共线点也构成垂直1 with Y'; Col.
      assert(共面 P C D Y').
      induction(两点重合的决定性 Y' P).
        subst.
        exists P.
        left.
        split; Col.
      apply 等价共面BCDA.
      apply 垂直蕴含共面.
      apply 垂线共线点也构成垂直1 with X'; Perp; Col.
      apply (l12_9 _ _ _ _ C D); Perp; apply coplanar_trans_1 with P; Col.
    exists X.
    exists Y.
    assert(Col X X' Y').
      induction H6.
        unfold 严格平行 in H6.
        分离合取式.
        apply False_ind.
        apply H7.
        exists P.
        split; Col.
      分离合取式.
      auto.
    assert(Col Y X' Y').
      induction H6.
        unfold 严格平行 in H6.
        分离合取式.
        apply False_ind.
        apply H8.
        exists P.
        split; Col.
      分离合取式.
      auto.
    repeat split; auto.
    assert(X <> Y).
      apply 垂直推出不重合1 in H2.
      auto.
    induction(两点重合的决定性 X Y').
      subst Y'.
      apply (垂线共线点也构成垂直1 _ X').
        auto.
        Perp.
      ColR.
    apply (垂线共线点也构成垂直1 _ Y').
      auto.
      apply 垂直的左交换性.
      apply(垂线共线点也构成垂直1 _ X').
        auto.
        Perp.
      ColR.
    apply par_symmetry in H6.
    induction H6.
      unfold 严格平行 in H6.
      分离合取式.
      apply False_ind.
      apply H11.
      exists P.
      split; Col.
    分离合取式.
    Col.
Qed.

Lemma col_cop_perp2__pars_bis : forall P A B C D, ~ Col A B P ->
    Col C D P -> 共面 A B C D -> Perp2 A B C D P -> 严格平行 A B C D.
Proof.
    unfold Perp2.
    intros.
    ex_and H2 X.
    ex_and H3 Y.
    assert (Col X Y P) by Col.
    assert (HQ := 每组共线三点都有另一共线点 X Y P H5).
    ex_and HQ Q.
    apply (col_cop_perp2__pars P Q); trivial; apply 与垂线共线之线也为垂线1 with X Y; trivial.
Qed.

Lemma perp2_preserves_bet23 : forall O A B A' B', Bet O A B -> Col O A' B' -> ~Col O A A' ->
    Perp2 A A' B B' O -> Bet O A' B'.

Proof.
intros.

assert(HD1: A <> A').
intro.
subst A'.
apply H1.
Col.

induction(两点重合的决定性 A' B').
subst B'.
Between.

assert(A <> B).
intro.
subst B.
unfold Perp2 in H2.
ex_and H2 X.
ex_and H4 Y.
assert(Col A A' B').
apply(cop_perp2__col A A' B' X Y); Perp.
exists O.
left.
split; Col.
apply H1.
ColR.

assert(Par A A' B B').
unfold Perp2 in H2.
ex_and H2 X.
ex_and H5 Y.
assert(共面 X Y A B).
exists O.
left.
split; Col.
apply (l12_9 _ _ _ _ X Y); Perp.
induction(共线的决定性 B X Y).
exists A.
left.
统计不重合点.
split; ColR.
apply coplanar_trans_1 with B; Cop.
induction(共线的决定性 A X Y).
exists B.
left.
统计不重合点.
split; ColR.
apply coplanar_trans_1 with A; Cop.
exists O.
left.
split; Col.
induction H5.
assert(OS A A' B B').
apply l12_6; Par.
assert(TS A A' O B).
repeat split; Col.
intro.
apply H5.
exists B.
split; Col.
exists A.
split; Col.

assert(TS A A' B' O).
apply( l9_8_2 A A' B B' O); auto.
apply l9_2.
auto.

unfold TS in H8.
分离合取式.
ex_and H10 T.
assert(T = A').
apply (l6_21_两线交点的唯一性 A A' O B'); Col.
intro.
subst B'.
apply 中间性的同一律 in H11.
subst T.
contradiction.
subst T.
Between.

分离合取式.
apply False_ind.
apply H1.
ColR.
Qed.

Lemma perp2_preserves_bet13 : forall O B C B' C', Bet B O C -> Col O B' C' -> ~Col O B B' ->
    Perp2 B C' C B' O -> Bet B' O C'.

Proof.
intros.

induction(两点重合的决定性 C' O).
subst.
Between.
induction(两点重合的决定性 B' O).
subst.
Between.

assert(B <> O).
intro.
subst B.
apply H1.
Col.

assert(B' <> O).
intro.
subst B'.
apply H1.
Col.

assert(Col B O C).
apply 中间性蕴含共线1.
Between.

induction(两点重合的决定性 B C).
subst C.
apply 中间性的同一律 in H.
contradiction.

assert(Par B C' C B').
unfold Perp2 in H2.
ex_and H2 X.
ex_and H9 Y.
assert(共面 X Y B C).
exists O.
left.
split; Col.
assert(共面 X Y C' B').
exists O.
left.
split; Col.
apply (l12_9 _ _ _ _ X Y); Perp.
induction(共线的决定性 C' X Y).
exists B'.
left.
统计不重合点.
split; ColR.
apply coplanar_trans_1 with C'; Cop.
induction(共线的决定性 B X Y).
exists C.
left.
统计不重合点.
split; ColR.
apply coplanar_trans_1 with B; Cop.

assert(严格平行 B C' C B').
induction H9.
assumption.
分离合取式.
apply False_ind.
apply H1.
ColR.

assert(C<> O).
intro.
subst C.
assert(严格平行 B C' O C').
apply(par_strict_col_par_strict _ _ _ B'); auto.
apply H11.
exists C'.
Col.

assert(B' <> O).
intro.
subst B'.
assert(严格平行 B C' O B).
apply(par_strict_col_par_strict _ _ _ C); auto.
apply par_strict_right_comm.
assumption.
Col.
apply H12.
exists B.
split; Col.

unfold Perp2 in H2.
ex_and H2 X.
ex_and H13 Y.

assert(X <> Y).
apply 垂直推出不重合 in H13.
tauto.

induction(共线的决定性 X Y B).
assert(Col X Y C).
ColR.

apply(per13_preserves_bet_inv  B' O C' C B); Between.
Col.

apply L形垂直于转直角.
induction(两点重合的决定性 X C).
subst X.
assert(Perp C O B' C).
apply(垂线共线点也构成垂直1 _ Y); Perp.
ColR.
apply L形垂直转垂直于 in H18.
Perp.
assert(Perp X C C B').
apply(垂线共线点也构成垂直1 _ Y); Perp.
assert(Perp C O B' C).
apply(垂线共线点也构成垂直1 _ X); Perp.
ColR.
apply L形垂直转垂直于 in H20.
Perp.

apply L形垂直于转直角.
induction(两点重合的决定性 X B).
subst X.
assert(Perp B O C' B).
apply(垂线共线点也构成垂直1 _ Y); Perp.
ColR.
apply L形垂直转垂直于 in H18.
Perp.
assert(Perp X B C' B).
apply(垂线共线点也构成垂直1 _ Y); Perp.
assert(Perp B O C' B).
apply(垂线共线点也构成垂直1 _ X); Perp.
ColR.
apply L形垂直转垂直于 in H20.
Perp.

assert(HP1:=l8_18_过一点垂线之垂点的存在性 X Y B H16).
ex_and HP1 B0.
assert(~Col X Y C).
intro.
apply H16.
ColR.
assert(HP1:=l8_18_过一点垂线之垂点的存在性 X Y C H19).
ex_and HP1 C0.

assert(B0 <> O).
intro.
subst B0.
assert(Par B O B C').
apply(l12_9 B O B C' X Y); Perp; Cop.
induction H22.
apply H22.
exists B.
split; Col.
分离合取式.
apply H1.
ColR.

assert(C0 <> O).
intro.
subst C0.
assert(Par C O C B').
apply(l12_9 C O C B' X Y); Perp; Cop.
induction H23.
apply H23.
exists C.
split; Col.
分离合取式.
apply H1.
ColR.

assert(Bet B0 O C0).

apply(per13_preserves_bet B O C B0 C0); auto.
Between.
ColR.
apply L形垂直于转直角.
induction(两点重合的决定性 X B0).
subst X.
assert(Perp B0 O B B0).
apply(垂线共线点也构成垂直1 _ Y); Perp.
Col.
apply L形垂直转垂直于 in H24.
Perp.
assert(Perp X B0 B B0).
apply(垂线共线点也构成垂直1 _ Y); Perp.
assert(Perp B0 O B B0).
apply (垂线共线点也构成垂直1 _ X); Perp.
ColR.
apply L形垂直转垂直于 in H26.
Perp.

apply L形垂直于转直角.
induction(两点重合的决定性 X C0).
subst X.
assert(Perp C0 O C C0).
apply(垂线共线点也构成垂直1 _ Y); Perp.
Col.
apply L形垂直转垂直于 in H24.
Perp.
assert(Perp X C0 C C0).
apply(垂线共线点也构成垂直1 _ Y); Perp.
assert(Perp C0 O C C0).
apply (垂线共线点也构成垂直1 _ X); Perp.
ColR.
apply L形垂直转垂直于 in H26.
Perp.

induction(两点重合的决定性 C' B0).
subst B0.
assert(B' = C0).
apply 中间性蕴含共线1 in H24.
apply (l6_21_两线交点的唯一性 C' O C C0); Col.
assert(Par C B' C C0).
apply(l12_9 C B' C C0 X Y); Perp; Cop.

induction H25.
apply False_ind.
apply H25.
exists C.
split; Col.
分离合取式.
Col.
intro.
apply H1.
ColR.
intro.
subst C0.
apply H1.
ColR.
apply(cop_perp2__col C C0 B' X Y); Perp.
exists C0.
left.
split; Col.
subst C0.
Between.

assert(B' <> C0).
intro.
subst C0.
apply H25.
apply (l6_21_两线交点的唯一性 B' O B B0); Col.
intro.
subst B0.
Col.
assert(Par B C' B B0).
apply(l12_9 B C' B B0 X Y); Perp; Cop.

induction H26.
apply False_ind.
apply H26.
exists B.
split; Col.
分离合取式.
Col.

assert(Col C C0 B').
apply(cop_perp2__col C C0 B' X Y); Perp.
exists C0.
left.
split; Col.
assert(Col B B0 C').
apply(cop_perp2__col B B0 C' X Y); Perp.
exists B0.
left.
split; Col.

apply(per13_preserves_bet_inv B' O C' C0 B0); Between.
Col.

apply L形垂直于转直角.
induction(两点重合的决定性 X C0).
subst X.
assert(Perp C0 O C B').
apply (垂线共线点也构成垂直1 _ Y); Perp.
Col.
assert(Perp B' C0 C0 O).
apply(垂线共线点也构成垂直1 _ C); Perp.
Col.
apply 垂直的交换性 in H30.
apply L形垂直转垂直于 in H30.
Perp.

assert(Perp X C0 C B').
apply(垂线共线点也构成垂直1 _ Y); Perp.
assert(Perp C0 O C B').
apply (垂线共线点也构成垂直1 _ X); Perp.
ColR.
assert(Perp B' C0 C0 O).
apply(垂线共线点也构成垂直1 _ C); Perp.
Col.
apply 垂直的交换性 in H32.
apply L形垂直转垂直于 in H32.
Perp.


apply L形垂直于转直角.

assert(Perp C' B0 X Y).
apply (垂线共线点也构成垂直1 _ B); Perp.
Col.
induction (两点重合的决定性 X O).
subst X.
assert(Perp O B0 B0 C').
apply(垂线共线点也构成垂直1 _ Y);Perp.
apply 垂直的交换性 in H30.
apply L形垂直转垂直于 in H30.
Perp.
 
assert(Perp X O C' B0).
apply(垂线共线点也构成垂直1 _ Y); Perp.
Col.
assert(Perp O B0 B0 C').
apply(垂线共线点也构成垂直1 _ X); Perp.
ColR.
apply 垂直的交换性 in H32.
apply L形垂直转垂直于 in H32.
Perp.

Qed.


Lemma is_image_perp_in : forall A A' X Y, A <> A' -> X <> Y -> 对称 A A' X Y ->
  exists P, 垂直于 P A A' X Y.
Proof.
intros.
unfold 对称 in H.
induction H1.
分离合取式.
unfold 严格对称 in H2.
分离合取式.
ex_and H2 P.
induction H3.
exists P.

apply 垂直于的对称性.
apply 垂直于的右交换性.
apply(l8_14_2_1b_bis_交点是垂点 X Y A' A P); Col.
assert_cols.
Col.
subst A'.
tauto.
分离合取式.
contradiction.
Qed.

Lemma perp_inter_perp_in_n
     : forall A B C D : Tpoint,
       Perp A B C D ->
       exists P : Tpoint, Col A B P /\ Col C D P /\ 垂直于 P A B C D.
Proof.
intros.
assert(A <> B /\ C <> D).
apply 垂直推出不重合 in H.
tauto.
分离合取式.
induction(共线的决定性 A B C).
exists C.
split; Col.
split; Col.
apply(l8_14_2_1b_bis_交点是垂点 A B C D C); Col.

assert(HH:=l8_18_过一点垂线之垂点的存在性 A B C H2).
ex_and HH P.
exists P.
assert(Col C D P).
apply(cop_perp2__col C D P A B); Perp.
exists P.
left.
split; Col.
split; Col.
split; Col.
apply(l8_14_2_1b_bis_交点是垂点 A B C D P); Col.
Qed.

Lemma perp2_perp_in : forall A B C D O, Perp2 A B C D O -> ~Col O A B /\ ~Col O C D ->
    exists P, exists Q, Col A B P /\ Col C D Q /\ Col O P Q /\ 垂直于 P O P A B /\ 垂直于 Q O Q C D.
  Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H1 Y.
    assert(X <> Y).
      apply 垂直推出不重合1 in H2.
      auto.
    assert(HH:= perp_inter_perp_in_n X Y A B H2).
    ex_and HH P.
    assert(HH:= perp_inter_perp_in_n X Y C D H3).
    ex_and HH Q.
    exists P.
    exists Q.
    split; auto.
    split; auto.
    split.
      apply (共线的传递性4 X Y); Col.
    split.
      induction(两点重合的决定性 X O).
        subst X.
        apply 垂直于的对称性.
        apply(垂线共线点也构成垂直_垂直于 A B O Y P P).
          intro.
          subst P.
          apply H.
          Col.
          Col.
        apply 垂直于的对称性.
        auto.
      assert(垂直于 P A B X O).
        apply(垂线共线点也构成垂直_垂直于 A B X Y O P H11).
          Col.
        apply 垂直于的对称性.
        auto.
      apply 垂直于的右交换性 in H12.
      eapply (垂线共线点也构成垂直_垂直于 _ _ _ _ P) in H12 .
        apply 垂直于的对称性.
        auto.
        intro.
        subst P.
        apply H.
        Col.
      ColR.
    induction(两点重合的决定性 X O).
      subst X.
      apply 垂直于的对称性.
      apply(垂线共线点也构成垂直_垂直于 C D O Y Q Q).
        intro.
        subst Q.
        apply H0.
        Col.
        Col.
      apply 垂直于的对称性.
      auto.
    assert(垂直于 Q C D X O).
      apply(垂线共线点也构成垂直_垂直于 C D X Y O Q H11).
        Col.
      apply 垂直于的对称性.
      auto.
    apply 垂直于的右交换性 in H12.
    eapply (垂线共线点也构成垂直_垂直于 _ _ _ _ Q) in H12 .
      apply 垂直于的对称性.
      auto.
      intro.
      subst Q.
      apply H0.
      Col.
    ColR.
Qed.


Lemma l13_8 : forall O P Q U V, U <> O -> V <> O -> Col O P Q -> Col O U V
    -> Per P U O -> Per Q V O -> (Out O P Q <-> Out O U V).
Proof.
    intros.
    induction(两点重合的决定性 P U).
      subst P.
      assert(Col Q V O).
        ColR.
      assert(HH:= l8_9_直角三点共线则必有两点重合 Q V O H4 H5).
      induction HH.
        subst Q.
        tauto.
      subst V.
      tauto.
    assert(Q <> V).
      intro.
      subst Q.
      assert(HH:= 成直角三点不共线 P U O H5 H H3).
      apply HH.
      ColR.
split.
intro.
unfold Out in H7.
分离合取式.
induction H9.

assert(HH:= per23_preserves_bet O P Q U V).
repeat split; auto.
left.
apply(per23_preserves_bet O P Q U V); auto.
Perp.
Perp.
repeat split; auto.
right.
apply(per23_preserves_bet O Q P V U); Col.
Perp.
Perp.

intro.
unfold Out in H7.
分离合取式.

repeat split.
intro.
subst P.
apply ABA直角则A与B重合 in H3.
contradiction.
intro.
subst Q.
apply ABA直角则A与B重合 in H4.
contradiction.
induction H9.
left.
apply(per23_preserves_bet_inv O P Q U V); Perp.
right.
apply(per23_preserves_bet_inv O Q P V U); Perp.
Col.
Qed.

Lemma perp_in_rewrite : forall A B C D P, 垂直于 P A B C D ->
                                          垂直于 P A P P C \/
                                          垂直于 P A P P D \/
                                          垂直于 P B P P C \/
                                          垂直于 P B P P D.
Proof.
intros.
assert(HH:= 垂点是交点 A B C D P H).
分离合取式.
induction(两点重合的决定性 A P);
induction(两点重合的决定性 C P).
subst A .
subst C.
right;right;right.
Perp.
subst A.
right; right; left.
apply 垂直于的右交换性.
assert(HP:=垂线共线点也构成垂直_垂直于 P B C D P P H3 H1 H).
Perp.
subst C.
right; left.
apply 垂直于的对称性.
apply(垂线共线点也构成垂直_垂直于 P D A B P P H2 H0).
Perp.
left.
assert(HP:= 垂线共线点也构成垂直_垂直于 A B C D P P H3 H1 H).
apply 垂直于的对称性.
apply 垂直于的左交换性.
apply(垂线共线点也构成垂直_垂直于 C P A B P P H2 H0).
Perp.
Qed.

Lemma perp_out_acute : forall A B C C', Out B A C' -> Perp A B C C' -> 为锐角 A B C.
Proof.
intros.
assert(A <> B /\ C' <> B).
apply out_distinct.
assumption.
分离合取式.

assert(Perp B C' C C').
apply(垂线共线点也构成垂直1 _ A); Perp.
Col.
assert(Per C C' B).
apply L形垂直于转直角.
apply 垂直的对称性 in H3.
apply 垂直的左交换性 in H3.
apply L形垂直转垂直于 in H3.
apply 垂直于的交换性.
assumption.
assert(为锐角 C' C B /\ 为锐角 C' B C).
apply(l11_43_非锐角三角形两小内角为锐角 C' C B).

统计不重合点.
auto.
auto.
left.
assumption.
分离合取式.

assert(C <> B).
intro.
subst C.
apply ABA直角则A与B重合 in H4.
subst C'.
auto.

apply acute_out2__acute with C' C; auto.
apply out_trivial; auto.
Qed.

Lemma perp_bet_obtuse : forall A B C C', B <> C' -> Perp A B C C' -> Bet A B C' -> 为钝角 A B C.
Proof.
intros.
assert(HPO:=perp_out_acute).
assert(HBO:=acute_中间性平角为钝角).
assert(Col A B C').
apply 中间性蕴含共线1 in H1.
Col.
assert(为锐角 C' B C).
apply (HPO _ _ _ C').
apply out_trivial; auto.
apply 垂直的左交换性.
apply(垂线共线点也构成垂直1 _ A); Perp.
Col.
apply (HBO C').
Between.
intro.
subst B.
apply 垂直推出不重合 in H0.
tauto.
assumption.
Qed.

End L13_1.

Section L13_1_2D.

Context `{T2D:Tarski_2D}.

Lemma perp_in2__col : forall A B A' B' X Y P, 垂直于 P A B X Y -> 垂直于 P A' B' X Y  ->
  Col A B A'.
Proof.
intros A B A' B' X Y P.
apply cop4_perp_in2__col; apply all_coplanar.
Qed.

Lemma perp2_trans : forall A B C D E F P, Perp2 A B C D P -> Perp2 C D E F P -> Perp2 A B E F P.
Proof.
    intros.
    unfold Perp2 in *.
    ex_and H X.
    ex_and H1 Y.
    ex_and H0 X'.
    ex_and H3 Y'.
    assert(Par X Y X' Y').
      apply (l12_9_2D _ _ _ _ C D); Perp.
    exists X.
    exists Y.
    assert(Col X X' Y').
      induction H5.
        unfold 严格平行 in H5.
        分离合取式.
        apply False_ind.
        apply H6.
        exists P.
        split; Col.
      分离合取式.
      auto.
    assert(Col Y X' Y').
      induction H5.
        unfold 严格平行 in H5.
        分离合取式.
        apply False_ind.
        apply H7.
        exists P.
        split; Col.
      分离合取式.
      auto.
    repeat split; auto.
    assert(X <> Y).
      apply 垂直推出不重合1 in H1.
      assert(X' <> Y').
        apply 垂直推出不重合1 in H3.
        auto.
      auto.
    induction(两点重合的决定性 X Y').
      subst Y'.
      apply (垂线共线点也构成垂直1 _ X').
        auto.
        Perp.
      ColR.
    apply (垂线共线点也构成垂直1 _ Y').
      auto.
      apply 垂直的左交换性.
      apply(垂线共线点也构成垂直1 _ X').
        auto.
        Perp.
      ColR.
    apply par_symmetry in H5.
    induction H5.
      unfold 严格平行 in H5.
      分离合取式.
      apply False_ind.
      apply H10.
      exists P.
      split; Col.
    分离合取式.
    Col.
Qed.

Lemma perp2_par : forall A B C D O, Perp2 A B C D O -> Par A B C D.
Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H0 Y.
    apply (l12_9_2D _ _ _ _ X Y).
      Perp.
    Perp.
Qed.

End L13_1_2D.