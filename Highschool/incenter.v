Require Export GeoCoq.Highschool.bisector.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section InCenter.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.


Definition 内心 I A B C :=
 ~ Col A B C /\ 等角 B A I I A C /\ 等角 A B I I B C /\ 等角 A C I I C B.

(** Proof of the existence of the incenter of a triangle. *)

Lemma 内心的存在性 : forall A B C, ~ Col A B C -> exists I, 内心 I A B C.
Proof.
intros A B C HNCOL.
(*----construction---*)
统计不重合点.
destruct (角平分线的存在性 A B C) as [IB HCONA];auto.
destruct (角平分线的存在性 B A C) as [IA HCONB];auto.
destruct HCONA as [HBINANGLE HCONGAA].
destruct HCONB as [HAINANGLE HCONGBB].
destruct HBINANGLE as [HBAB [HBCB [HBIBB HBEXI]]].
destruct HAINANGLE as [HABA [HACA [HAIAA HAEXI]]].
destruct HAEXI as [XA [HXABET HXAO]].
destruct HBEXI as [XB [HXBBET HXBO]].
assert (HXEXISTS : exists X : Tpoint, Bet XB X B /\ Bet XA X A).
apply (帕施公理 A B C XB XA);assumption.
destruct HXEXISTS as [X [HXBET1 HXBET2]].
destruct HXAO as [HXAEQ | HXAOUT].
subst.
elim HNCOL;ColR.
destruct HXBO as [HXBEQ | HXBOUT].
subst.
elim HNCOL;ColR.
assert (XA <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);Col).
assert (XB <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);elim HNCOL;Col).
assert (~ Col A B X) by (intro;elim HNCOL;col_with_conga).
assert (~ Col A C X) by (intro;assert (Col C A B) by (col_with_conga);elim HNCOL;Col).
assert (~ Col B C X) by (intro;assert (Col C B A) by (col_with_conga);elim HNCOL;Col).
destruct (l8_18_过一点垂线之垂点的存在性 A B X) as [HC [HCC1 HCC2]];auto.
destruct (l8_18_过一点垂线之垂点的存在性 A C X) as [HB [HBC1 HBC2]];auto.
destruct (l8_18_过一点垂线之垂点的存在性 B C X) as [HA [HAC1 HAC2]];auto.
exists X.
unfold 内心.
split.
assumption.
(*-prove some conclusions which will be required later for many times.-*)
assert (Out A X IA) by (assert (Out A X XA) by (统计不重合点;apply (bet_out A X XA);Between);
apply (l6_7 A X XA IA);auto).
assert (Out B X IB) by (assert (Out B X XB) by (统计不重合点;apply (bet_out B X XB);Between);
apply (l6_7 B X XB IB);auto).
assert (等角 B A X X A C).
{ apply (l11_10 B A IA IA A C B X X C);Out.
}
assert (等角 A B X X B C).
{ apply (l11_10 A B IB IB B C A X X C);Out.
}
assert (共面 C A B X) by (exists XB; left; split; Col).
assert (Cong X HB X HC) by (apply (角平分线定理 C A B X HB HC);Col;Perp;等角).
assert (Cong X HC X HA) by (apply (角平分线定理 A B C X HC HA);Col;Cop).
assert (Cong X HB X HA) by (apply (等长的传递性 X HB X HC X HA);auto).
assert (等角 A C X X C B).
{ 
 apply (角平分线定理的逆定理 A C B X HB HA);Col;Perp.
 assert (在角内 X A B C).
 repeat split;auto.
 exists XB.
 split;auto.
 right.
 apply (l6_6 B X XB);auto.
 apply (bet_out B X XB);auto.
 Between.
 assert (在角内 X B A C).
 统计不重合点.
 repeat split;auto.
 exists XA.
 split;auto.
 right.
 apply (l6_6 A X XA);auto.
 apply (bet_out A X XA);auto.
 Between.
 apply (os2__inangle A C B X).
 apply (one_side_symmetry C A X B).
 apply (角内点和一端点在角另一边同侧 C A B X);Col.
 apply (l11_24_在角内的对称性 X B A C);auto.
 apply (one_side_symmetry C B X A).
 apply (角内点和一端点在角另一边同侧 C B A X);Col.
 apply (l11_24_在角内的对称性 X A B C);auto.
}
split;auto.
Qed.

Lemma 等价内心ACB : forall A B C I, 内心 I A B C -> 内心 I A C B.
Proof.
unfold 内心.
intros A B C I HIABC.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
Col.
split;等角.
Qed.

Lemma 等价内心BAC : forall A B C I, 内心 I A B C -> 内心 I B A C.
Proof.
unfold 内心.
intros A B C I HIABC.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
intro;Col.
split;auto.
split;等角.
Qed.

Lemma 等价内心BCA : forall A B C I, 内心 I A B C -> 内心 I B C A.
Proof.
intros A B C I HIABC.
apply (等价内心ACB B A C I).
apply (等价内心BAC A B C I);auto.
Qed.

Lemma 等价内心CAB : forall A B C I, 内心 I A B C -> 内心 I C A B.
Proof.
intros A B C I HIABC.
apply (等价内心BAC A C B I).
apply (等价内心ACB A B C I);auto.
Qed.

Lemma 等价内心CBA : forall A B C I, 内心 I A B C -> 内心 I C B A.
Proof.
intros A B C I HIABC.
apply (等价内心CAB B A C I).
apply (等价内心BAC A B C I);auto.
Qed.

Lemma 一点是否为内心的决定性 : forall A B C I, 内心 I A B C \/ ~ 内心 I A B C.
Proof.
intros A B C I.
unfold 内心.
destruct (共线的决定性 A B C) as [HCOL | HNCOL].
right.
intro HCOLIN.
destruct HCOLIN as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
elim HNCOL;auto.
destruct (conga_dec B A I I A C) as [HAC | HANC].
destruct (conga_dec A B I I B C) as [HBC | HBNC].
destruct (conga_dec A C I I C B) as [HCC | HCNC].
left;split;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HCNC;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HBNC;等角.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HANC;auto.
Qed.

End InCenter.