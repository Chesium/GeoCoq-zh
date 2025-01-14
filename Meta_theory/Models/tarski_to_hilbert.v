Require Import Morphisms.
Require Import GeoCoq.Axioms.hilbert_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Import GeoCoq.Meta_theory.Parallel_postulates.SPP_ID.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_3.
Require Import GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.

Require Export GeoCoq.Utils.triples.

Section T.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** We need a notion of line. *)

Definition Line := @Couple Tpoint.
Definition Lin := build_couple Tpoint.

Definition IncidentL := fun A l => Col A (P1 l) (P2 l).

(** * Group I Incidence *)

(** For every pair of distinct points there is a line containing them. *)

Lemma axiom_line_existence : forall A B, A<>B -> exists l, IncidentL A l /\ IncidentL B l.
Proof.
intros.
exists (Lin A B H).
unfold IncidentL.
intuition.
Qed.

(** We need a notion of equality over lines. *)

Definition 谓词等长 : relation Line := fun l m => forall X, IncidentL X l <-> IncidentL X m.

Infix "=l=" := 谓词等长 (at level 70):type_scope.

Lemma incident_eq : forall A B l, forall H : A<>B,
 IncidentL A l -> IncidentL B l ->
 (Lin A B H) =l= l.
Proof.
intros.
unfold 谓词等长.
intros.
unfold IncidentL in *.
replace (P1 (Lin A B H)) with A; trivial.
replace (P2 (Lin A B H)) with B; trivial.
split;intro.
assert (T:=Cond l).
elim (两点重合的决定性 X B); intro.
subst X.
auto.
assert (Col (P1 l) A B).
apply 共线的传递性2 with (P2 l); Col.
assert (Col (P2 l) A B).
apply (共线的传递性3 (P1 l)); Col.
apply (共线的传递性4 A B); Col.

assert (U:=Cond l).
apply (共线的传递性4 (P1 l) (P2 l)); Col.
Qed.

(** Our equality is an equivalence relation. *)

Lemma eq_transitivity : forall l m n, l =l= m -> m =l= n -> l =l= n.
Proof.
unfold 谓词等长,IncidentL.
intros.
assert (T:=H X).
assert (V:= H0 X).
split;intro;intuition.
Qed.

Lemma eq_reflexivity : forall l, l =l= l.
Proof.
intros.
unfold 谓词等长.
intuition.
Qed.

Lemma eq_symmetry : forall l m, l =l= m -> m =l= l.
Proof.
unfold 谓词等长.
intros.
assert (T:=H X).
intuition.
Qed.

Instance 谓词等长_Equiv : Equivalence 谓词等长.
Proof.
split.
unfold Reflexive.
apply eq_reflexivity.
unfold Symmetric.
apply eq_symmetry.
unfold Transitive.
apply eq_transitivity.
Defined.


(** The equality is compatible with IncidentL *)

Lemma eq_incident : forall A l m, l =l= m ->
 (IncidentL A l <-> IncidentL A m).
Proof.
intros.
split;intros;
unfold 谓词等长 in *;
assert (T:= H A);
intuition.
Qed.

Instance incident_Proper (A:Tpoint) :
Proper (谓词等长 ==>iff) (IncidentL A).
Proof.
intros a b H .
apply eq_incident.
assumption.
Defined.

Lemma axiom_Incid_morphism :
 forall P l m, IncidentL P l -> 谓词等长 l m -> IncidentL P m.
Proof.
intros.
destruct (eq_incident P l m H0).
intuition.
Qed.

Lemma axiom_Incid_dec : forall P l, IncidentL P l \/ ~IncidentL P l.
Proof.
intros.
unfold IncidentL.
apply 共线的决定性.
Qed.

(** There is only one line going through two points. *)

Lemma axiom_line_uniqueness : forall A B l m, A <> B ->
 IncidentL A l -> IncidentL B l -> IncidentL A m -> IncidentL B m ->
 l =l= m.
Proof.
intros.
assert ((Lin A B H) =l= l).
eapply incident_eq;assumption.
assert ((Lin A B H) =l= m).
eapply incident_eq;assumption.
rewrite <- H4.
assumption.
Qed.

(** Every line contains at least two points. *)

Lemma axiom_two_points_on_line : forall l,
  { A : Tpoint & { B | IncidentL B l /\ IncidentL A l /\ A <> B}}.
Proof.
intros.
exists (P1 l).
exists (P2 l).
unfold IncidentL.
repeat split;Col.
exact (Cond l).
Qed.

(** Definition of the collinearity predicate.
 We say that three points are collinear if they belongs to the same line. *)

Definition Col_H := fun A B C =>
  exists l, IncidentL A l /\ IncidentL B l /\ IncidentL C l.

(** We show that the notion of collinearity we just defined is equivalent to the
 notion of collinearity of Tarski. *)

Lemma cols_coincide_1 : forall A B C, Col_H A B C -> Col A B C.
Proof.
intros.
unfold Col_H in H.
DecompExAnd H l.
unfold IncidentL in *.
assert (T:=Cond l).
apply (共线的传递性4 (P1 l) (P2 l)); Col.
Qed.

Lemma cols_coincide_2 : forall A B C, Col A B C -> Col_H A B C.
Proof.
intros.
unfold Col_H.
elim (两点重合的决定性 A B); intro.
subst B.
elim (两点重合的决定性 A C); intro.
subst C.
assert (exists B, A<>B).
eapply 每个点均有不同点.
DecompEx H0 B.
exists (Lin A B H1).
unfold IncidentL;intuition.
exists (Lin A C H0).
unfold IncidentL;intuition.
exists (Lin A B H0).
unfold IncidentL;intuition.
Qed.

Lemma cols_coincide : forall A B C, Col A B C <-> Col_H A B C.
Proof.
intros.
split.
apply cols_coincide_2.
apply cols_coincide_1.
Qed.

Lemma ncols_coincide : forall A B C, ~ Col A B C <-> ~ Col_H A B C.
Proof.
intros.
split; intros HNCol HCol; apply HNCol, cols_coincide, HCol.
Qed.

(** There exists three non collinear points. *)

Lemma 防降维公理' : PA <> PB /\ PB <> PC /\ PA <> PC /\ ~ Col_H PA PB PC.
Proof.
assert (HNCol : ~ Col PA PB PC) by (apply 防降维公理).
统计不重合点.
apply ncols_coincide in HNCol.
repeat split; auto.
Qed.

(** We need a notion of plane. *)

Record Plane := Plan {M1; M2; M3; NCol : ~ Col_H M1 M2 M3}.

Definition IncidentP := fun A p => 共面 (M1 p) (M2 p) (M3 p) A.

(** For every triplet of non collinear points there is a plane containing them. *)

Lemma axiom_plane_existence : forall A B C, ~ Col_H A B C ->
  exists p, IncidentP A p /\ IncidentP B p /\ IncidentP C p.
Proof.
intros A B C HNCol.
exists (Plan A B C HNCol).
unfold IncidentP; simpl; repeat split; Cop.
Qed.

(** We need a notion of equality over planes. *)

Definition EqP : relation Plane := fun p q => forall X, IncidentP X p <-> IncidentP X q.

Infix "=p=" := EqP (at level 70):type_scope.

Lemma incidentp_eqp : forall A B C p, forall H : ~ Col_H A B C,
 IncidentP A p -> IncidentP B p -> IncidentP C p ->
 (Plan A B C H) =p= p.
Proof.
intros A B C p HNCol HA HB HC X.
unfold IncidentP in *; simpl.
assert (Hp := NCol p).
apply ncols_coincide in Hp.
apply ncols_coincide in HNCol.
split; intro; [apply coplanar_pseudo_trans with A B C; trivial|];
apply coplanar_pseudo_trans with (M1 p) (M2 p) (M3 p); Cop.
Qed.

(** Our equality is an equivalence relation. *)

Lemma eqp_transitivity : forall p q r, p =p= q -> q =p= r -> p =p= r.
Proof.
intros p q r H1 H2 X.
rewrite (H1 X); apply H2.
Qed.

Lemma eqp_reflexivity : forall p, p =p= p.
Proof.
intros.
unfold EqP.
intuition.
Qed.

Lemma eqp_symmetry : forall p q, p =p= q -> q =p= p.
Proof.
unfold EqP.
intros p q H X.
assert (T := H X).
intuition.
Qed.

Instance EqP_Equiv : Equivalence EqP.
Proof.
split.
unfold Reflexive.
apply eqp_reflexivity.
unfold Symmetric.
apply eqp_symmetry.
unfold Transitive.
apply eqp_transitivity.
Defined.


(** The equality is compatible with IncidentL *)

Lemma eqp_incidentp : forall A p q, p =p= q ->
 (IncidentP A p <-> IncidentP A q).
Proof.
intros A p q H.
exact (H A).
Qed.

Instance incidentp_Proper (A:Tpoint) :
Proper (EqP ==>iff) (IncidentP A).
Proof.
intros a b H.
apply eqp_incidentp.
assumption.
Defined.

Lemma axiom_Incidp_morphism :
 forall M p q, IncidentP M p -> EqP p q -> IncidentP M q.
Proof.
intros M p q Hp H.
destruct (eqp_incidentp M p q H).
intuition.
Qed.

Lemma axiom_Incidp_dec : forall M p, IncidentP M p \/ ~ IncidentP M p.
Proof.
intros.
apply cop_dec.
Qed.

(** There is only one plane going through three non collinear points. *)

Lemma axiom_plane_uniqueness : forall A B C p q, ~ Col_H A B C ->
 IncidentP A p -> IncidentP B p -> IncidentP C p ->
 IncidentP A q -> IncidentP B q -> IncidentP C q ->
 p =p= q.
Proof.
intros A B C p q H; intros.
assert (Heq : (Plan A B C H) =p= p).
apply incidentp_eqp;assumption.
assert ((Plan A B C H) =p= q).
apply incidentp_eqp;assumption.
rewrite <- Heq.
assumption.
Qed.

(** Every plane contains at least one point. *)

Lemma axiom_one_point_on_plane : forall p,
  { A | IncidentP A p }.
Proof.
intro p.
exists (M1 p).
unfold IncidentP; Cop.
Qed.

(** Definition of a line belonging to a plane.
  We say that a line belongs to a plane if every point of the line belongs to the plane. *)

Definition  IncidentLP := fun l p => forall A, IncidentL A l -> IncidentP A p.

(** If two distinct points of a line belong to a plane, then the line belongs to the plane. *)

Lemma axiom_line_on_plane : forall A B l p, A <> B ->
 IncidentL A l -> IncidentL B l -> IncidentP A p -> IncidentP B p ->
 IncidentLP l p.
Proof.
intros A B l p HAB HAl HBl HAp HBp X HXl.
destruct (ex_ncol_cop (M1 p) (M2 p) (M3 p) A B HAB) as [C [HCp HNCol]].
apply ncols_coincide in HNCol.
assert (Heq : (Plan A B C HNCol) =p= p).
apply incidentp_eqp; auto.
rewrite <- Heq.
unfold IncidentP; simpl.
exists X; left; split.
apply cols_coincide_1; exists l; repeat split; assumption.
Col.
Qed.

(** * Group II Order *)

(** Definition of the Between predicate of Hilbert.
    Note that it is different from the Between of Tarski.
    The Between of Hilbert is strict. *)

Definition Between_H := fun A B C =>
  Bet A B C /\ A <> B /\ B <> C /\ A <> C.

Lemma axiom_between_col :
 forall A B C, Between_H A B C -> Col_H A B C.
Proof.
intros.
unfold Col_H, Between_H in *.
DecompAndAll.
exists (Lin A B H2).
unfold IncidentL.
intuition.
Qed.

Lemma axiom_between_diff :
 forall A B C, Between_H A B C -> A<>C.
Proof.
intros.
unfold Between_H in *.
intuition.
Qed.

(** If B is between A and C, it is also between C and A. *)

Lemma axiom_between_comm : forall A B C, Between_H A B C -> Between_H C B A.
Proof.
unfold Between_H in |- *.
intros.
intuition.
Qed.



Lemma axiom_between_out :
 forall A B, A <> B -> exists C, Between_H A B C.
Proof.
intros.
prolong A B C A B.
exists C.
unfold Between_H.
repeat split;
auto;
intro;
treat_equalities;
tauto.
Qed.

Lemma axiom_between_only_one :
 forall A B C,
 Between_H A B C -> ~ Between_H B C A.
Proof.
unfold Between_H in |- *.
intros.
intro;
分离合取式.
assert (B=C) by
 (apply (双中间性推出点重合 B C A);Between).
solve [intuition].
Qed.

Lemma between_one : forall A B C,
 A<>B -> A<>C -> B<>C -> Col A B C ->
 Between_H A B C \/ Between_H B C A \/ Between_H B A C.
Proof.
intros.
unfold Col, Between_H in *.
destruct H2 as [|[|]]; [left|right..]; Between.
Qed.


Lemma axiom_between_one : forall A B C,
 A<>B -> A<>C -> B<>C -> Col_H A B C ->
 Between_H A B C \/ Between_H B C A \/ Between_H B A C.
Proof.
intros.
apply between_one;try assumption.
apply cols_coincide_1.
assumption.
Qed.

(** Axiom of Pasch, (Hilbert version). *)

(** First we define a predicate which means that the line l intersects the segment AB. *)

Definition cut := fun l A B =>
  ~ IncidentL A l /\ ~ IncidentL B l /\ exists I, IncidentL I l /\ Between_H A I B.

(** We show that this definition is equivalent to the predicate TS of Tarski. *)

Lemma cut_two_sides : forall l A B, cut l A B <-> TS (P1 l) (P2 l) A B.
Proof.
intros.
unfold cut.
unfold TS.
split.
intros.
分离合取式.
repeat split; intuition.
ex_and H1 T.
exists T.
unfold IncidentL in H1.
unfold Between_H in *.
intuition.

intros.
分离合取式.
ex_and H1 T.
unfold IncidentL.
repeat split; try assumption.
exists T.
split.
assumption.
unfold Between_H.
repeat split.
assumption.
intro.
subst.
contradiction.
intro.
subst.
contradiction.
intro.
treat_equalities.
contradiction.
Qed.

Lemma cop_plane_aux : forall A B C D, 共面 A B C D -> A <> B ->
  exists p, IncidentP A p /\ IncidentP B p /\ IncidentP C p /\ IncidentP D p.
Proof.
  intros A B C D HCop HAB.
  destruct (共线的决定性 A B C) as [|HNCol]; [destruct (共线的决定性 A B D) as [|HNCol]|].
  - destruct (两点不重合则存在不共线的点 A B HAB) as [E HNCol].
    apply ncols_coincide in HNCol.
    exists (Plan A B E HNCol).
    unfold IncidentP; simpl; repeat split; Cop.
  - apply ncols_coincide in HNCol.
    exists (Plan A B D HNCol).
    unfold IncidentP; simpl; repeat split; Cop.
  - apply ncols_coincide in HNCol.
    exists (Plan A B C HNCol).
    unfold IncidentP; simpl; repeat split; Cop.
Qed.

Lemma cop_plane : forall A B C D, 共面 A B C D ->
  exists p, IncidentP A p /\ IncidentP B p /\ IncidentP C p /\ IncidentP D p.
Proof.
  intros A B C D HCop.
  destruct (两点重合的决定性 A B) as [|HAB]; [destruct (两点重合的决定性 A C);
    [destruct (两点重合的决定性 A D)|]|].
  - destruct (每个点均有不同点 D) as [E].
    destruct (cop_plane_aux D E E E) as [p []]; Cop.
    subst; exists p; repeat split; assumption.
  - destruct (cop_plane_aux A D B C) as [p]; Cop.
    分离合取式; exists p; repeat split; assumption.
  - destruct (cop_plane_aux A C B D) as [p]; Cop.
    分离合取式; exists p; repeat split; assumption.
  - apply (cop_plane_aux A B C D HCop HAB).
Qed.

Lemma plane_cop: forall A B C D p,
  IncidentP A p -> IncidentP B p -> IncidentP C p -> IncidentP D p -> 共面 A B C D.
Proof.
  unfold IncidentP.
  intros A B C D p HA HB HC HD.
  assert (HNCol := NCol p).
  apply ncols_coincide in HNCol.
  apply coplanar_pseudo_trans with (M1 p) (M2 p) (M3 p); assumption.
Qed.

Lemma axiom_pasch : forall A B C l p, ~ Col_H A B C ->
 IncidentP A p -> IncidentP B p -> IncidentP C p -> IncidentLP l p -> ~ IncidentL C l ->
 cut l A B -> cut l A C \/ cut l B C.
Proof.
intros.
apply cut_two_sides in H5.
assert(~Col A B C).
apply ncols_coincide.
assumption.

assert(HH:=H5).
unfold TS in HH.
分离合取式.

unfold IncidentL in H4.
assert (HCop : 共面 (P1 l) (P2 l) A C).
apply plane_cop with p; trivial; apply H3; unfold IncidentL; simpl; Col.

assert(HH:= cop__one_or_two_sides (P1 l)(P2 l) A C HCop H7 H4).

induction HH.
left.
apply <-cut_two_sides.
assumption.
right.
apply <-cut_two_sides.
apply l9_2.
eapply l9_8_2.
apply H5.
assumption.
Qed.

Lemma Incid_line :
 forall P A B l, A<>B ->
 IncidentL A l -> IncidentL B l -> Col P A B -> IncidentL P l.
Proof.
intros.
unfold IncidentL in *.
destruct l as [C D HCD].
simpl in *.
ColR.
Qed.




(** * Group III Congruence *)

(** The cong predicate of Hilbert is the same as the one of Tarski: *)

Definition outH := fun P A B => Between_H P A B \/ Between_H P B A \/ (P <> A /\ A = B).

Lemma out_outH : forall P A B, Out P A B -> outH P A B.
unfold Out.
unfold outH.
intros.
分离合取式.
induction H1.

induction (两点重合的决定性 A B).
right; right.
split; auto.
left.
unfold Between_H.
repeat split; auto.


induction (两点重合的决定性 A B).
right; right.
split; auto.
right; left.
unfold Between_H.
repeat split; auto.
Qed.

Lemma axiom_hcong_1_existence : forall A B A' P l,
  A <> B -> A' <> P ->
  IncidentL A' l -> IncidentL P l ->
  exists B', IncidentL B' l /\ outH A' P B' /\ Cong A' B' A B.
Proof.
intros; destruct (l6_11_existence A' A B P) as [B' [HOut HCong]]; auto.
exists B'; repeat split; try apply out_outH, l6_6; auto; unfold IncidentL in *.
destruct l; simpl in *; ColR.
Qed.

Lemma axiom_hcong_1_uniqueness :
 forall A B l M A' B' A'' B'', A <> B -> IncidentL M l ->
  IncidentL A' l -> IncidentL B' l ->
  IncidentL A'' l -> IncidentL B'' l ->
  Between_H A' M B' -> Cong M A' A B ->
  Cong M B' A B -> Between_H A'' M B'' ->
  Cong M A'' A B -> Cong M B'' A B ->
  (A' = A'' /\ B' = B'') \/ (A' = B'' /\ B' = A'').
Proof.
unfold Between_H.
unfold IncidentL.
intros.
分离合取式.

assert(A' <> M /\ A'' <> M /\ B' <> M /\ B'' <> M /\ A' <> B' /\ A'' <> B'').
repeat split; intro; treat_equalities; tauto.
分离合取式.

induction(out_dec M A' A'').
left.
assert(A' = A'').
apply (l6_11_uniqueness M A B A''); try assumption.
apply out_trivial.
assumption.

split.
assumption.
subst A''.

apply (l6_11_uniqueness M A B B''); try assumption.

unfold Out.
repeat split; try assumption.
eapply l5_2.
apply H18.
assumption.
assumption.
apply out_trivial.
assumption.

right.
apply not_out_bet in H23.

assert(A' = B'').
apply (l6_11_uniqueness M A B A'); try assumption.
apply out_trivial.
assumption.

unfold Out.
repeat split; try assumption.

eapply l5_2.
apply H18.
assumption.
apply 中间性的对称性.
assumption.

split.
assumption.

subst B''.
apply (l6_11_uniqueness M A B B'); try assumption.
apply out_trivial.
assumption.
unfold Out.
repeat split; try assumption.
eapply l5_2.
apply H20.
apply 中间性的对称性.
assumption.
assumption.
eapply 共线的传递性4.
apply (Cond l).
Col.
Col.
Col.
Qed.

(** As a remark we also prove another version of this axiom as formalized in Isabelle by
Phil Scott. *)

Definition same_side_scott := fun E A B => E <> A /\ E <> B /\ Col_H E A B /\ ~ Between_H A E B.

Remark axiom_hcong_scott:
 forall P Q A C, A <> C -> P <> Q ->
  exists B, same_side_scott A B C  /\ Cong P Q A B.
Proof.
intros.
unfold same_side_scott.
assert (exists X : Tpoint, Out A X C /\ Cong A X P Q).
apply l6_11_existence;auto.
decompose [ex and] H1;clear H1.
exists x.
repeat split.
unfold Out in H3.
intuition.
unfold Out in H3.
intuition.
apply cols_coincide_2.
apply out_col;assumption.


unfold Out in H3.
unfold Between_H.
intro.
decompose [and] H3;clear H3.
decompose [and] H1;clear H1.
clear H8.
destruct H7.
assert (A = x).
eapply 双中间性推出点重合;eauto.
intuition.
assert (A = C).
eapply 双中间性推出点重合;eauto.
apply 中间性的对称性.
auto.
intuition.
Cong.
Qed.

(** We define when two segments do not intersect. *)

Definition disjoint := fun A B C D => ~ exists P, Between_H A P B /\ Between_H C P D.

(** Note that two disjoint segments may share one of their extremities. *)

Lemma col_disjoint_bet : forall A B C, Col_H A B C -> disjoint A B B C -> Bet A B C.
Proof.
intros.
apply cols_coincide_1 in H.
unfold disjoint in H0.

induction (两点重合的决定性 A B).
subst  B.
apply AAB中间性.
induction (两点重合的决定性 B C).
subst  C.
apply ABB中间性.

unfold Col in H.
induction H.
assumption.

induction H.
apply False_ind.
apply H0.
assert(exists M, 中点 M B C) by(apply 中点的存在性).
ex_and H3 M.
exists M.
unfold 中点 in H4.
分离合取式.
split.
unfold Between_H.
repeat split.
apply 中间性的对称性.
eapply 中间性的交换传递性2.
apply H3.
assumption.
intro.
treat_equalities.
(*
apply 中间性的对称性 in H.
apply 双中间性推出点重合 in H.
treat_equalities.
*)
tauto.
(*
apply 中间性的对称性.
assumption.
*)
intro.
treat_equalities.
tauto.
assumption.
unfold Between_H.
repeat split.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
assumption.

apply False_ind.
apply H0.
assert(exists M, 中点 M A B) by(apply 中点的存在性).
ex_and H3 M.
exists M.
unfold 中点 in H4.
分离合取式.
split.
unfold Between_H.
repeat split.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
assumption.

unfold Between_H.
repeat split.

eapply 中间性的交换传递性2.
apply 中间性的对称性.
apply H3.
apply 中间性的对称性.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
intuition.
assumption.
Qed.


Lemma axiom_hcong_3 : forall A B C A' B' C',
   Col_H A B C -> Col_H A' B' C' ->
  disjoint A B B C -> disjoint A' B' B' C' ->
  Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
intros.
assert(Bet A B C).
eapply col_disjoint_bet.
assumption.
assumption.

assert(Bet A' B' C').
eapply col_disjoint_bet.
assumption.
assumption.
eapply 两组连续三点分段等则全体等;eauto.
Qed.

Lemma exists_not_incident : forall A B : Tpoint, forall  HH : A <> B , exists C, ~ IncidentL C (Lin A B HH).
Proof.
intros.
unfold IncidentL.
assert(HC:=两点不重合则存在不共线的点 A B HH).
ex_and HC C.
exists C.
intro.
apply H.
simpl in H0.
Col.
Qed.

Definition same_side := fun A B l => exists P, cut l A P /\ cut l B P.

(** Same side predicate corresponds to OS of Tarski. *)

Lemma same_side_one_side : forall A B l, same_side A B l -> OS (P1 l) (P2 l) A B.
Proof.
unfold same_side.
intros.
destruct H as [P []].
apply cut_two_sides in H.
apply cut_two_sides in H0.
eapply l9_8_1.
apply H.
apply H0.
Qed.



Lemma one_side_same_side : forall A B l, OS (P1 l) (P2 l) A B -> same_side A B l.
Proof.
intros.
unfold same_side.
unfold OS in H.
destruct H as [P []].
exists P.
unfold cut.
unfold IncidentL.
unfold TS in H.
unfold TS in H0.
分离合取式.
repeat split; auto.
ex_and H4 T.
exists T.
unfold Between_H.
repeat split; auto.
intro.
subst T.
contradiction.
intro.
subst T.
contradiction.
intro.
subst P.
apply 中间性的同一律 in H5.
subst T.
contradiction.
ex_and H2 T.
exists T.
unfold Between_H.
repeat split; auto.
intro.
subst T.
contradiction.
intro.
subst T.
contradiction.
intro.
subst P.
apply 中间性的同一律 in H5.
subst T.
contradiction.
Qed.

Definition same_side' := fun A B X Y =>
  X <> Y /\ forall l, IncidentL X l -> IncidentL Y l -> same_side A B l.

Lemma OS_distinct : forall P Q A B,
  OS P Q A B -> P<>Q.
Proof.
intros.
apply one_side_not_col123 in H.
统计不重合点;assumption.
Qed.


Lemma OS_same_side' :
 forall P Q A B, OS P Q A B -> same_side' A B P Q.
Proof.
intros.
unfold same_side'.
intros.
split.
apply OS_distinct with A B;assumption.
intros.

apply  one_side_same_side.
destruct l.
unfold IncidentL in *.
simpl in *.
apply col2_os__os with P Q; try assumption; ColR.
Qed.

Lemma same_side_OS :
 forall P Q A B, same_side' P Q A B -> OS A B P Q.
Proof.
intros.
unfold same_side' in *.
destruct H.
destruct (axiom_line_existence A B H).
destruct H1.
assert (T:=H0 x H1 H2).
assert (U:=same_side_one_side P Q x T).
destruct x.
unfold IncidentL in *.
simpl in *.
apply col2_os__os with P1 P2;Col.
Qed.

(** This is equivalent to the out predicate of Tarski. *)

Lemma outH_out : forall P A B, outH P A B -> Out P A B.
Proof.
unfold outH.
unfold Out.
intros.
induction H.
unfold Between_H in H.
分离合取式.
repeat split; auto.
induction H.
unfold Between_H in H.
分离合取式.
repeat split; auto.
分离合取式.
repeat split.
auto.
subst B.
auto.
subst B.
left.
apply ABB中间性.
Qed.

(** The 2D version of the fourth congruence axiom **)

Lemma incident_col : forall M l, IncidentL M l -> Col M (P1 l)(P2 l).
Proof.
unfold IncidentL.
intros.
assumption.
Qed.

Lemma col_incident : forall M l, Col M (P1 l)(P2 l) -> IncidentL M l.
Proof.
unfold IncidentL.
intros.
assumption.
Qed.

Lemma Bet_Between_H : forall A B C,
 Bet A B C -> A<>B -> B<>C -> Between_H A B C.
Proof.
intros.
unfold Between_H.
repeat split;try assumption.
intro.
subst.
treat_equalities.
intuition.
Qed.

Lemma axiom_cong_5' : forall A B C A' B' C', ~ Col_H A B C -> ~ Col_H A' B' C' ->
           Cong A B A' B' -> Cong A C A' C' -> 等角 B A C B' A' C' -> 等角 A B C A' B' C'.
Proof.
intros A B C A' B' C'.
intros.
assert (T:=l11_49 B A C B' A' C').
assert (~ Col A B C).
intro.
apply cols_coincide_2 in H4.
intuition.
统计不重合点.
intuition.
Qed.


Lemma axiom_hcong_4_existence :  forall A B C O X P,
   ~ Col_H P O X -> ~ Col_H A B C ->
  exists Y, 等角 A B C X O Y  (* /\ ~Col O X Y *) /\ same_side' P Y O X.
Proof.
intros.
rewrite <- cols_coincide in H.
rewrite <- cols_coincide in H0.

assert(~Col X O P).
intro.
apply H.
Col.
assert(HH:=给定角一边可作出与给定点同侧一点构成等角_非平角 A B C X O P H0 H1).

ex_and HH Y.

exists Y.
split.
assumption.
apply OS_same_side'.
apply invert_one_side.
apply one_side_symmetry.
assumption.
Qed.

Lemma same_side_trans :
 forall A B C l,
  same_side A B l -> same_side B C l -> same_side A C l.
Proof.
intros.
apply one_side_same_side.
apply same_side_one_side in H.
apply same_side_one_side in H0.
eapply one_side_transitivity.
apply H.
assumption.
Qed.

Lemma same_side_sym :
 forall A B l,
  same_side A B l -> same_side B A l.
Proof.
intros.
apply one_side_same_side.
apply same_side_one_side in H.
apply one_side_symmetry.
assumption.
Qed.


Lemma axiom_hcong_4_uniqueness :
  forall A B C O P X Y Y', ~ Col_H P O X  -> ~ Col_H A B C -> 等角 A B C X O Y -> 等角 A B C X O Y' -> 
  same_side' P Y O X -> same_side' P Y' O X -> outH O Y Y'.
Proof.
intros.
rewrite <- cols_coincide in H.
rewrite <- cols_coincide in H0.
assert (T:等角 X O Y X O Y').
eapply 角等的传递性.
apply 等角的对称性.
apply H1.
assumption.

apply out_outH.
apply (conga_os__out X).
assumption.

apply same_side_OS in H3.
apply same_side_OS in H4.
apply invert_one_side.
apply one_side_transitivity with P.
apply one_side_symmetry.
assumption.
assumption.
Qed.

Lemma axiom_等角的交换性 : forall A B C,
 ~ Col_H A B C -> 等角 A B C C B A.
Proof.
intros.
rewrite <- cols_coincide in H.
统计不重合点.
apply 角ABC等于角CBA;auto.
Qed.

Lemma axiom_congaH_outH_congaH :
 forall A B C D E F A' C' D' F' : Tpoint,
  等角 A B C D E F ->
  Between_H B A A' \/ Between_H B A' A \/ B <> A /\ A = A' ->
  Between_H B C C' \/ Between_H B C' C \/ B <> C /\ C = C' ->
  Between_H E D D' \/ Between_H E D' D \/ E <> D /\ D = D' ->
  Between_H E F F' \/ Between_H E F' F \/ E <> F /\ F = F' ->
  等角 A' B C' D' E F'.
Proof.
intros.
apply l11_10 with A C D F; trivial; apply l6_6; apply outH_out; auto.
Qed.

Lemma axiom_conga_permlr:
forall A B C D E F : Tpoint, 等角 A B C D E F -> 等角 C B A F E D.
Proof.
apply Ch11_angles.等角的交换性.
Qed.

(*
Lemma axiom_inter_dec : forall l m,
  (exists P, IncidentL P l /\ IncidentL P m) \/ ~ (exists P, IncidentL P l /\ IncidentL P m).
Proof.
intros l m;
elim (inter_dec (P1 l) (P2 l) (P1 m) (P2 m));
intro; [left|right]; auto.
Qed.
*)

Lemma axiom_同角相等 : forall A B C, ~ Col_H A B C -> 等角 A B C A B C.
Proof.
intros A B C H.
apply Ch11_angles.同角相等; intro; subst; apply H; apply cols_coincide; Col.
Qed.

End T.

Section Tarski_neutral_to_Hilbert_neutral.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Instance Hilbert_neutral_follows_from_Tarski_neutral : Hilbert_neutral_dimensionless.
Proof.
exact (Build_Hilbert_neutral_dimensionless Tpoint Line Plane 谓词等长 谓词等长_Equiv EqP EqP_Equiv IncidentL
       IncidentP axiom_Incid_morphism axiom_Incid_dec axiom_Incidp_morphism axiom_Incidp_dec
       两点重合的决定性 axiom_line_existence axiom_line_uniqueness axiom_two_points_on_line PA
       PB PC 防降维公理' axiom_plane_existence axiom_one_point_on_plane axiom_plane_uniqueness
       axiom_line_on_plane Between_H axiom_between_diff axiom_between_col axiom_between_comm
       axiom_between_out axiom_between_only_one axiom_pasch Cong 等长的右交换性
       axiom_hcong_1_existence 等长的内传递性
        axiom_hcong_3 等角 axiom_同角相等 axiom_等角的交换性
       axiom_conga_permlr axiom_congaH_outH_congaH axiom_hcong_4_existence
       axiom_hcong_4_uniqueness axiom_cong_5').
Defined.

End Tarski_neutral_to_Hilbert_neutral.

Section Tarski_neutral_2D_to_Hilbert_neutral_2D.

Context `{T2D:Tarski_2D}.

Instance Hilbert_2D_follows_from_Tarski_2D : Hilbert_neutral_2D Hilbert_neutral_follows_from_Tarski_neutral.
Proof.
split.
intros A B C l HNCol HNCl Hcut.
apply axiom_pasch with (Plan A B C HNCol); trivial;
  unfold IncidentLP, IncidentP; intros; try (apply all_coplanar).
Defined.

End Tarski_neutral_2D_to_Hilbert_neutral_2D.

Section Tarski_neutral_3D_to_Hilbert_neutral_3D.

Context `{T3D:Tarski_3D}.

Lemma 三维防降维公理' : {A : Tpoint & {B : Tpoint & {C : Tpoint & {D |
  ~ exists p, IncidentP A p /\ IncidentP B p /\ IncidentP C p /\ IncidentP D p}}}}.
Proof.
exists S1, S2, S3, S4.
intros [p]; 分离合取式.
apply tarski_axioms.三维防降维公理, plane_cop with p; assumption.
Qed.

Instance Hilbert_3D_follows_from_Tarski_3D : Hilbert_neutral_3D Hilbert_neutral_follows_from_Tarski_neutral.
Proof.
destruct 三维防降维公理' as [A [B [C [D n]]]].
exists A B C D; [|assumption].
clear A B C D n.
intros A p q HAp HAq.
destruct p as [P1 P2 P3 HP].
destruct q as [Q1 Q2 Q3 HQ].
unfold IncidP in *; simpl in *; unfold IncidentP in *; simpl in *.
assert (pi : plane_intersection_axiom).
cut 三维防升维公理_axiom.
apply 三维防升维公理_equivalent_axioms; simpl; tauto.
unfold 三维防升维公理_axiom.
apply 三维防升维公理.
apply pi; assumption.
Defined.

End Tarski_neutral_3D_to_Hilbert_neutral_3D.

Section 塔斯基公理系统_欧几里得几何_to_Hilbert_Euclidean.

Context `{TE:塔斯基公理系统_欧几里得几何}.

(** * Group Parallels *)

Definition Para := fun l m =>
  (~ exists X, IncidentL X l /\ IncidentL X m) /\ exists p, IncidentLP l p /\ IncidentLP m p.

Lemma Para_Par : forall A B C D (HAB : A<>B) (HCD: C<>D),
 Para (Lin A B HAB) (Lin C D HCD) -> Par A B C D.
Proof.
unfold Para, IncidentL, Par, 严格平行; simpl.
intros.
destruct H as [HNI [p []]].
left.
repeat split;auto.
apply plane_cop with p; [apply H|apply H|apply H0..]; unfold IncidentL; simpl; Col.
Qed.

Lemma axiom_euclid_uniqueness :
  forall l P m1 m2,
  ~ IncidentL P l ->
   Para l m1 -> IncidentL P m1 ->
   Para l m2 -> IncidentL P m2 ->
   谓词等长 m1 m2.
Proof.
intros.
destruct l as [A B HAB].
destruct m1 as [C D HCD].
destruct m2 as [C' D' HCD'].
unfold IncidentL in *;simpl in *.
apply Para_Par in H0.
apply Para_Par in H2.
elim (tarski_s_euclid_implies_playfair euclid A B C D C' D' P H0 H1 H2 H3);intros.
apply axiom_line_uniqueness with C' D';
unfold IncidentL;simpl;Col.
Qed.

Instance Hilbert_euclidean_follows_from_塔斯基公理系统_欧几里得几何 :
  Hilbert_euclidean Hilbert_neutral_follows_from_Tarski_neutral.
Proof.
split.
apply axiom_euclid_uniqueness.
Defined.

Instance Hilbert_euclidean_ID_follows_from_塔斯基公理系统_欧几里得几何 :
  Hilbert_euclidean_ID Hilbert_euclidean_follows_from_塔斯基公理系统_欧几里得几何.
Proof.
split.
intros l m.
assert (ID : decidability_of_intersection).
apply strong_parallel_postulate_implies_inter_dec.
cut tarski_s_parallel_postulate.
apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis; simpl; tauto.
unfold tarski_s_parallel_postulate.
apply euclid.
destruct l as [L1 L2 HL].
destruct m as [M1 M2 HM].
simpl; unfold IncidentL; simpl.
apply ID.
Defined.

End 塔斯基公理系统_欧几里得几何_to_Hilbert_Euclidean.