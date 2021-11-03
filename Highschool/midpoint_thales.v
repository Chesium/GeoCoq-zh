(* Exercise done by David Braun under the supervision of Nicolas Magaud, cleaned up by Julien Narboux. *)

Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Section T_42.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma midpoint_thales : forall O A B C : Tpoint,
   ~ Col A B C ->
   中点 O A B ->
   Cong O A O C ->
   Per A C B.
Proof.
intros.
Name X the midpoint of C and A.
assert (严格平行 O X B C)
 by perm_apply (triangle_mid_par_strict_cong_simp C B A O X).
assert(Per O X A)
 by (exists C;split;finish).
assert_diffs.
assert_cols.
assert(Hid2 : Perp O X C A)
 by perm_apply (直角加共线转L形垂直 O X A C).
assert (Perp B C C A).
 apply (cop_par_perp__perp O X B C C A);finish.
apply L形垂直转直角1;Perp.
Qed.

(* TODO cleanup *)

Lemma midpoint_thales_reci :
  forall a b c o: Tpoint,
   Per a c b ->
   中点 o a b ->
   Cong o a o b /\ Cong o b o c.
Proof.
intros.

induction (共线的决定性 a b c).

induction (l8_9_直角三点共线则必有两点重合 a c b H);
treat_equalities;assert_congs_perm;try split;finish.
assert_diffs.
(* Demonstration Cong o a o b *)
assert_congs_perm.
split.
Cong.
(* Demonstration Cong o b o c *)
assert(Hmid := 中点的存在性 a c).
(* Soit x Le milieu de a c *)
destruct Hmid.
(* Demonstration o x parallele à b c *)
assert(Hpar : Par c b x o).
apply (triangle_mid_par c b a o x);finish.
(* On doit effectuer Le changement d'angle perpendiculaire en appliquant par_perp_perp*)
(* Demonstration du sous but Perp pour appliquer par_perp_perp *)
assert(Hper : Perp c b c a)
 by (apply 垂直的左交换性;apply 直角转L形垂直;Perp).
(* Demonstratin du sous but Cop pour appliquer par_perp_perp *)
assert(Hcop : 共面 x o c a) by Cop.
(* Application de par_perp_perp *)
assert(HH := cop_par_perp__perp c b x o c a Hpar Hper).
assert(Hper2 : Perp c x o x).
  apply (垂线共线点也构成垂直1 c a o x x).
  assert_diffs.
  finish.
  Perp.
  Col.
(*Transformation de Perp c x o x en Per *)
assert_diffs.
assert (Per o x c)
 by (apply L形垂直转直角2;Perp).

(* Depliage de Per pour obtenir Cong o b o c *)
unfold Per in H8.
destruct H8.
spliter.
apply M是AB中点则M是BA中点 in H8.
assert(HmidU := 中点组的唯一性2 a x0 x c H2 H8).
subst.
unfold 中点 in H2.
spliter.
eCong.
Qed.

End T_42.
