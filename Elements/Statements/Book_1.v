(** * Euclid's Elements

  Book I
*)

(**
  We present in this file the formalization of the propositions
  from the first book of Euclid's Elements.
  Our formal proofs are not formalizations of
  Euclid's proofs; they can be very different
  because we do not use the axiom system of Euclid.
  The proofs are performed in the context of Tarski's axioms.
  We have proven the bi-interpretability with
  the corresponding Hilbert's axioms,
  hence the user can choose his favorite axiom system.

  The english version of the propositions is imported from the
  xml version of Euclid's Elements provided by the Perseus project:
  http://www.perseus.tufts.edu/hopper/text?doc=Perseus:text:1999.01.0086 .
  The GeoGebra figures have been created by Gianluigi Trivia:
  https://www.geogebra.org/m/qScJxt8s .

  Hence, this file is licenced under
  https://creativecommons.org/licenses/by-sa/3.0/us/
  in addition to LGPL 3.0.
*)

(** #
<script type="text/javascript" src="https://www.geogebra.org/scripts/deployggb.js"></script>
<script type="text/javascript">
    var applet1 = new GGBApplet({material_id: "r4D6cEeh"}, true);
    var applet2 = new GGBApplet({material_id: "ERFPd6Gx"}, true);
    var applet3 = new GGBApplet({material_id: "rXcJrHZh"}, true);
    var applet4 = new GGBApplet({material_id: "uEgvYkrc"}, true);
    var applet5 = new GGBApplet({material_id: "tn33uzyD"}, true);
    var applet6 = new GGBApplet({material_id: "VCsxJRRH"}, true);
    var applet7 = new GGBApplet({material_id: "d5dMrQXs"}, true);
    var applet8 = new GGBApplet({material_id: "aQqPfsMd"}, true);
    var applet9 = new GGBApplet({material_id: "RjFXAa9f"}, true);
    var applet10 = new GGBApplet({material_id: "mmRErFqd"}, true);
    var applet11 = new GGBApplet({material_id: "pMdtFxq6"}, true);
    var applet12 = new GGBApplet({material_id: "z5AkXe6N"}, true);
    var applet13 = new GGBApplet({material_id: "ZAHjwcyc"}, true);
    var applet14 = new GGBApplet({material_id: "UKg84dFT"}, true);
    var applet15 = new GGBApplet({material_id: "bnjUjQ9X"}, true);
    var applet16 = new GGBApplet({material_id: "Gg6rHEs3"}, true);
    var applet17 = new GGBApplet({material_id: "npxkCJpC"}, true);
    var applet18 = new GGBApplet({material_id: "VFYgBjGh"}, true);
    var applet19 = new GGBApplet({material_id: "AfKPEzb7"}, true);
    var applet20 = new GGBApplet({material_id: "fH6japew"}, true);
    var applet21 = new GGBApplet({material_id: "rXrbmX4t"}, true);
    var applet22 = new GGBApplet({material_id: "vc4qEQeN"}, true);
    var applet23 = new GGBApplet({material_id: "bThxPU7Q"}, true);
    var applet24 = new GGBApplet({material_id: "Tuz27uFN"}, true);
    var applet25 = new GGBApplet({material_id: "WwqvjYpu"}, true);
    var applet26 = new GGBApplet({material_id: "JUMQJ7pm"}, true);
    var applet27 = new GGBApplet({material_id: "bVZjmJwk"}, true);
    var applet28 = new GGBApplet({material_id: "zsQmywaj"}, true);
    var applet29 = new GGBApplet({material_id: "DhjHHgP5"}, true);
    var applet30 = new GGBApplet({material_id: "bKxnmXBq"}, true);
    var applet31 = new GGBApplet({material_id: "FfT7t9Cu"}, true);
    var applet32 = new GGBApplet({material_id: "mcBCaz8R"}, true);
    var applet33 = new GGBApplet({material_id: "k48aN5wj"}, true);
    var applet34 = new GGBApplet({material_id: "KgPuPTfy"}, true);
    var applet35 = new GGBApplet({material_id: "C7YJBaaB"}, true);
    var applet36 = new GGBApplet({material_id: "gdesjdZD"}, true);
    var applet37 = new GGBApplet({material_id: "TNp5dZa6"}, true);
    var applet38 = new GGBApplet({material_id: "B4FWM9g7"}, true);
    var applet39 = new GGBApplet({material_id: "jHyHD9q7"}, true);
    var applet40 = new GGBApplet({material_id: "W5SANQJp"}, true);
    var applet41 = new GGBApplet({material_id: "ZQtgFvAM"}, true);
    var applet42 = new GGBApplet({material_id: "UQYRQX7w"}, true);
    var applet43 = new GGBApplet({material_id: "anfyFSKf"}, true);
    var applet44 = new GGBApplet({material_id: "y6tFXckE"}, true);
    var applet45 = new GGBApplet({material_id: "vJQkwr7r"}, true);
    var applet46 = new GGBApplet({material_id: "GnrYvWx3"}, true);
    var applet47 = new GGBApplet({material_id: "tdxHWEBA"}, true);
    var applet48 = new GGBApplet({material_id: "T4HcNAgy"}, true);

    window.onload = function() {
        applet1.inject('applet_container1', 'preferHTML5');
        applet2.inject('applet_container2', 'preferHTML5');
        applet3.inject('applet_container3', 'preferHTML5');
        applet4.inject('applet_container4', 'preferHTML5');
        applet5.inject('applet_container5', 'preferHTML5');
        applet6.inject('applet_container6', 'preferHTML5');
        applet7.inject('applet_container7', 'preferHTML5');
        applet8.inject('applet_container8', 'preferHTML5');
        applet9.inject('applet_container9', 'preferHTML5');
        applet10.inject('applet_container10', 'preferHTML5');
        applet11.inject('applet_container11', 'preferHTML5');
        applet12.inject('applet_container12', 'preferHTML5');
        applet13.inject('applet_container13', 'preferHTML5');
        applet14.inject('applet_container14', 'preferHTML5');
        applet15.inject('applet_container15', 'preferHTML5');
        applet16.inject('applet_container16', 'preferHTML5');
        applet17.inject('applet_container17', 'preferHTML5');
        applet18.inject('applet_container18', 'preferHTML5');
        applet19.inject('applet_container19', 'preferHTML5');
        applet20.inject('applet_container20', 'preferHTML5');
        applet21.inject('applet_container21', 'preferHTML5');
        applet22.inject('applet_container22', 'preferHTML5');
        applet23.inject('applet_container23', 'preferHTML5');
        applet24.inject('applet_container24', 'preferHTML5');
        applet25.inject('applet_container25', 'preferHTML5');
        applet26.inject('applet_container26', 'preferHTML5');
        applet27.inject('applet_container27', 'preferHTML5');
        applet28.inject('applet_container28', 'preferHTML5');
        applet29.inject('applet_container29', 'preferHTML5');
        applet30.inject('applet_container30', 'preferHTML5');
        applet31.inject('applet_container31', 'preferHTML5');
        applet32.inject('applet_container32', 'preferHTML5');
        applet33.inject('applet_container33', 'preferHTML5');
        applet34.inject('applet_container34', 'preferHTML5');
        applet35.inject('applet_container35', 'preferHTML5');
        applet36.inject('applet_container36', 'preferHTML5');
        applet37.inject('applet_container37', 'preferHTML5');
        applet38.inject('applet_container38', 'preferHTML5');
        applet39.inject('applet_container39', 'preferHTML5');
        applet40.inject('applet_container40', 'preferHTML5');
        applet41.inject('applet_container41', 'preferHTML5');
        applet42.inject('applet_container42', 'preferHTML5');
        applet43.inject('applet_container43', 'preferHTML5');
        applet44.inject('applet_container44', 'preferHTML5');
        applet45.inject('applet_container45', 'preferHTML5');
        applet46.inject('applet_container46', 'preferHTML5');
        applet47.inject('applet_container47', 'preferHTML5');
        applet48.inject('applet_container48', 'preferHTML5');
    } </script>
# **)

Require Export GeoCoq.Meta_theory.Continuity.elementary_continuity_props.
Require Export GeoCoq.Tarski_dev.Ch16_coordinates_with_functions.

(** * Proposition 1
       On a given finite straight line to construct an 等边三角形 triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container1"></div> # **)


(** We proved this proposition in the context of euclidean geometry without any continuity axiom.
    It can also be proven more easily assuming a circle-circle intersection axiom,
    as Euclid implicitly did.
    Victor Pambuccian has shown that these hypotheses are minimal.
*)


Section Book_1_prop_1_euclidean.

Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.

Lemma prop_1_euclidean :
  forall A B, exists C, Cong A B A C /\ Cong A B B C.
Proof.
  destruct exists_grid_spec as [SS [U1 [U2 Hgrid]]].
  apply (exists_等边三角形_triangle SS U1 U2 Hgrid).
Qed.

End Book_1_prop_1_euclidean.

Section Book_1_prop_1_circle_circle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma prop_1_circle_circle : circle_circle ->
  forall A B, exists C, Cong A B A C /\ Cong A B B C.
Proof.
  intros cc A B.
  apply circle_circle__circle_circle_bis in cc.
  destruct (cc A B B A A B) as [C [HC1 HC2]]; Circle.
  exists C.
  split;Cong.
Qed.

End Book_1_prop_1_circle_circle.


Section Book_1_part_2.

  (** For the next 27 propositions, we do not need the 5th axiom of Euclid,
      nor any continuity axioms, except for Proposition 22,
      which needs Circle/Circle intersection axiom.
  *)

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.
	    (** * Proposition 2
       To place at a given point (as an extremity) a straight line equal to a given straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container2"></div> # **)


Lemma prop_2 : forall A B C, exists L, Cong A L B C.
Proof.
  intros.
  apply 由一点构造等长线段.
Qed.


	    (** * Proposition 3
       Given two unequal straight lines, to cut off from the greater
       a straight line equal to the less. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container3"></div> # **)

Lemma prop_3 : forall A B C1 C2, Le C1 C2 A B -> exists E, Bet A E B /\ Cong C1 C2 A E.
Proof.
  auto.
Qed.


	    (** * Proposition 4
       If two triangles have the two sides equal to two sides respectively,
       and have the angles contained by the equal straight lines equal,
       they will also have the base equal to the base, the triangle will be equal to the triangle,
       and the remaining angles will be equal to the remaining angles respectively,
       namely those which the equal sides subtend.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container4"></div> # **)

Lemma prop_4 : forall A B C D E F, 等角 C A B F D E -> Cong A C D F -> Cong A B D E ->
  Cong C B F E /\ (C <> B -> 等角 A C B D F E /\ 等角 A B C D E F).
Proof.
  intros A B C D E F.
  apply l11_49.
Qed.


	    (** * Proposition 5
       In 等腰三角形 triangles the angles at the base are equal to one another, and,
       if the equal straight lines be produced further, the angles under the base
       will be equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container5"></div> # **)

Lemma prop_5_1 : forall A B C, A <> B -> B <> C -> Cong A B A C -> 等角 A B C A C B.
Proof.
  intros.
  apply l11_44_1_a_等腰三角形底角相等; auto.
Qed.

Lemma prop_5_2 : forall A B C F G, A <> B -> B <> C -> Cong A B A C ->
  Bet A B F -> B <> F -> Bet A C G -> C <> G ->
  等角 F B C G C B.
Proof.
  intros A B C F G.
  intros.
  apply l11_13 with A A; auto.
  apply l11_44_1_a_等腰三角形底角相等; auto.
Qed.


	    (** * Proposition 6
       If in a triangle two angles be equal to one another,
       the sides which subtend the equal angles will also be equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container6"></div> # **)

Lemma prop_6 : forall A B C, ~ Col A B C -> 等角 A B C A C B -> Cong A B A C.
Proof.
  intros A B C H.
  apply l11_44_1_三角形底角相等等价于等腰_b_底角相等的三角形是等腰三角形; Col.
Qed.


	    (** * Proposition 7
       Given two straight lines constructed on a straight line (from its extremities)
       and meeting in a point, there cannot be constructed on the same straight line
       (from its extremities), and on the same side of it, two other straight lines
       meeting in another point and equal to the former two respectively,
       namely each to that which has the same extremity with it.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container7"></div> # **)

Lemma prop_7 : forall A B C C', Cong A C A C' -> Cong B C B C' -> OS A B C C' -> C = C'.
Proof.
  intros A B C C' H等角 HCongB HOS.
  assert (HNCol := one_side_not_col123 A B C C' HOS).
  统计不重合点.
  destruct (l11_51 A B C A B C') as [H等角A [H等角B H等角C]]; Cong.
  apply (l6_21_两线交点的唯一性 A C B C); Col; apply out_col.
    apply (conga_os__out B); Side.
    apply (conga_os__out A); assumption.
Qed.


	    (** * Proposition 8
       If two triangles have the two sides equal to two sides respectively,
       and have also the base equal to the base, they will also have the angles equal
       which are contained by the equal straight lines. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container8"></div> # **)

Lemma prop_8 : forall A B C D E F, A <> B -> A <> C -> B <> C ->
       Cong A B D E -> Cong A C D F -> Cong B C E F ->
       等角 B A C E D F /\ 等角 A B C D E F /\ 等角 B C A E F D.
Proof.
  apply l11_51.
Qed.


	    (** * Proposition 9
       To bisect a given rectilineal angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container9"></div> # **)

Lemma prop_9 : forall A B C, A <> B -> A <> C ->
  exists F, 在角内 F B A C /\ 等角 F A B F A C.
Proof.
  intros.
  apply angle_bisector; auto.
Qed.


	    (** * Proposition 10
       To bisect a given finite straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container10"></div> # **)

Lemma prop_10 : forall A B, exists D, 中点 D A B.
Proof.
  apply 中点的存在性.
Qed.


	    (** * Proposition 11
       To draw a straight line at right angles to a given straight line from a given point on it.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container11"></div> # **)

Lemma prop_11 : forall A B C, A <> B -> Col A B C -> exists F, Perp C F A B.
Proof.
  intros.
  apply 垂点的存在性; assumption.
Qed.


	    (** * Proposition 12
       To a given infinite straight line, from a given point which is not on it,
       to draw a perpendicular straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container12"></div> # **)

Lemma prop_12 : forall A B C, ~ Col A B C -> exists H, Col A B H /\ Perp A B C H.
Proof.
  apply l8_18_过一点垂线之垂点的存在性.
Qed.


	    (** * Proposition 13
       If a straight line set up on a straight line make angles, it will make either
       two right angles or angles equal to two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container13"></div> # **)

Lemma prop_13 : forall A B C D P Q R, A <> B -> B <> C -> B <> D -> Bet C B D ->
  P <> Q -> Q <> R -> Per P Q R ->
  和角 C B A A B D C B D /\ 和角 P Q R P Q R C B D.
Proof.
  intros.
  split.
  - apply 中间性推出和角; auto.
  - apply 平角为两直角之和; auto.
Qed.


	    (** * Proposition 14
       If with any straight line, and at a point on it,
       two straight lines not lying on the same side
       make the adjacent angles equal to two right angles,
       the two straight lines will be in a straight line with one another. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container14"></div> # **)

Lemma prop_14 : forall A B C D P Q R S T U, TS A B C D -> Per P Q R ->
  和角 A B C A B D S T U -> 和角 P Q R P Q R S T U -> Bet C B D.
Proof.
  intros A B C D P Q R S T U HTS HP HSuma1 HSuma2.
  apply (零角的等角是零角 S T U).
    apply (两直角之和为平角 P Q R P Q R); assumption.
  apply (和角的唯一性 A B C A B D).
    assumption.
  apply 和角的左交换性, 异侧推出和角1, HTS.
Qed.


	    (** * Proposition 15
       If two straight lines cut one another, they make the vertical angles equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container15"></div> # **)

Lemma prop_15 : forall A B C D E, Bet A E B -> A <> E -> B <> E ->
  Bet C E D -> C <> E -> D <> E ->
  等角 A E C B E D.
Proof.
  intros.
  apply l11_14; auto.
Qed.


	    (** * Proposition 16
       In any triangle, if one of the sides is produced,
       the exterior angle is greater than either of the interior and opposite angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container16"></div> # **)

Lemma prop_16 : forall A B C D, ~ Col A B C -> Bet B C D -> C <> D ->
  角度小于 C A B A C D /\ 角度小于 C B A A C D.
Proof.
  intros.
  apply l11_41_三角形两内角小于另一外角; Col.
Qed.


	    (** * Proposition 17
       In any triangle two angles taken together in any manner are less than two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container17"></div> # **)

      (** Here, the fact that the two angles are less than two right angles is described with
          the 和角不大于平角 predicate, which means that they have a "sum at most straight", and the fact that
          their sum is not a straight line.
        *)

Lemma prop_17 : forall A B C P Q R, ~ Col A B C -> 和角 A B C B C A P Q R -> 
  和角不大于平角 A B C B C A /\ ~ Bet P Q R.
Proof.
  intros A B C P Q R HNCol HSuma.
  split.
  - 统计不重合点.
    apply 三角形两内角之和小于平角_BC; auto.
  - intro HBet.
    apply HNCol, 共线与和角推共线 with P Q R; Col.
Qed.


	    (** * Proposition 18
       In any triangle the greater side subtends the greater angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container18"></div> # **)

Lemma prop_18 : forall A B C, ~ Col A B C -> Lt A B A C -> Lt B C A C ->
  角度小于 B C A A B C /\ 角度小于 C A B A B C.
Proof.
  intros.
  split.
  - apply 角度小于的左交换性, l11_44_2_a_三角形长边对小角; Col.
  - apply 角度小于的右交换性, l11_44_2_a_三角形长边对小角.
      Col.
    apply 长度小于的交换性; assumption.
Qed.


	    (** * Proposition 19
       In any triangle the greater angle is subtended by the greater side.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container19"></div> # **)

Lemma prop_19 : forall A B C, ~ Col A B C -> 角度小于 B C A A B C -> 角度小于 C A B A B C ->
  Lt A B A C /\ Lt B C A C.
Proof.
  intros.
  split.
  - apply l11_44_2_b_三角形小角对长边.
      Col.
    apply 角度小于的左交换性; assumption.
  - apply 长度小于的交换性, l11_44_2_b_三角形小角对长边.
      Col.
    apply 角度小于的右交换性; assumption.
Qed.


	    (** * Proposition 20
       In any triangle two sides taken together in any manner are greater than the remaining one.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container20"></div> # **)

Lemma prop_20 : forall A B C P Q, ~ Bet B A C -> 长度之和 A B A C P Q -> Lt B C P Q.
Proof.
  intros A B C P Q HNBet HSum.
  destruct (由一点往一方向构造等长线段 B A A C) as [D [HBet HCong]].
  apply (等长保持小于关系 B C B D); Cong.
    apply triangle_strict_inequality with A; Cong.
  apply (长度之和的唯一性 A B A C); trivial.
  exists B, A, D; repeat split; Cong.
Qed.


	    (** * Proposition 21
       If on one of the sides of a triangle, from its extremities,
       there be constructed two straight lines meeting within the triangle,
       the straight lines so constructed will be less than the remaining two sides of the triangle,
       but will contain a greater angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container21"></div> # **)

Lemma prop_21_1 : forall A B C D, OS A B C D -> OS B C A D -> OS A C B D -> 角度小于 B A C B D C.
Proof.
  apply os3__lta.
Qed.

Lemma prop_21_2 : forall A B C D A1 A2 D1 D2, OS A B C D -> OS B C A D -> OS A C B D ->
  长度之和 A B A C A1 A2 -> 长度之和 D B D C D1 D2 -> Lt D1 D2 A1 A2.
Proof.
  intros A B C D A1 A2 D1 D2; intros.
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D; assumption).
  destruct (os2__inangle A B C D) as [HAB [HCB [HDB [E [HBet [Heq|HOut]]]]]]; Side.
    subst; exfalso; apply HNCol; ColR.
  统计不重合点.
  assert (A <> E) by (intro; subst E; apply (one_side_not_col124 A B C D); Col).
  assert (C <> E) by (intro; subst E; apply (one_side_not_col124 B C A D); Col).
  assert (D <> E) by (intro; subst E; apply (one_side_not_col124 A C B D); Col).
  assert (Bet B D E).
    apply out2__bet; [apply l6_6, HOut|].
    apply col_one_side_out with A; Col.
    apply invert_one_side, col_one_side with C; Col.
  destruct (长度之和的存在性 E B E C) as [P [Q]].
  apply 长度小于的传递性 with P Q.
  - destruct (长度之和的存在性 E C E D) as [R [S]].
    apply 长度一偏序一全序则和长保持全序 with D B D C D B R S; Le.
      apply prop_20 with E; Sums.
      intro; apply HNCol; ColR.
    apply 长度之和的结合律1 with E D E C E B; Sums.
  - destruct (长度之和的存在性 A B A E) as [R [S]].
    apply 长度一全序一偏序则和长保持全序 with E B E C R S E C; Le.
      apply prop_20 with A; Sums.
      intro; apply HNCol; ColR.
    apply 长度之和的结合律2 with A B A E A C; Sums.
Qed.


	    (** * Proposition 22
       Out of three straight lines, which are equal to three given straight lines,
       to construct a triangle:
       thus it is necessary that two of the straight lines taken together in any manner
       should be greater than the remaining one (cf. [I. 20]).
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container22"></div> # **)

      (** This needs Circle/Circle intersection axiom *)

Lemma prop_22 : circle_circle -> forall A1 A2 B1 B2 C1 C2 A1' A2' B1' B2' C1' C2',
  长度之和 A1 A2 B1 B2 C1' C2' -> 长度之和 A1 A2 C1 C2 B1' B2' -> 长度之和 B1 B2 C1 C2 A1' A2' ->
  Le C1 C2 C1' C2' -> Le B1 B2 B1' B2' -> Le A1 A2 A1' A2' ->
  exists F G K, Cong F G A1 A2 /\ Cong F K B1 B2 /\ Cong G K C1 C2.
Proof.
  intro cc.
  apply circle_circle__circle_circle_bis in cc.
  apply (circle_circle_bis__euclid_22 cc).
Qed.


	    (** * Proposition 23
       On a given straight line and at a point on it to construct
       a rectilineal angle equal to a given rectilineal angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container23"></div> # **)

Lemma prop_23 : forall A B C D E, A <> B -> C <> D -> C <> E ->
  exists F, 等角 D C E B A F.
Proof.
  intros.
  apply 给定角一边可作出等角; auto.
Qed.


	    (** * Proposition 24
       If two triangles have the two sides equal to two sides respectively,
       but have the one of the angles contained by the equal straight lines greater than the other,
       they will also have the base greater than the base.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container24"></div> # **)

Lemma prop_24 : forall A B C D E F, Cong A B D E -> Cong A C D F -> 角度小于 F D E C A B ->
  Lt E F B C.
Proof.
  apply t18_18.
Qed.


	    (** * Proposition 25
       If two triangles have the two sides equal to two sides respectively,
       but have the base greater than the base, they will also have
       the one of the angles contained by the equal straight lines greater than the other.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container25"></div> # **)

Lemma prop_25 : forall A B C D E F, A <> B -> A <> C ->
  Cong A B D E -> Cong A C D F -> Lt E F B C ->
  角度小于 F D E C A B.
Proof.
  apply t18_19.
Qed.


	    (** * Proposition 26
       If two triangles have the two angles equal to two angles respectively,
       and one side equal to one side, namely, either the side adjoining the equal angles,
       or that subtending one of the equal angles, they will also have the remaining sides
       equal to the remaining sides and the remaining angle to the remaining angle. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container26"></div> # **)

Lemma prop_26_1 : forall A B C D E F, ~ Col A B C ->
       等角 B A C E D F -> 等角 A B C D E F -> Cong A B D E ->
       Cong A C D F /\ Cong B C E F /\ 等角 A C B D F E.
Proof.
  apply l11_50_1.
Qed.

Lemma prop_26_2 : forall A B C D E F, ~ Col A B C ->
       等角 B C A E F D -> 等角 A B C D E F -> Cong A B D E ->
       Cong A C D F /\ Cong B C E F /\ 等角 C A B F D E.
Proof.
  apply l11_50_2.
Qed.


	    (** * Proposition 27
       If a straight line falling on two straight lines
       make the alternate angles equal to one another,
       the straight lines will be parallel to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container27"></div> # **)

Lemma prop_27 : forall A D E F, TS E F A D -> 等角 A E F D F E -> Par E A F D.
Proof.
  intros A D E F.
  apply l12_21_b.
Qed.


	    (** * Proposition 28
       If a straight line falling on two straight lines
       make the exterior angle equal to the interior and opposite angle on the same side,
       or the interior angles on the same side equal to two right angles,
       the straight lines will be parallel to one another. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container28"></div> # **)

Lemma prop_28_1 : forall B D E G H, Out E G H -> OS E G B D -> 等角 B G E D H E ->
  Par G B H D.
Proof.
  intros B D E G H.
  apply l12_22_b.
Qed.

Lemma prop_28_2 : forall A C G H P Q R, OS G H A C -> 和角 A G H G H C P Q R -> Bet P Q R ->
  Par A G C H.
Proof.
  intros A C G H P Q R HOS H和角 HBet.
  destruct (由一点往一方向构造等长线段 C H C H) as [D [HBet1 HCong]].
  apply par_comm.
  统计不重合点.
  apply par_col_par with D; Col.
  apply l12_21_b.
  - apply l9_8_2 with C; Side.
    assert (HNCol := one_side_not_col124 G H A C HOS).
    repeat split; Col.
      intro; apply HNCol; ColR.
    exists H; Col.
  - apply suppa2__conga123 with G H C.
      apply 和角为平角则为补角 with P Q R; assumption.
      split; auto; exists C; split; [Between|等角].
Qed.

End Book_1_part_2.

(** The following propositions are valid only in Euclidean geometry,
    except for Proposition 31, which is valid in neutral geometry.
*)

Section Book_1_part_3.


Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.

	    (** * Proposition 29
       A straight line falling on parallel straight lines makes
       the alternate angles equal to one another,
       the exterior angle equal to the interior and opposite angle,
       and the interior angles on the same side equal to two right angles. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container29"></div> # **)

Lemma prop_29_1 : forall A D G H, TS G H A D -> Par G A H D -> 等角 A G H D H G.
Proof.
  intros A D G H.
  apply l12_21_a.
Qed.

Lemma prop_29_2 : forall B D E G H, Out E G H -> OS E G B D -> Par G B H D ->
  等角 B G E D H E.
Proof.
  intros B D E G H.
  apply l12_22_a.
Qed.

Lemma prop_29_3 : forall A C G H P Q R, OS G H A C -> Par A G H C -> 和角 A G H G H C P Q R ->
  Bet P Q R.
Proof.
  intros A C G H P Q R HOS HPar.
  apply (补角和为平角).
  apply alternate_interior__consecutive_interior; trivial.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.


	    (** * Proposition 30
       Straight lines parallel to the same straight line are also parallel to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container30"></div> # **)

Lemma prop_30 : forall A B C D E F, Par A B C D -> Par C D E F ->
   Par A B E F.
Proof.
  apply par_trans.
Qed.

End Book_1_part_3.


Section Book_1_part_4.
	    (** * Proposition 31
       Through a given point to draw a straight line parallel to a given straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container31"></div> # **)

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma prop_31 : forall A B C, B <> C -> exists E, Par B C A E.
Proof.
  intros A B C.
  apply parallel_existence1.
Qed.

End Book_1_part_4.

Section Book_1_part_5.

Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.
	    (** * Proposition 32
       In any triangle, if one of the sides be produced,
       the exterior angle is equal to the two interior and opposite angles,
       and the three interior angles of the triangle are equal to two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container32"></div> # **)

Lemma prop_32_1 : forall A B C D E F, 三角形内角和 A B C D E F -> Bet D E F.
Proof.
  apply alternate_interior__triangle.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.

Lemma prop_32_2 : forall A B C D, A <> B -> B <> C -> A <> C -> Bet B C D -> C <> D ->
  和角 C A B A B C A C D.
Proof.
  intros A B C D HAB HBC HAC HBet HAD.
  destruct (三角形内角和的存在性 C A B) as [P [Q [R HTri]]]; auto.
  assert (Bet P Q R) by (apply (prop_32_1 C A B), HTri).
  destruct HTri as [S [T [U [HSuma1 H和角2]]]].
  apply 等角保持和角性质 with C A B A B C S T U; try (apply 同角相等); auto.
  统计不重合点.
  assert (H等角 : 等角 B C D P Q R) by (apply 成中间性三点组的角相等; auto).
  assert (H和角' : 和角 A C D B C A P Q R).
    apply 等角保持和角性质 with A C D B C A B C D; 等角.
    apply 和角的对称性, 中间性推出和角; auto.
  apply 和角推原角唯一性 with B C A P Q R; trivial;
    apply 和角为平角推和角不大于平角 with P Q R; assumption.
Qed.


	    (** * Proposition 33
       The straight lines joining at the extremities
       equal and parallel straight lines which are in the same directions
       are themselves also equal and parallel.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container33"></div> # **)

Lemma prop_33 : forall A B C D,
 TS B C A D -> Par A B C D -> Cong A B C D ->
 Cong A C B D /\ Par A C B D.
Proof.
  intros A B C D HTS HPAR HC.
  assert (HPara:平行四边形 B A C D) by (left;split;finish).
  destruct (plg_cong B A C D HPara).
  统计不重合点.
  destruct (plg_par B A C D); auto.
  split; [Cong|Par].
Qed.

	    (** * Proposition 34
       In parallelogrammic areas the opposite sides and angles are equal to one another,
       and the diameter bisects the areas.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container34"></div> # **)

Lemma prop_34_1 : forall A B D C,
  A <> B /\ A <> D /\ B <> D ->
  平行四边形 A B D C -> (等角 A B D D C A /\ 等角 B D C C A B) /\ (Cong A B D C /\ Cong A C B D).
Proof.
  intros; split.
  - apply plg_conga; auto.
  - apply plg_cong; auto.
Qed.

	    (** * Proposition 35
       平行四边形s which are on the same base and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container35"></div> # **)
	  
	    (** * Proposition 36
       平行四边形s which are on equal bases and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container36"></div> # **)
	  
	    (** * Proposition 37
       Triangles which are on the same base and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container37"></div> # **)
	  
	    (** * Proposition 38
       Triangles which are on equal bases and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container38"></div> # **)
	  
	    (** * Proposition 39
       Equal triangles which are on the same base and on the same side are also in the same parallels.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container39"></div> # **)
	  
	    (** * Proposition 40
       Equal triangles which are on equal bases and on the same side are also in the same parallels.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container40"></div> # **)
	  
	    (** * Proposition 41
       If a parallelogram have the same base with a triangle and be in the same parallels,
       the parallelogram is double of the triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container41"></div> # **)
	  
	    (** * Proposition 42
       To construct, in a given rectilineal angle, a parallelogram equal to a given triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container42"></div> # **)
	  
	    (** * Proposition 43
       In any parallelogram the complements of the parallelograms about the diameter
       are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container43"></div> # **)
	  
	    (** * Proposition 44
       To a given straight line to apply, in a given rectilineal angle,
       a parallelogram equal to a given triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container44"></div> # **)
	  
	    (** * Proposition 45
       To construct, in a given rectilineal angle, a parallelogram equal to a given rectilineal figure.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container45"></div> # **)
	  
	    (** * Proposition 46
       On a given straight line to describe a square.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container46"></div> # **)

Lemma prop_46 : forall A B, A<>B -> exists E D, 正方形 A B E D.
Proof.
  exact exists_square.
Qed.


	    (** * Proposition 47
       In right-angled triangles the square on the side subtending the right angle
       is equal to the squares on the sides containing the right angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container47"></div> # **)

      (** This is the Pythagoras theorem.
          Pythagoras is tied to the parallel postulate, in the sense
          that we need the parallel postulate to express it.
          Here, we have a statement based on the geometric definition
          of addition and multiplication as predicates. 
      *)

Lemma prop_47 :
     forall O E E' A B C AC BC AB AC2 BC2 AB2,
       O <> E ->
       Per B A C ->
       Length O E E' A B AB ->
       Length O E E' A C AC ->
       Length O E E' B C BC ->
       Prod O E E' AC AC AC2 ->
       Prod O E E' BC BC BC2 ->
       Prod O E E' AB AB AB2 ->
       Sum O E E' AB2 AC2 BC2.
Proof.
  intros O E E' A B C AC BC AB AC2 BC2 AB2.
  intros.
  apply pythagoras with B C A AB AC BC; trivial; apply length_sym; assumption.
Qed.


	    (** * Proposition 48
       If in a triangle the square on one of the sides be equal
       to the squares on the remaining two sides of the triangle,
       the angle contained by the remaining two sides of the triangle is right.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container48"></div> # **)


End Book_1_part_5.