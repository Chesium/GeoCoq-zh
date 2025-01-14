Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Tarski_dev.Annexes.half_angles.
Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.

Import circles.

Section Inscribed_angle.

Context `{TE:塔斯基公理系统_欧几里得几何}.

(** The sum of the angles of a triangle is the flat angle. *)

Lemma trisuma__bet : forall A B C D E F, 三角形内角和 A B C D E F -> Bet D E F.
Proof.
  apply alternate_interior__triangle.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.

Lemma bet__trisuma : forall A B C D E F, Bet D E F -> A <> B -> B <> C -> A <> C -> D <> E -> E <> F ->
  三角形内角和 A B C D E F.
Proof.
  intros A B C D E F HBet; intros.
  destruct (三角形内角和的存在性 A B C) as [P [Q [R HTri]]]; auto.
  apply 等角保持三角形内角和性质 with P Q R; trivial.
  assert (Hd := HTri).
  apply 三角形内角和推出不重合 in Hd; 分离合取式.
  apply 成中间性三点组的角相等; auto.
  apply (trisuma__bet A B C); trivial.
Qed.

Lemma right_saccheris : forall A B C D, 萨凯里四边形 A B C D -> Per A B C.
Proof.
  apply postulates_in_euclidean_context; simpl; repeat (try (left; reflexivity); right).
Qed.

Lemma not_obtuse_saccheris : ~ 钝角萨凯里四边形假设.
Proof.
  apply not_oah; right.
  unfold 直角萨凯里四边形假设; apply right_saccheris.
Qed.

Lemma suma123231__sams : forall A B C D E F, 和角 A B C B C A D E F -> 和角不大于平角 D E F C A B.
Proof. exact (t22_20 not_obtuse_saccheris). Qed.

Lemma bet_suma__suma : forall A B C D E F G H I, G <> H -> H <> I ->
  Bet G H I -> 和角 A B C B C A D E F -> 和角 D E F C A B G H I.
Proof.
  intros A B C D E F G H I HGH HHI HBet HSuma.
  suma.统计不重合点.
  destruct (bet__trisuma A B C G H I) as [D' [E' [F' []]]]; auto.
  apply (等角保持和角性质 D' E' F' C A B G H I); try apply 同角相等; auto.
  apply (和角的唯一性 A B C B C A); assumption.
Qed.

Lemma suma__suppa : forall A B C D E F, 和角 A B C B C A D E F -> 互为补角 D E F C A B.
Proof.
  intros A B C D E F HSuma.
  suma.统计不重合点.
  destruct (构造满足中间性的不重合点 A B) as [A' []].
  apply 和角为平角则为补角 with A B A'; trivial.
  apply bet_suma__suma; auto.
Qed.

Lemma high_school_exterior_angle_theorem : forall A B C B', A <> B -> B <> C -> A <> C -> A <> B' ->
  Bet B A B' -> 和角 A B C B C A C A B'.
Proof.
  intros A B C B'; intros.
  destruct (和角的存在性 A B C B C A) as [D [E [F HSuma]]]; auto.
  apply (等角保持和角性质 A B C B C A D E F); try apply 同角相等; auto.
  apply suppa2__conga123 with C A B.
    apply suma__suppa; assumption.
    apply suppa_sym, suppa_left_comm, bet__suppa; auto.
Qed.

(** If A, B and C are points on a circle where the line AB is a diameter of the circle,
    then the angle ACB is a right angle. *)

Lemma thales_theorem : forall A B C M,
  中点 M A B -> Cong M A M C -> Per A C B.
Proof.
  apply rah__thales_postulate.
  unfold postulate_of_right_saccheri_quadrilaterals; apply right_saccheris.
Qed.

(** In a right triangle, the midpoint of the hypotenuse is the circumcenter. *)

Lemma thales_converse_theorem : forall A B C M,
  中点 M A B -> Per A C B -> Cong M A M C.
Proof.
  apply thales_postulate__thales_converse_postulate.
  unfold thales_postulate; apply thales_theorem.
Qed.

Lemma thales_converse_theorem_1 : forall A B C O, A <> C -> B <> C ->
  Per A C B -> Cong O A O B -> Cong O A O C -> 共面 A B C O -> 中点 O A B.
Proof.
  intros A B C O HAC HBC HPer HCong1 HCong2 HCop.
  destruct (中点的存在性 A B) as [M HM].
  assert (M = O); [|subst; apply HM].
  suma.统计不重合点.
  apply (cong4_cop2__eq A C B); Cong; [|Cop..].
  apply 等长的交换性, thales_converse_theorem with B; assumption.
Qed.

Lemma bet_cong__ghalfa : forall A B C B', A <> B -> B <> C -> A <> B' ->
  Bet B A B' -> Cong A B A C -> gHalfA A B C C A B'.
Proof.
  intros A B C B' HAB HBC HAB' HBet HCong.
  apply ghalfa_chara; split.
    apply cong__acute; auto.
  suma.统计不重合点.
  apply (等角保持和角性质 A B C B C A C A B'); try apply 同角相等; auto.
    apply high_school_exterior_angle_theorem; auto.
  apply 等角的左交换性, l11_44_1_a_等腰三角形底角相等; Cong.
Qed.

(** If the angle ACB is inscribed in a circle of center O and
    C, O lie on the same side of AB, then this angle is acute. *)

Lemma onc3_os__acute : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> OS A B O C ->
  为锐角 A C B.
Proof.
  intros O P A B C HA HB HC HOS.
  destruct (中点的存在性 A B) as [M HM].
  assert (HNCol : ~ Col A B C) by (eapply one_side_not_col124, HOS).
  assert (HLt : Lt M A M C).
  { assert (HNCol1 : ~ Col A B O) by (eapply one_side_not_col123, HOS).
    assert (M <> O) by (intro; treat_equalities; apply HNCol1; Col).
    assert (O <> C) by (intro; treat_equalities; auto).
    suma.统计不重合点.
    assert (Cong O A O C) by (apply (在同圆上的两点与圆心等距 O P); assumption).
    destruct (angle_partition M O C); auto.
    - assert (HMO := H).
      clear H.
      destruct (l8_18_过一点垂线之垂点的存在性 M O C) as [H []].
      { intro.
        destruct (共线锐角推外共线 M O C) as [_ [_ [HBet|HBet]]]; auto.
        - apply l9_9_bis in HOS.
          apply HOS.
          repeat split; Col.
          exists M; split; Col.
        - apply (长度小于等于推出反向不小于 O C O M); Le.
          apply (等长保持小于关系 O M O P); Cong.
          apply bet_inc2__incs with A B; Circle; Between.
      }
      assert (Perp O M A B) by (apply 弦中点与圆心连线垂直于弦 with P; auto).
      assert (HOS1 : OS A B C H).
      { apply l12_6, par_not_col_strict with C; Col.
        apply l12_9 with O M; Perp; [|Cop| |Cop].
          apply 等价共面ADCB, col_cop__cop with B; Col; Cop.
          apply 等价共面ADCB, col_cop__cop with A; Col; Cop.
      }
      assert (M <> H) by (intro; subst; apply one_side_not_col124 in HOS1; apply HOS1; Col).
      assert (Per M H C) by (apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with O; Col).
      apply 长度小于的传递性 with H C; [|suma.统计不重合点; apply l11_46_非锐角三角形中大角对边最长; auto].
      apply cong_lt_per2__lt_1 with O O; Cong.
        apply 直角的对称性, 直角边共线点也构成直角2 with M; Col; Perp.
        apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直2 with B; Col.
      apply bet__lt1213; auto; apply out2__bet.
        apply (acute_col_perp__out C); [apply 为锐角的对称性|..]; Col; Perp.
        apply (l9_19 A B); Col; apply one_side_transitivity with C; assumption.
    - apply 长度小于的传递性 with O C; [|apply l11_46_非锐角三角形中大角对边最长; auto].
      apply (等长保持小于关系 M A O A); Cong.
      apply l11_46_非锐角三角形中大角对边最长; auto.
      left.
      apply 弦中点与圆心连线形成直角 with P B; auto.
  }
  destruct HLt as [[C' [HBet HCong]] HNCong].
  exists A, C', B; split.
    apply thales_theorem with M; trivial.
  suma.统计不重合点.
  assert (C <> C') by (intro; subst; apply HNCong, HCong).
  apply os3__lta.
  - apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; [Col|apply l6_6, bet_out; Between].
      apply out_one_side; [left; intro; apply HNCol; ColR|apply l6_6, bet_out; Between].
  - apply out_one_side_1 with M; Col; apply l6_6, bet_out; auto.
  - apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; [Col|apply l6_6, bet_out; Between].
      apply out_one_side; [left; intro; apply HNCol; ColR|apply l6_6, bet_out; Between].
Qed.

Lemma inscribed_angle_aux : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
  OS A B O C -> TS O C A B ->
  gHalfA A C B A O B.
Proof.
  intros O P A B C HA HB HC HOS HTS.
  destruct (由一点往一方向构造等长线段 C O O P) as [C' []].
  suma.统计不重合点.
  assert (O <> C') by (intro; treat_equalities; auto).
  assert (HCong := (在同圆上的两点与圆心等距 O P)).
  apply suma_preserves_ghalfa with A C C' C' C B A O C' C' O B.
    apply (onc3_os__acute O P); assumption.
    apply 异侧推出和角1, invert_two_sides, col_two_sides with O; Side; Col.
    apply 异侧推出和角1, invert_two_sides, col_two_sides with C; Col.
    apply ghalfa_out4__ghalfa with A O A C'; try apply out_trivial; auto;
      [apply l6_6, bet_out|apply ghalfa_left_comm, bet_cong__ghalfa]; auto.
    apply ghalfa_out4__ghalfa with O B C' B; try apply out_trivial; auto;
      [apply l6_6, bet_out|apply ghalfa_right_comm, bet_cong__ghalfa]; auto.
Qed.

Lemma inscribed_angle_aux1 : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
  OS A B O C -> OS O C A B ->
  gHalfA A C B A O B.
Proof.
  assert (Haux : forall O P A B C, 在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
  OS A B O C -> OS O C A B -> OS O B A C -> gHalfA A C B A O B).
  { intros O P A B C HA HB HC HOS1 HOS2 HOS3.
    destruct (由圆上圆内两点补全一弦 O P C O) as [C' [HC' HBet ]]; Circle.
    suma.统计不重合点.
    assert (C' <> O) by (intro; treat_equalities; auto).
    assert (TS O B A C').
    { apply l9_8_2 with C; [|Side].
      apply one_side_not_col124 in HOS3.
      repeat split.
        Col.
        intro; apply HOS3; ColR.
      exists O; split; Col.
    }
    assert (HCong := (在同圆上的两点与圆心等距 O P)).
    apply acute_ghalfa2_sams_suma2__ghalfa123 with B C O A C O B O C' A O C'.
    - repeat split; auto.
        right; intro; assert_cols; assert_ncols; Col.
      exists C'.
      split; 等角.
      repeat split; [Side| |Cop].
      apply l9_9_bis, invert_one_side, one_side_symmetry, os_ts1324__os; [|Side].
      apply col_one_side with C; Col; Side.
    - apply (onc3_os__acute O P); assumption.
    - exists O.
      repeat (split; 等角); [|Cop].
      apply l9_9, invert_two_sides, l9_31; Side.
    - exists C'.
      repeat (split; 等角); [Side|Cop].
    - apply ghalfa_left_comm, bet_cong__ghalfa; auto.
    - apply ghalfa_left_comm, bet_cong__ghalfa; auto.
  }
  intros O P A B C HA HB HC HOS1 HOS2.
  assert_ncols.
  destruct (cop__one_or_two_sides O B A C) as [HTS|]; Col; Cop.
    apply ghalfa_comm, Haux with P; auto; [..|apply one_side_symmetry, os_ts1324__os]; Side.
    apply Haux with P; assumption.
Qed.

(** Euclid Book III Prop 20:
    In a circle the angle at the centre is double of the angle at the circumference,
    when the angles have the same circumference as base. *)

Lemma inscribed_angle : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> OS A B O C ->
  gHalfA A C B A O B.
Proof.
  intros O P A B C HA HB HC HOS.
  assert (HCong := (在同圆上的两点与圆心等距 O P)).
  destruct (共线的决定性 A O C).
  { suma.统计不重合点.
    assert (Bet C O A) by (apply col_inc_onc2__bet with O P; Col; Circle).
    assert (O <> C) by (intro; treat_equalities; auto).
    apply ghalfa_right_comm, ghalfa_out4__ghalfa with O B B A; try apply out_trivial; auto.
      apply l6_6, bet_out; auto.
    apply bet_cong__ghalfa; auto.
  }
  destruct (共线的决定性 B O C).
  { suma.统计不重合点.
    assert (Bet C O B) by (apply col_inc_onc2__bet with O P; Col; Circle).
    assert (O <> C) by (intro; treat_equalities; auto).
    apply ghalfa_left_comm, ghalfa_out4__ghalfa with O A A B; try apply out_trivial; auto.
      apply l6_6, bet_out; auto.
    apply bet_cong__ghalfa; auto.
  }
  destruct (cop__one_or_two_sides O C A B); Cop.
    apply inscribed_angle_aux with P; assumption.
    apply inscribed_angle_aux1 with P; assumption.
Qed.

Lemma diam_onc2_ts__suppa : forall O P A B C C',
  在圆上 A O P -> 在圆上 B O P -> 直径 C C' O P -> TS A B C C' ->
  互为补角 A C B A C' B.
Proof.
  intros O P A B C C' HA HB [HBet [HC HC']] HTS.
  suma.统计不重合点.
  assert (HCong := 在同圆上的两点与圆心等距 O P).
  assert (HMid : 中点 O C C') by (split; Cong).
  assert (C <> C') by (intro; treat_equalities; auto).
  assert (HNColA : ~ Col C C' A) by (apply (onc3__ncol O P); auto).
  assert (HNColB : ~ Col C C' B) by (apply (onc3__ncol O P); auto).
  assert (HSumaA : 和角 A C C' C C' A C A C') by (apply cong_mid__suma with O; auto).
  assert (HSumaB : 和角 B C C' C C' B C B C') by (apply cong_mid__suma with O; auto).
  assert (Per C A C') by (apply thales_theorem with O; auto).
  assert (Per C B C') by (apply thales_theorem with O; auto).
  assert (HSuma : 和角 C A C' C B C' C O C') by (suma.统计不重合点; apply 平角为两直角之和; auto).
  apply 和角为平角则为补角 with C O C'; trivial.
  destruct (和角的存在性 C A C' C' C B) as [D [E [F HSuma1]]]; auto.
  assert (HTS2 : TS C C' A B) by (apply (chord_intersection O P); assumption).
  assert (HTS3 : TS C' C A B) by (apply invert_two_sides, HTS2).
  assert (为锐角 C' C A).
  { suma.统计不重合点; apply acute_out2__acute with O A.
      apply l6_6, bet_out; auto.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (为锐角 C' C B).
  { suma.统计不重合点; apply acute_out2__acute with O B.
      apply l6_6, bet_out; auto.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (为锐角 C C' A).
  { suma.统计不重合点; apply acute_out2__acute with O A.
      apply l6_6, bet_out; Between.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (为锐角 C C' B).
  { suma.统计不重合点; apply acute_out2__acute with O B.
      apply l6_6, bet_out; Between.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (HSuma2 : 和角 A C B A C' C D E F).
    apply 和角的对称性, 和角结合律1 with A C C' C' C B C A C'; 和角.
  assert (H和角不大于平角 : 和角不大于平角 A C B A C' C).
    apply 和角不大于平角的对称性, 和角不大于平角结合律1 with A C C' C' C B C A C'; 和角.
  apply 和角结合律1 with A C' C C C' B D E F; [和角..|].
  apply 和角结合律2 with C A C' B C C' C B C'; 和角.
Qed.

(** In a circle the angle at the centre is double of the angle at the circumference. *)

Lemma inscribed_angle_1 : forall O P A B C, A <> B -> B <> C -> A <> C ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 共面 A B C O ->
  和角 A C B A C B A O B.
Proof.
  intros O P A B C HAB HBC HAC HA HB HC HCop.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  destruct (共线的决定性 A B O).
  { assert (中点 O A B) by (apply 若圆心在一弦上则其平分该弦 with P; auto).
    assert (Per A C B) by (apply thales_theorem with O; auto; apply 等长的传递性 with O P; Cong).
    suma.统计不重合点; apply 平角为两直角之和; Between.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  - destruct (由圆上圆内两点补全一弦 O P C O) as [C' []]; Circle.
    assert (TS A B C' C) by (apply l9_2, bet_ts__ts with O; Side).
    assert (互为补角 A C' B A C B).
      apply (diam_onc2_ts__suppa O P); [..|repeat split|]; Between.
    apply (两角和与其补角和相等 A C' B A C' B); trivial.
    apply ghalfa__suma, inscribed_angle with P; trivial.
    exists C; split; trivial.
  - apply ghalfa__suma, inscribed_angle with P; trivial.
Qed.

(** If two angles ACB and ADB are inscribed in the same circle,
    then they are either congruent or supplementary. *)

Lemma cop2_onc4__or_conga_suppa : forall O P A B C C',
  A <> B -> B <> C -> A <> C -> B <> C' -> A <> C' ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 在圆上 C' O P ->
  共面 A B C O -> 共面 A B C' O ->
  等角 A C B A C' B \/ 互为补角 A C B A C' B.
Proof.
  intros O P A B C C'; intros.
  apply 两角倍角相等则两角相等或互补 with A O B; trivial; apply inscribed_angle_1 with P; assumption.
Qed.

(** If the angle ACB is inscribed in a circle of center O and
    C, O lie on opposite sides of AB, then this angle is obtuse. *)

Lemma onc3_ts__obtuse : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> TS A B O C ->
  为钝角 A C B.
Proof.
  intros O P A B C HA HB HC HTS.
  destruct (由圆上圆内两点补全一弦 O P C O) as [C' []]; Circle.
  assert (TS A B C C') by (apply bet_ts__ts with O; Side).
  apply (acute_suppa__obtuse A C' B).
    apply (onc3_os__acute O P); trivial; exists C; split; Side.
  apply (diam_onc2_ts__suppa O P); Side.
  repeat split; Between.
Qed.

(** Euclid Book III Prop 21:
    In a circle the angles in the same segment are equal to one another. *)

Lemma cop_onc4_os__conga : forall O P A B C C',
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 在圆上 C' O P ->
  OS A B C C' -> 共面 A B C O ->
  等角 A C B A C' B.
Proof.
  intros O P A B C C' HA HB HC HC' HOS HCop.
  assert_ncols.
  destruct (共线的决定性 A B O).
  { suma.统计不重合点.
    assert (中点 O A B) by (apply 若圆心在一弦上则其平分该弦 with P; auto).
    apply l11_16_直角相等; auto; apply thales_theorem with O; Col; apply 等长的传递性 with O P; Cong.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  - suma.统计不重合点; destruct (cop2_onc4__or_conga_suppa O P A B C C') as [|Habs]; auto.
      apply coplanar_trans_1 with C; Col; Cop.
    exfalso.
    apply (一角不可能小于自己 A C' B), acute_obtuse__lta.
      apply (obtuse_suppa__acute A C B); [apply (onc3_ts__obtuse O P)|]; trivial.
      apply (onc3_ts__obtuse O P); trivial; apply l9_2, l9_8_2 with C; Side.
  - apply ghalfa2__conga_2 with A O B; apply inscribed_angle with P; trivial.
    apply one_side_transitivity with C; Side.
Qed.

(** Euclid Book III Prop 22:
    The opposite angles of quadrilaterals in circles are equal to two right angles. *)

Lemma cop_onc4_ts__suppa : forall O P A B C C',
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 在圆上 C' O P ->
  TS A B C C' -> 共面 A B C O ->
  互为补角 A C B A C' B.
Proof.
  intros O P A B C C' HA HB.
  revert C C'.
  assert (Haux : forall C C', 在圆上 C O P -> 在圆上 C' O P -> TS A B C C' -> OS A B O C ->
    互为补角 A C B A C' B).
  { intros C C' HC HC' HTS HOS.
    suma.统计不重合点.
    assert (~ Col C A B) by (destruct HTS; assumption).
    assert (共面 A B C' O) by (apply coplanar_trans_1 with C; Cop).
    destruct (cop2_onc4__or_conga_suppa O P A B C C') as [Habs|]; Cop.
    exfalso.
    assert (HLta : 角度小于 A C B A C' B); [|destruct HLta as [_ HN]; apply HN, Habs].
    apply acute_obtuse__lta.
      apply (onc3_os__acute O P); assumption.
    apply (onc3_ts__obtuse O P); trivial.
    apply l9_8_2 with C; Side.
  }
  intros C C' HC HC' HTS HCop.
  assert (~ Col C A B) by (destruct HTS; assumption).
  destruct (共线的决定性 A B O).
  { suma.统计不重合点.
    assert (中点 O A B) by (apply 若圆心在一弦上则其平分该弦 with P; auto).
    destruct HTS as [_ []].
    apply per2__suppa; auto; apply thales_theorem with O; trivial; apply 在同圆上的两点与圆心等距 with P; assumption.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  apply suppa_sym, Haux; [..|exists C; split]; Side.
Qed.

(** If the angle ACB is acute and inscribed in a circle of center O,
    then C and O lie on the same side of AB. *)

Lemma acute_cop_onc3__os : forall O P A B C, A <> B ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 共面 A B C O -> 为锐角 A C B ->
  OS A B O C.
Proof.
  intros O P A B C HAB HA HB HC HCop H为锐角.
  suma.统计不重合点.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  apply 等价共面ABDC in HCop.
  apply cop_nts__os; Col; intro Habs; apply (一角不可能小于自己 A C B).
  - apply acute_per__lta; auto.
    apply thales_theorem with O; trivial.
      apply 若圆心在一弦上则其平分该弦 with P; Col.
      apply (在同圆上的两点与圆心等距 O P); assumption.
  - apply acute_obtuse__lta; trivial.
    apply (onc3_ts__obtuse O P); assumption.
Qed.

(** If the angle ACB is obtuse and inscribed in a circle of center O,
    then C and O lie on opposite sides of AB. *)

Lemma cop_obtuse_onc3__ts : forall O P A B C,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 共面 A B C O -> 为钝角 A C B ->
  TS A B O C.
Proof.
  intros O P A B C HA HB HC HCop H为钝角.
  suma.统计不重合点.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  apply 等价共面ABDC in HCop.
  apply cop_nos__ts; Col; intro Habs; apply (一角不可能小于自己 A C B).
  - apply obtuse_per__lta; auto.
    apply thales_theorem with O; trivial.
      apply 若圆心在一弦上则其平分该弦 with P; Col.
      apply (在同圆上的两点与圆心等距 O P); assumption.
  - apply acute_obtuse__lta; trivial.
    apply (onc3_os__acute O P); assumption.
Qed.

(** If the angles ACB and ADB are congruent and inscribed in the same circle,
    then C and D lie on the same side of AB. *)

Lemma conga_cop2_onc4__os : forall O P A B C D, ~ Col A B O ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 在圆上 D O P ->
  共面 A B O C -> 共面 A B O D -> 等角 A C B A D B ->
  OS A B C D.
Proof.
  intros O P A B C D HNCol HA HB HC HD HCopC HCopD HConga.
  suma.统计不重合点.
  destruct (angle_partition A C B) as [H为锐角|[HPer|H为钝角]]; auto.
  - apply one_side_transitivity with O; [apply one_side_symmetry|];
      apply acute_cop_onc3__os with P; Cop.
    apply (acute_conga__acute A C B); assumption.
  - exfalso.
    apply HNCol, 等价共线BCA, 中点蕴含共线.
    assert (HCong := 在同圆上的两点与圆心等距 O P).
    apply thales_converse_theorem_1 with C; Cop.
  - exists O; split; apply l9_2; apply cop_obtuse_onc3__ts with P; Cop.
    apply (conga_obtuse__obtuse A C B); assumption.
Qed.

(** If the angles ACB and ADB are supplementary and inscribed in the same circle,
    then C and D lie on opposite sides of AB. *)

Lemma cop2_onc4_suppa__ts : forall O P A B C D, ~ Col A B O ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 在圆上 D O P ->
  共面 A B O C -> 共面 A B O D -> 互为补角 A C B A D B ->
  TS A B C D.
Proof.
  intros O P A B C D HNCol HA HB HC HD HCopC HCopD HSuppa.
  suma.统计不重合点.
  destruct (angle_partition A C B) as [H为锐角|[HPer|H为钝角]]; auto.
  - apply l9_8_2 with O.
      apply cop_obtuse_onc3__ts with P; Cop; apply (acute_suppa__obtuse A C B); assumption.
      apply acute_cop_onc3__os with P; Cop.
  - exfalso.
    apply HNCol, 等价共线BCA, 中点蕴含共线.
    assert (HCong := 在同圆上的两点与圆心等距 O P).
    apply thales_converse_theorem_1 with C; Cop.
  - apply l9_2, l9_8_2 with O.
      apply cop_obtuse_onc3__ts with P; Cop.
    apply acute_cop_onc3__os with P; Cop; apply (obtuse_suppa__acute A C B); assumption.
Qed.

(** Non degenerated triangles can be circumscribed. *)

Lemma triangle_circumscription : forall A B C, ~ Col A B C ->
  exists CC : Tpoint, Cong A CC B CC /\ Cong A CC C CC /\ 共面 A B C CC.
Proof.
  apply postulates_in_euclidean_context; simpl; repeat (try (left; reflexivity); right).
Qed.

(** Euclid Book III Prop 23:
    On the same straight line there cannot be constructed
    two similar and unequal segments of circles on the same side. *)

Lemma conga_cop_onc6_os__eqc : forall A B C D O P O' P',
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 共面 A B C O ->
  在圆上 A O' P' -> 在圆上 B O' P' -> 在圆上 D O' P' -> 共面 A B D O' ->
  OS A B C D -> 等角 A C B A D B ->
  同圆 O P O' P'.
Proof.
  intros A B C D O P O' P' HA HB HC HCop HA' HB' HD' HCop' HOS HConga.
  apply eqc_chara.
  assert (O = O'); [|split; trivial; subst O'; apply 等长的传递性 with O A; Cong].
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D, HOS).
  assert (HCong := 在同圆上的两点与圆心等距 O P).
  assert (HCong' := 在同圆上的两点与圆心等距 O' P').
  destruct (共线的决定性 A B O) as [|HNCol1].
  { suma.统计不重合点.
    assert (中点 O A B) by (apply 若圆心在一弦上则其平分该弦 with P; assumption).
    apply (中点的唯一性1 A B); trivial.
    apply thales_converse_theorem_1 with D; auto.
    apply (l11_17_等于直角的角是直角 A C B); trivial.
    apply thales_theorem with O; auto.
  }
  assert (HNCol' : ~ Col A B D) by (apply one_side_not_col124 with C, HOS).
  destruct (中点的存在性 A B) as [M HM].
  assert (HOS1 : OS A B O O').
  { suma.统计不重合点; destruct (angle_partition A C B) as [H为锐角|[HPer|H为钝角]]; auto.
    - apply one_side_transitivity with C;
        [|apply one_side_transitivity with D; trivial; apply one_side_symmetry].
        apply acute_cop_onc3__os with P; auto.
      apply acute_cop_onc3__os with P'; auto.
      apply (acute_conga__acute A C B); assumption.
    - exfalso.
      apply HNCol1, 等价共线BCA, 中点蕴含共线.
      apply thales_converse_theorem_1 with C; auto.
    - exists C; split; [|apply l9_2, l9_8_2 with D; [apply l9_2|Side]].
        apply cop_obtuse_onc3__ts with P; auto.
      apply cop_obtuse_onc3__ts with P'; auto.
      apply (conga_obtuse__obtuse A C B); assumption.
  }
  assert (HNCol1' : ~ Col A B O') by (apply one_side_not_col124 with O, HOS1).
  destruct (bet_cop_onc2__ex_onc_os_out O P A B C M) as [C1]; Between; Col; [suma.统计不重合点; auto..|].
  destruct (bet_cop_onc2__ex_onc_os_out O' P' A B D M) as [D1]; Between; Col; [suma.统计不重合点; auto..|].
  分离合取式.
  assert (HNCol2 : ~ Col A B C1) by (apply one_side_not_col124 with C; assumption).
  assert (HOut : Out M C1 D1).
  { apply (l9_19 A B); [Col| |
      apply one_side_transitivity with C; [|apply one_side_transitivity with D]; Side].
    assert (O <> M) by (intro; subst; apply HNCol1; Col).
    assert (O' <> M) by (intro; subst; apply HNCol1'; Col).
    assert (Col O O' M); [|ColR].
    suma.统计不重合点; apply (cop_per2__col A); auto;
      [|apply 弦中点与圆心连线形成直角 with P B; auto|apply 弦中点与圆心连线形成直角 with P' B; auto].
    apply coplanar_trans_1 with B; Col; [|Cop].
    apply coplanar_trans_1 with C; Col; [Cop|].
    apply 等价共面CABD, coplanar_trans_1 with D; Col; Cop.
  }
  destruct (两点重合的决定性 C1 D1).
  { subst D1.
    suma.统计不重合点.
    apply (cong4_cop2__eq A B C1); Cong; exists M; left; split; Col.
  }
  assert (HNCol2' : ~ Col A B D1) by (apply one_side_not_col124 with D; assumption).
  assert (等角 A C1 B A C B) by (apply (cop_onc4_os__conga O P); Side; exists M; left; split; Col).
  assert (等角 A D1 B A D B) by (apply (cop_onc4_os__conga O' P'); Side; exists M; left; split; Col).
  assert (Out A B M) by (suma.统计不重合点; apply l6_6, bet_out; Between).
  assert (Out B A M) by (suma.统计不重合点; apply l6_6, bet_out; Between).
  assert (HH := HOut).
  destruct HH as [HMC1 [HMD1 [HBet|HBet]]]; exfalso.
  - apply (一角小于另一角则两角不可能相等 A D B A C B); 等角.
    apply (等角保持角度小于性质 A D1 B A C1 B); trivial.
    assert (Out D1 M C1) by (apply l6_6, bet_out; Between).
    apply os3__lta; [|apply one_side_symmetry, l9_19 with M; Col|];
      apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2'; ColR.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2'; ColR.
  - apply (一角小于另一角则两角不可能相等 A C B A D B); trivial.
    apply (等角保持角度小于性质 A C1 B A D1 B); trivial.
    assert (Out C1 M D1) by (apply l6_6, bet_out; Between).
    apply os3__lta; [|apply l9_19 with M; Col|];
      apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2; ColR.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2; ColR.
Qed.

Lemma conga_cop_onc3_os__onc : forall A B C D O P,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
  共面 A B C O -> OS A B C D -> 等角 A C B A D B ->
  在圆上 D O P.
Proof.
  intros A B C D O P HA HB HC HCop HOS HConga.
  destruct (triangle_circumscription A B D) as [O'].
    apply one_side_not_col124 in HOS; Col.
  分离合取式.
  assert (在圆上 A O' A /\ 在圆上 B O' A /\ 在圆上 D O' A).
    unfold 在圆上; repeat split; Cong.
  分离合取式.
  apply (conga_cop_onc6_os__eqc A B C D O P O' A); trivial.
Qed.

(** If the angles ACB and ADB are congruent and C, D lie on the same side of AB,
    then A, B, C and D are concyclic. *)

Lemma conga_os__concyclic : forall A B C D,
  OS A B C D -> 等角 A C B A D B -> 共圆 A B C D.
Proof.
  intros A B C D HOS HConga.
  split.
    apply os__coplanar, HOS.
  destruct (triangle_circumscription A B C) as [O]; 分离合取式.
    apply one_side_not_col123 with D, HOS.
  assert (在圆上 A O A /\ 在圆上 B O A /\ 在圆上 C O A).
    unfold 在圆上; repeat split; Cong.
  分离合取式.
  exists O, A; repeat split; trivial.
  apply (conga_cop_onc3_os__onc A B C); assumption.
Qed.

(** If the angles ACB and ADB are supplementary and C, D lie on opposite sides of AB,
    then A, B, C and D are concyclic. *)

Lemma suppa_ts__concyclic : forall A B C D,
  TS A B C D -> 互为补角 A C B A D B -> 共圆 A B C D.
Proof.
  intros A B.
  assert (Haux : forall C D, TS A B C D -> 为钝角 A C B -> 互为补角 A C B A D B -> 共圆 A B C D).
  { intros C D HTS H为钝角 HSuppa.
    split.
      apply 异侧蕴含共面, HTS.
    assert (HNCol : ~ Col A B C) by (destruct HTS; Col).
    destruct (triangle_circumscription A B C HNCol) as [O]; 分离合取式.
    assert (在圆上 A O A /\ 在圆上 B O A /\ 在圆上 C O A).
      unfold 在圆上; repeat split; Cong.
    分离合取式.
    exists O, A; repeat split; trivial.
    destruct (由圆上圆内两点补全一弦 O A C O) as [C'[HC' HBet]]; Circle.
    assert (TS A B C C').
      apply bet_ts__ts with O; [apply l9_2, cop_obtuse_onc3__ts with A|]; assumption.
    apply (conga_cop_onc3_os__onc A B C'); trivial.
      apply coplanar_trans_1 with C; Col; Cop.
      exists C; split; Side.
      apply (suppa2__conga456 A C B); [apply (cop_onc4_ts__suppa O A)|]; assumption.
  }
  intros C D HTS HSuppa.
  assert (HCop : 共面 A B C D) by (apply 异侧蕴含共面, HTS).
  suma.统计不重合点; destruct (angle_partition A C B) as [|[|]]; auto; split; trivial.
  { destruct (Haux D C) as [_ [O [P]]].
      Side.
      apply (acute_suppa__obtuse A C B); trivial.
      apply suppa_sym, HSuppa.
    exists O, P.
    分离合取式; repeat split; trivial.
  }
  destruct (中点的存在性 A B) as [M].
  exists M, A.
  destruct HTS as [HNCol1 [HNCol2 _]].
  unfold 在圆上; repeat split; [Cong..| |];
    apply 等长的对称性, thales_converse_theorem with B; auto.
  apply (per_suppa__per A C B); assumption.
Qed.

(** In a convex quadrilateral, if two opposite angles are supplementary
    then the two other angles are also supplementary. *)

Lemma suppa_ts2__suppa : forall A B C D,
  TS A C B D -> TS B D A C -> 互为补角 A B C A D C -> 互为补角 B A D B C D.
Proof.
  intros A B C D HTS1 HTS2 HSuppa.
  assert (HCon : 共圆 A C B D) by (apply suppa_ts__concyclic; trivial).
  apply 共圆定义_辅助 in HCon.
  destruct HCon as [O [P]]; 分离合取式.
  apply (cop_onc4_ts__suppa O P); trivial.
  apply 等价共面ACBD, coplanar_trans_1 with C; [destruct HTS1; Col|Cop..].
Qed.

End Inscribed_angle.

Section Inscribed_angle_2.

Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.

Lemma chord_par_diam : forall O P A B C C' A' U,
 O <> P -> ~Col A B C' -> 直径 C C' O P -> 中点 A' A C' -> 在圆上 A O P -> 在圆上 B O P ->
 Col A B U -> Perp O U A B -> Par A C' O U -> B = C.
Proof.
intros.
suma.统计不重合点.
assert(中点 U A B).
{
  apply(垂直于弦的直径平分弦 O P A B U); Col.
}
assert(O <> A').
intro.
treat_equalities.
induction H7.
apply H7.
exists O.
split; Col.
分离合取式.
assert(Perp A U  O U).
{
  apply 垂直的对称性 in H6.
  apply (垂线共线点也构成垂直1 A B O U U); Col.
  intro.
  treat_equalities.
  apply 垂直推出不重合 in H6.
  tauto.
}
apply 垂直的左交换性 in H18.
apply L形垂直推出不共线 in H18.
apply H18; Col.
unfold 直径 in H1.
分离合取式.
assert(HH:=弦中点与圆心连线垂直于弦 O P A C' A' H15 H13 H3 H17 H2).
assert(Perp O U O A').
{
  apply(par_perp__perp A C' O U O A' H7); Perp.
}

assert(Par O A' A B).
{
  apply (l12_9_2D _ _ _ _ O U); Perp.
}
assert(HM:=中点的存在性 B C').
ex_and HM O'.
assert(HP:= 广义三角形中位线平行于第三边 A B C' O' A' H0 H20 H2).
apply par_strict_par in HP.
assert(Par O A' A' O').
{
  apply (par_trans _ _ A B); Par.
}
assert(Col O O' A').
{
  induction H21.
  apply False_ind.
  apply H21.
  exists A'.
  split; Col.
  分离合取式.
  Col.
}

induction(两点重合的决定性 O O').
treat_equalities.
apply(中点组的唯一性1 C' O); 中点.
split; [Between|CongR].

assert(HQ:= 弦中点与圆心连线垂直于弦 O P B C' O' H23  H10 H4 H17 H20).
apply(垂线共线点也构成垂直1 O A' A C' O') in HH; Col.
assert(Par A C' B C').
{
  apply(l12_9_2D A C' B C' O O'); Perp.
}
apply False_ind.
induction H24.
apply H24.
exists C'.
split;Col.
分离合取式.
apply H0.
Col.
Qed.

End Inscribed_angle_2.
