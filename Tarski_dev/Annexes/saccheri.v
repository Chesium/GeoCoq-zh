Require Export GeoCoq.Tarski_dev.Ch12_parallel.
Require Export GeoCoq.Tarski_dev.Annexes.suma.

(** This development is inspired by The Foundations of Geometry and the Non-Euclidean Plane,
    by George E. Martin, chapters 21 and 22 *)

Section 萨凯里四边形.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma sac_perm : forall A B C D, 萨凯里四边形 A B C D -> 萨凯里四边形 D C B A.
Proof.
  intros.
  unfold 萨凯里四边形 in *.
  spliter.
  repeat split; Perp; Cong; Side.
Qed.

Lemma sac_distincts : forall A B C D,
  萨凯里四边形 A B C D ->
  A <> B /\ B <> C /\ C <> D /\ A <> D /\ A <> C /\ B <> D.
Proof.
  intros A B C D HSac.
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  repeat split; auto.
  intro; treat_equalities.
  assert(A=D) by (apply (ABC和ACB均直角则B与C重合 B A D); Perp); auto.
Qed.

Lemma lam_perm : forall A B C D, Lambert四边形 A B C D -> Lambert四边形 A D C B.
Proof.
  intros.
  unfold Lambert四边形 in *.
  spliter.
  repeat split; Perp; Cop.
Qed.

(** The two following lemmas come from Theorem 21.10 *)

Lemma sac__cong : forall A B C D, 萨凯里四边形 A B C D -> Cong A C B D.
Proof.
  intros A B C D HSac.
  assert(Hdiff := sac_distincts A B C D HSac).
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert(HSAS := l11_49 B A D C D A).
  destruct HSAS; Cong; 等角.
Qed.

Lemma sac__conga : forall A B C D, 萨凯里四边形 A B C D -> 等角 A B C B C D.
Proof.
  intros A B C D HSac.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HCong := sac__cong A B C D HSac).
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert(HSSS := l11_51 A B C D C B).
  destruct HSSS as [_ []]; Cong; 等角.
Qed.

Lemma lam__pars1234 : forall A B C D, Lambert四边形 A B C D -> 严格平行 A B C D.
Proof.
  unfold Lambert四边形.
  intros A B C D HLam.
  spliter.
  assert (~ Col B A D) by (apply 成直角三点不共线; auto).
  apply (col_cop_perp2__pars D A); Perp; Col.
Qed.

Lemma lam__pars1423 : forall A B C D, Lambert四边形 A B C D -> 严格平行 A D B C.
Proof.
  intros; apply par_strict_right_comm, lam__pars1234, lam_perm; assumption.
Qed.

Lemma lam__par1234 : forall A B C D, Lambert四边形 A B C D -> Par A B C D.
Proof.
  intros A B C D HLam.
  apply par_strict_par, lam__pars1234, HLam.
Qed.

Lemma lam__par1423 : forall A B C D, Lambert四边形 A B C D -> Par A D B C.
Proof.
  intros A B C D HLam.
  apply par_strict_par, lam__pars1423, HLam.
Qed.

Lemma lam__os : forall A B C D, Lambert四边形 A B C D -> OS A B C D.
Proof.
  intros A B C D H; apply l12_6, lam__pars1234, H.
Qed.

Lemma per2_os__pars : forall A B C D, Per B A D -> Per A D C -> OS A D B C ->
  严格平行 A B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos.
  assert_diffs.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C), Hos).
  apply (col_cop_perp2__pars D A); Perp; Col; Cop.
Qed.

Lemma per2_os__ncol123 : forall A B C D, Per B A D -> Per A D C -> OS A D B C ->
   ~ Col A B C.
Proof.
  intros A B C D HPer1 HPer2 Hos.
  apply (par_strict_not_col_1 _ _ _ D), per2_os__pars; assumption.
Qed.

Lemma per2_os__ncol234 : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C ->
  ~ Col B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos.
  apply (par_strict_not_col_2 A), per2_os__pars; assumption.
Qed.

Lemma sac__pars1234 : forall A B C D, 萨凯里四边形 A B C D -> 严格平行 A B C D.
Proof.
  unfold 萨凯里四边形.
  intros A B C D HSac; spliter.
  apply per2_os__pars; assumption.
Qed.

Lemma sac__par1234 : forall A B C D, 萨凯里四边形 A B C D -> Par A B C D.
Proof.
  intros A B C D HSac.
  left; apply sac__pars1234, HSac.
Qed.

(** The five following lemmas come from Theorem 21.8 *)

Lemma lt_os_per2__lta : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C ->
  Lt A B C D ->
  角度小于 B C D A B C.
Proof.
  intros A B C D HPer1 HPer2 Hos Hlt.
  apply 长度小于的右交换性 in Hlt.
  destruct Hlt as [[E []] HNCong].
  assert(E<>C) by (intro; subst; auto).
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ C); auto).
  assert(~ Col A D C) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  assert(HNCol1 :=  per2_os__ncol123 A B C D HPer1 HPer2 Hos).
  assert(HNCol2 :=  per2_os__ncol234 A B C D HPer1 HPer2 Hos).
  assert(HSac : 萨凯里四边形 A B E D).
  { repeat split; Cong.
    apply (直角边共线点也构成直角2 _ _ C); Col.
    apply (one_side_transitivity _ _ _ C); auto.
    apply one_side_symmetry; apply invert_one_side.
    apply out_one_side.
    right; Col.
    apply bet_out; auto.
  }
  assert(HNCol3 : ~ Col E C B) by (intro; apply HNCol2; ColR).
  assert(严格平行 A B C D).
  { apply (par_not_col_strict _ _ _ _ D); Col.
    apply (l12_9 _ _ _ _ A D); Perp; Cop.
  }
  assert_diffs.
  apply (lta_trans _ _ _ B E D).
  - assert(HInter := l11_41 E C B D).
    destruct HInter; Between.
    apply (conga_preserves_lta E C B B E D); try (apply 同角相等); auto.
    apply (l11_10 E C B B C E); try (apply out_trivial); 等角.
    apply l6_6, bet_out; Between.

  - apply (conga_preserves_lta A B E A B C); try (apply 同角相等); auto.
    apply sac__conga; auto.
    split.
    { apply inangle__lea.
      apply os2__inangle.
      - apply l12_6.
        apply (par_strict_col_par_strict _ _ _ D); Par; Col.

      - apply (one_side_transitivity _ _ _ D);
        [|apply invert_one_side, one_side_symmetry, out_one_side; Out; Col].
        destruct (par_one_or_two_sides A B D C) as [[]|[]]; Par.
        exfalso; apply (l9_9 A D B C); trivial.
    }
    intro.
    assert (Out B E C).
      apply (conga_os__out A); trivial; apply one_side_symmetry, par_strict_one_side with D; Col.
    apply HNCol3; Col.
Qed.

Lemma lt4321_os_per2__lta : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> Lt D C B A ->
  角度小于 A B C B C D.
Proof.
  intros.
  apply 角度小于的交换性, lt_os_per2__lta; Perp; Side.
Qed.

Lemma lta_os_per2__lt : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> 角度小于 B C D A B C ->
  Lt A B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos H角度小于.
  destruct (两长度必大于小于或等于 A B C D) as [Hlt | [Hlt | Hcong]]; trivial; exfalso.
  - unfold Gt in Hlt.
    apply 长度小于的交换性 in Hlt.
    apply (两长度不可能互相小于对方a B C D A B C).
    split; trivial.
    apply lt4321_os_per2__lta; trivial.
  - destruct H角度小于 as [H角度小于等于 HN等角].
    apply HN等角.
    apply 等角的对称性, sac__conga.
    unfold 萨凯里四边形; repeat (split; trivial).
Qed.

Lemma lta123234_os_per2__lt : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> 角度小于 A B C B C D ->
  Lt D C B A.
Proof.
  intros.
  apply lta_os_per2__lt; Perp; Side.
  apply 角度小于的交换性; trivial.
Qed.

Lemma conga_per2_os__cong : forall A B C D,
  Per B A D -> Per A D C ->
  OS A D B C -> 等角 B C D A B C ->
  Cong A B C D.
Proof.
  intros A B C D HPer1 HPer2 Hos H等角.
  destruct (两长度必大于小于或等于 A B C D) as [Hlt | [Hlt | Hcong]]; trivial; exfalso.
  - destruct (lt_os_per2__lta A B C D); auto.
  - unfold Gt in Hlt.
    apply 长度小于的交换性 in Hlt.
    destruct (lt4321_os_per2__lta A B C D); 等角.
Qed.

(** The two following lemmas constitute Theorem 21.11 *)

Lemma mid2_sac__perp_lower : forall A B C D M N,
  萨凯里四边形 A B C D ->
  中点 M B C -> 中点 N A D ->
  Perp A D M N.
Proof.
  intros A B C D M N HSac HM HN.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HConga := sac__conga A B C D HSac).
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert_diffs.
  assert(HSAS := l11_49 M B A M C D).
  destruct HSAS; Cong.
    apply (l11_10 C B A B C D); [等角|Out..].
  apply (l8_16_2_共线四点和一直角推另一垂直 _ _ _ A); Col.
  { apply one_side_not_col124 with B.
    apply l9_17 with C; Between.
  }
  exists D.
  split; auto.
Qed.

Lemma mid2_sac__perp_upper : forall A B C D M N, 萨凯里四边形 A B C D ->
  中点 M B C -> 中点 N A D -> Perp B C M N.
Proof.
  intros A B C D M N HSac HM HN.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HConga := sac__conga A B C D HSac).
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert_diffs.
  assert(HSAS := l11_49 N A B N D C).
  destruct HSAS; Cong.
  { apply l11_16_直角相等; auto.
    apply (l8_3_直角边共线点也构成直角1 D); Perp; Col.
    apply (l8_3_直角边共线点也构成直角1 A); Col.
  }
  apply 垂直的右交换性.
  apply (l8_16_2_共线四点和一直角推另一垂直 _ _ _ B); Col.
  { intro.
    absurd (Col A D N); [|Col].
    apply one_side_not_col124 with B.
    apply l9_17 with C; trivial.
    apply midpoint_bet, 不重合共线点间距相同则为中点组1; Col.
  }
  exists C.
  split; auto.
Qed.

Lemma sac__pars1423 : forall A B C D, 萨凯里四边形 A B C D -> 严格平行 A D B C.
Proof.
  intros A B C D HSac.
  assert(HM := 中点的存在性 B C).
  destruct HM as [M HM].
  assert(HN := 中点的存在性 A D).
  destruct HN as [N HN].
  assert(HPerp1 := mid2_sac__perp_lower A B C D M N HSac HM HN).
  assert(HPerp2 := mid2_sac__perp_upper A B C D M N HSac HM HN).
  unfold 萨凯里四边形 in HSac.
  spliter.
  apply (col_cop_perp2__pars M N); Col; Cop.
  apply one_side_not_col124 with B.
  apply l9_17 with C; Between.
Qed.

Lemma sac__par1423 : forall A B C D, 萨凯里四边形 A B C D -> Par A D B C.
Proof.
  intros A B C D HSac.
  apply par_strict_par, sac__pars1423, HSac.
Qed.

(** The four following constitute Theorem 22.3 *)

Lemma mid2_sac__lam6521 : forall A B C D M N,
  萨凯里四边形 A B C D ->
  中点 M B C -> 中点 N A D ->
  Lambert四边形 N M B A.
Proof.
  intros A B C D M N HSac HM HN.
  unfold Lambert四边形.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HPerp1 := mid2_sac__perp_lower A B C D M N HSac HM HN).
  assert(HPerp2 := mid2_sac__perp_upper A B C D M N HSac HM HN).
  unfold 萨凯里四边形 in HSac.
  spliter.
  assert_diffs.
  repeat split; auto.
  - apply L形垂直转直角1, (垂线共线点也构成垂直2 _ _ _ D); Perp; Col.
  - apply (l8_3_直角边共线点也构成直角1 D); Perp; Col.
  - apply L形垂直转直角1; auto.
    apply (垂线共线点也构成垂直2 _ _ _ C); Perp; Col.
  - apply coplanar_perm_5, col_cop__cop with C; Col.
    apply coplanar_perm_22, col_cop__cop with D; Col; Cop.
Qed.

Lemma mid2_sac__lam6534 : forall A B C D M N,
  萨凯里四边形 A B C D ->
  中点 M B C -> 中点 N A D ->
  Lambert四边形 N M C D.
Proof.
  intros A B C D M N HSac HM HN.
  apply (mid2_sac__lam6521 _ _ B A); [apply sac_perm|apply M是AB中点则M是BA中点..]; assumption.
Qed.

Lemma lam6521_mid2__sac : forall A B C D M N,
  Lambert四边形 N M B A ->
  中点 M B C -> 中点 N A D ->
  萨凯里四边形 A B C D.
Proof.
  intros A B C D M N HLam HM HN.
  assert (HLam' := HLam).
  unfold Lambert四边形 in HLam'.
  spliter.
  assert_diffs.
  assert(Per D A B) by (apply (l8_3_直角边共线点也构成直角1 N); Col).
  assert(严格对称 D A M N).
  { split.
    exists N; Col.
    left; apply (垂线共线点也构成垂直2 _ _ _ N); Col; Perp.
  }
  assert(严格对称 A D M N) by (apply l10_4_spec; auto).
  assert(严格对称 C B M N).
  { split.
    exists M; Col.
    left; apply (垂线共线点也构成垂直2 _ _ _ M); Col; Perp.
  }
  assert(严格对称 B C M N) by (apply l10_4_spec; auto).
  repeat split; auto.
  - Perp.
  - apply (image_spec_preserves_per D A B _ _ _ M N); auto.
  - apply 等长的左交换性.
    apply (l10_10_spec M N); auto.
  - apply (col_one_side _ N); Col.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ M); Col.
    apply lam__pars1423 in HLam; Par.
Qed.

Lemma lam6534_mid2__sac : forall A B C D M N,
  Lambert四边形 N M C D ->
  中点 M B C -> 中点 N A D ->
  萨凯里四边形 A B C D.
Proof.
  intros A B C D M N HLam HM HN.
  apply sac_perm.
  apply (lam6521_mid2__sac _ _ _ _ M N); 中点.
Qed.

(** The six following lemmas constitute Theorem 22.5 *)

Lemma cong_lam__per : forall A B C D,
  Lambert四边形 A B C D ->
  Cong A D B C ->
  Per B C D.
Proof.
  intros A B C D HLam HCong.
  assert (HLam' := HLam).
  unfold Lambert四边形 in HLam'.
  spliter.
  apply 直角的对称性, (l11_17_等于直角的角是直角 A D C); auto.
  apply sac__conga.
  repeat split; Perp; Cong.
  apply one_side_symmetry, l12_6, lam__pars1234, HLam.
Qed.

Lemma lam_lt__acute : forall A B C D,
  Lambert四边形 A B C D ->
  Lt A D B C ->
  为锐角 B C D.
Proof.
  intros A B C D HLam HLt.
  assert (HLam' := HLam).
  unfold Lambert四边形 in HLam'.
  spliter.
  exists A, D, C.
  split; trivial.
  apply 角度小于的左交换性, lt_os_per2__lta; Perp; [|apply 长度小于的右交换性; trivial].
  apply one_side_symmetry, l12_6, lam__pars1234, HLam.
Qed.

Lemma lam_lt__obtuse : forall A B C D,
  Lambert四边形 A B C D ->
  Lt B C A D ->
  为钝角 B C D.
Proof.
  intros A B C D HLam HLt.
  assert (HLam' := HLam).
  unfold Lambert四边形 in HLam'.
  spliter.
  exists A, D, C.
  split; trivial.
  apply 角度小于的左交换性, lt_os_per2__lta; Perp; [|apply 长度小于的右交换性; trivial].
  apply invert_one_side, l12_6, lam__pars1234, HLam.
Qed.

Lemma lam_per__cong : forall A B C D,
  Lambert四边形 A B C D ->
  Per B C D ->
  Cong A D B C.
Proof.
  intros A B C D HLam HPer.
  assert (HLam' := HLam).
  unfold Lambert四边形 in HLam'.
  spliter.
  destruct (两长度必大于小于或等于 A D B C) as [Habs|[HCong|Habs]]; trivial;
  exfalso; apply (nlta B C D).
  - apply acute_per__lta; trivial.
    apply (lam_lt__acute A); trivial.
  - apply obtuse_per__lta; trivial.
    apply (lam_lt__obtuse A); trivial.
Qed.

Lemma acute_lam__lt : forall A B C D,
  Lambert四边形 A B C D ->
  为锐角 B C D ->
  Lt A D B C.
Proof.
  intros A B C D HLam H为锐角.
  destruct (两长度必大于小于或等于 A D B C) as [|Habs]; trivial.
  exfalso; apply (nlta B C D).
  destruct Habs.
  - apply acute_obtuse__lta; trivial.
    apply (lam_lt__obtuse A); trivial.
  - assert (HL := HLam).
    ex_and HL Hd.
    apply acute_per__lta; trivial.
    apply (cong_lam__per A); trivial.
Qed.

Lemma lam_obtuse__lt : forall A B C D,
  Lambert四边形 A B C D ->
  为钝角 B C D ->
  Lt B C A D.
Proof.
  intros A B C D HLam H为钝角.
  destruct (两长度必大于小于或等于 A D B C) as [Habs|[Habs|HLt]]; trivial;
  exfalso; apply (nlta B C D).
  - apply acute_obtuse__lta; trivial.
    apply (lam_lt__acute A); trivial.
  - assert (HL := HLam).
    ex_and HL Hd.
    apply obtuse_per__lta; trivial.
    apply (cong_lam__per A); trivial.
Qed.

(** The three following lemmas constitute Omar Khayyam's Theorem (22.6) *)

Lemma cong_sac__per : forall A B C D,
  萨凯里四边形 A B C D ->
  Cong A D B C <-> Per A B C.
Proof.
  intros A B C D HSac.
  assert(HM := 中点的存在性 B C).
  destruct HM as [M HM].
  assert(HN := 中点的存在性 A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  apply sac_distincts in HSac; spliter.
  assert_diffs.
  split.
  - intro HCong.
    apply (直角边共线点也构成直角2 _ _ M); Col.
    apply 直角的对称性, (cong_lam__per N); auto.
    apply 等长的交换性; apply (两中点组全段等长则前半段等长 _ _ D _ _ C); auto.
  - intro HPer.
    apply 两中点组半段等长则全段等长 with N M; trivial.
    apply 等长的交换性, lam_per__cong; trivial.
    apply 直角的对称性, 直角边共线点也构成直角2 with C; Col.
Qed.

Lemma lt_sac__acute : forall A B C D,
  萨凯里四边形 A B C D ->
  Lt A D B C <-> 为锐角 A B C.
Proof.
  intros A B C D HSac.
  assert(HM := 中点的存在性 B C).
  destruct HM as [M HM].
  assert(HN := 中点的存在性 A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  assert (H等角 : 等角 A B C M B A).
  { apply sac_distincts in HSac; spliter.
    assert_diffs.
    apply 等角的右交换性, out2__conga.
      apply out_trivial; auto.
    apply bet_out; Between.
  }
  split.
  - intro HLt.
    apply (acute_conga__acute M B A); 等角.
    apply (lam_lt__acute N); trivial.
    apply 长度小于的交换性, 两中点组全段全序则半段全序 with D C; trivial.
  - intro H为锐角.
    apply 两中点组半段全序则全段全序 with N M; trivial.
    apply 长度小于的交换性, acute_lam__lt; trivial.
    apply (acute_conga__acute A B C); trivial.
Qed.

Lemma lt_sac__obtuse : forall A B C D,
  萨凯里四边形 A B C D ->
  Lt B C A D <-> 为钝角 A B C.
Proof.
  intros A B C D HSac.
  assert(HM := 中点的存在性 B C).
  destruct HM as [M HM].
  assert(HN := 中点的存在性 A D).
  destruct HN as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  assert (H等角 : 等角 A B C M B A).
  { apply sac_distincts in HSac; spliter.
    assert_diffs.
    apply 等角的右交换性, out2__conga.
      apply out_trivial; auto.
    apply bet_out; Between.
  }
  split.
  - intro HLt.
    apply (conga_obtuse__obtuse M B A); 等角.
    apply (lam_lt__obtuse N); trivial.
    apply 长度小于的交换性, 两中点组全段全序则半段全序 with C D; trivial.
  - intro H为钝角.
    apply 两中点组半段全序则全段全序 with M N; trivial.
    apply 长度小于的交换性, lam_obtuse__lt; trivial.
    apply (conga_obtuse__obtuse A B C); trivial.
Qed.


Lemma t22_7__per : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> Q <> D ->
  Per P Q A ->
  Cong P Q A B ->
  Per A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HQD HPerQ HCong.
  assert(Hd := sac_distincts A B C D HSac).
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(B <> P).
  { intro.
    subst P.
    apply HAQ, (ABC和ACB均直角则B与C重合 B); trivial.
    apply 直角边共线点也构成直角2 with D; Col.
  }
  assert(P <> C).
  { intro.
    subst P.
    apply HQD, (ABC和ACB均直角则B与C重合 C); apply 直角边共线点也构成直角2 with A; Perp; Col.
  }
  assert(HSac1 : 萨凯里四边形 A B P Q).
  { repeat split; Cong.
    apply (直角边共线点也构成直角2 _ _ D); Col.
    Perp.
    apply (col_one_side _ D); Col;
    apply (l9_17 _ _ C); Between.
  }
  assert(HSac2 : 萨凯里四边形 D C P Q).
  { repeat split; auto.
    apply (直角边共线点也构成直角2 _ _ A); Col; Perp.
    apply (l8_3_直角边共线点也构成直角1 A); Col; Perp.
    apply (等长的传递性 _ _ A B); Cong.
    apply (col_one_side _ A); Col.
    apply (l9_17 _ _ B); Between; Side.
  }
  apply (bet_suma__per _ _ _ B P C); auto.
  assert (P <> Q) by (intro; treat_equalities; auto).
  apply (等角保持和角 B P Q Q P C B P C); [和角|..|等角].
  - apply (l11_10 B P Q A B P); Out.
    apply 等角的对称性, sac__conga, HSac1.

  - apply (角等的传递性 _ _ _ P C D).
      apply sac__conga, sac_perm, HSac2.
    apply (l11_10 B C D A B C); Out.
    apply 等角的对称性; apply sac__conga; auto.
Qed.

Lemma t22_7__acute : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q ->
  Per P Q A ->
  Lt P Q A B ->
  为锐角 A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HPerQ Hlt.
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(HPar := sac__pars1423 A B C D HSac).
  assert(HPar' := sac__pars1234 A B C D HSac).
  assert(~ Col A B C) by (apply par_strict_not_col_1 with D, HPar').
  assert_diffs.
  assert(P <> Q) by (intro; apply HPar; exists P; subst; split; Col).
  assert(B <> P).
  { intro.
    subst P.
    apply HAQ, (ABC和ACB均直角则B与C重合 B); trivial; apply 直角边共线点也构成直角2 with D; Col.
  }
  assert(P <> C).
  { intro.
    subst P.
    assert(D = Q) by (apply (ABC和ACB均直角则B与C重合 C); apply 直角边共线点也构成直角2 with A; Col; Perp).
    subst; apply Hlt; Cong.
  }
  assert(Q <> D).
  { intro.
    subst Q.
    assert(Col C P D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply (par_strict_not_col_2 A B C D HPar'); ColR.
  }
  assert(Hlta1 : 角度小于 A B C B P Q).
  { apply (conga_preserves_lta A B P B P Q); try (apply 同角相等); auto.
      apply out2__conga; Out.
    apply lt4321_os_per2__lta; Le; Perp.
      apply (直角边共线点也构成直角2 _ _ D); Col.
    apply (col_one_side _ D); Col; apply (l9_17 _ _ C); auto.
  }
  assert(Hlta2 : 角度小于 A B C C P Q).
  { apply (conga_preserves_lta D C P C P Q); try (apply 同角相等); auto.
    - apply sac__conga in HSac.
      apply (l11_10 D C B A B C); [等角|Out..].
    - apply lt4321_os_per2__lta; auto.
        apply (直角边共线点也构成直角2 _ _ A); Perp; Col.
        apply (l8_3_直角边共线点也构成直角1 A); Perp; Col.
        apply (col_one_side _ A); Col; apply (l9_17 _ _ B); Between; Side.
        apply (等长保持小于关系 P Q A B); Cong.
  }
  destruct (angle_partition B P Q) as [H为锐角|[HPer|H为钝角]]; auto.
  - apply acute_lea_acute with B P Q; Lea.
  - exists B, P, Q; auto.
  - apply acute_lea_acute with C P Q; Lea.
    apply (bet_obtuse__acute B); auto.
Qed.

Lemma t22_7__obtuse : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q ->
  Per P Q A ->
  Lt A B P Q ->
  为钝角 A B C.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HPerQ Hlt.
  assert(HSac' := HSac).
  destruct HSac'.
  spliter.
  assert(HPar := sac__pars1423 A B C D HSac).
  assert(HPar' := sac__pars1234 A B C D HSac).
  assert(~ Col A B C) by (apply par_strict_not_col_1 with D, HPar').
  assert_diffs.
  assert(B <> P).
  { intro.
    subst P.
    apply HAQ, (ABC和ACB均直角则B与C重合 B); trivial; apply 直角边共线点也构成直角2 with D; Col.
  }
  assert(P <> C).
  { intro.
    subst P.
    assert(D = Q) by (apply (ABC和ACB均直角则B与C重合 C); apply 直角边共线点也构成直角2 with A; Col; Perp).
    subst; apply Hlt; Cong.
  }
  assert(Q <> D).
  { intro.
    subst Q.
    assert(Col C P D).
      apply cop_per2__col with A; Perp.
      apply coplanar_perm_3, col_cop__cop with B; Col; Cop.
    apply (par_strict_not_col_2 A B C D HPar'); ColR.
  }
  assert (角度小于 B P Q A B C).
  { apply (conga_preserves_lta B P Q A B P); try (apply 同角相等); auto.
      apply out2__conga; [apply out_trivial|apply l6_6, bet_out]; auto.
    apply lt_os_per2__lta; Perp.
      apply (直角边共线点也构成直角2 _ _ D); Col.
    apply (col_one_side _ D); Col; apply (l9_17 _ _ C); auto.
  }
  assert (角度小于 C P Q A B C).
  { apply (conga_preserves_lta Q P C P C D); try (apply 角ABC等于角CBA); auto.
    - apply sac__conga in HSac.
      apply (l11_10 B C D A B C); [等角|Out..].
    - apply lt4321_os_per2__lta.
        apply (直角边共线点也构成直角2 _ _ A); Perp; Col.
        apply (l8_3_直角边共线点也构成直角1 A); Col.
        apply invert_one_side, (col_one_side _ A); Col;
        apply one_side_symmetry, (l9_17 _ _ B); Side; Between.
        apply (等长保持小于关系 A B P Q); Cong.
  }
  destruct (angle_partition B P Q) as [H为锐角|[HPer|H为钝角]]; auto.
  - apply lea_obtuse_obtuse with C P Q; [|unfold 角度大于等于; Lea].
    apply (acute_bet__obtuse B); auto.
  - exists B, P, Q; auto.
  - apply lea_obtuse_obtuse with B P Q; [|unfold 角度大于等于]; Lea.
Qed.

Lemma t22_7__cong : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q ->
  Per P Q A -> Per A B C ->
  Cong P Q A B.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HPerQ HPer.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  destruct (等长的决定性 P Q A B); auto.
  exfalso.
  apply (nlta A B C).
  elim(长度小于等于的决定性 P Q A B).
  - intro.
    apply acute_per__lta; auto.
    apply (t22_7__acute _ _ _ D P Q); auto.
    split; auto.
  - intro.
    apply obtuse_per__lta; auto.
    apply (t22_7__obtuse _ _ _ D P Q); auto.
    split; Cong.
Qed.

Lemma t22_7__lt5612 : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> Q <> D ->
  Per P Q A -> 为锐角 A B C ->
  Lt P Q A B.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HQD HPerQ Hacute.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  destruct (等长的决定性 P Q A B).
  { exfalso.
    apply (nlta A B C).
    apply acute_per__lta; auto.
    apply (t22_7__per _ _ _ D P Q); auto.
  }
  split; auto.
  destruct (长度小于等于的决定性 P Q A B); auto.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_7__obtuse _ _ _ D P Q); auto.
  split; Cong.
Qed.

Lemma t22_7__lt1256 : forall A B C D P Q,
  萨凯里四边形 A B C D ->
  Bet B P C -> Bet A Q D ->
  A <> Q -> Q <> D ->
  Per P Q A -> 为钝角 A B C ->
  Lt A B P Q.
Proof.
  intros A B C D P Q HSac HP HQ HAQ HQD HPerQ Hobtuse.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  destruct(等长的决定性 P Q A B).
  { exfalso.
    apply (nlta A B C).
    apply obtuse_per__lta; auto.
    apply (t22_7__per _ _ _ D P Q); auto.
  }
  split; Cong.
  destruct(长度小于等于的决定性 P Q A B); auto.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_7__acute _ _ _ D P Q); auto.
  split; auto.
Qed.

Lemma t22_8_aux : forall A B C D R S J,
  萨凯里四边形 A B C D -> Bet B C R -> Bet A D S -> D <> S -> Per A S R ->
  Out S R J -> Cong S J A B ->
  C <> R /\ 萨凯里四边形 A B J S /\ 萨凯里四边形 D C J S /\ OS S J C B /\ 共面 A B C J.
Proof.
  intros A B C D R S J HSac HR HS HDS HPer HJ1 HJ2.
  assert(HSac' := HSac).
  unfold 萨凯里四边形 in HSac'.
  spliter.
  assert_diffs.
  assert(HPar := sac__pars1423 A B C D HSac).
  assert(HPer1 : Per B A S) by (apply 直角边共线点也构成直角2 with D; Col).
  assert(HPer2 : Per D S J) by (apply (l8_3_直角边共线点也构成直角1 A); [apply 直角边共线点也构成直角2 with R|..]; Col).
  assert(HPer3 : Per C D S) by (apply 直角边共线点也构成直角2 with A; Perp; Col).
  assert(HOS : OS A S B J).
  { apply one_side_transitivity with R.
      apply col_one_side with D; Col; apply par_strict_one_side with C; Col.
    assert(~ Col A S R) by (apply 成直角三点不共线; auto).
    apply invert_one_side, out_one_side; Col.
  }
  assert(HSac' : 萨凯里四边形 D C J S).
  { repeat split; auto.
      apply 等长的传递性 with A B; Cong.
    apply one_side_transitivity with R.
      apply col_one_side with A; Col; apply par_strict_one_side with B; Par; Col.
    apply 成直角三点不共线 in HPer2; auto; apply invert_one_side, out_one_side; Col.
  }
  assert(HNCol : ~ Col C J S) by (apply (par_strict_not_col_2 D), sac__pars1234, HSac').
  assert(C <> R) by (intro; subst; apply HNCol; Col).
  repeat (split; try assumption).
  - apply 直角边共线点也构成直角2 with R; Col.
  - Cong.
  - apply out_one_side_1 with R; [Col..|Out].
  - apply coplanar_trans_1 with S.
      apply 成直角三点不共线; Perp.
      apply coplanar_perm_22, col_cop__cop with D; Col; Cop.
      Cop.
Qed.

Lemma t22_8__per : forall A B C D R S,
  萨凯里四边形 A B C D ->
  Bet B C R -> Bet A D S ->
  D <> S ->
  Per A S R ->
  Cong R S A B ->
  Per A B C.
Proof.
  intros A B C D R S HSac HR HS HDS HPer HCong.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(HSac' := HSac).
  unfold 萨凯里四边形 in HSac'.
  spliter.
  assert(B <> R) by (intro; treat_equalities; auto).
  assert(HSac' : 萨凯里四边形 A B R S).
  { destruct (t22_8_aux A B C D R S R) as [_ []]; Cong.
    apply out_trivial; intro; treat_equalities; auto.
  }
  apply (直角边共线点也构成直角2 _ _ R); Col.
  apply (t22_7__per _ _ _  S C D); Perp; Cong.
Qed.

Lemma t22_8__acute : forall A B C D R S,
  萨凯里四边形 A B C D ->
  Bet B C R -> Bet A D S ->
  D <> S ->
  Per A S R ->
  Lt A B R S ->
  为锐角 A B C.
Proof.
  intros A B C D R S HSac HR HS HDS HPer Hlt.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  assert(HJ := Hlt).
  apply 长度小于的右交换性 in HJ.
  destruct HJ as [[J []] _].
  assert_diffs.
  assert(J <> R) by (intro; subst J; destruct Hlt; Cong).
  assert(等角 A B C B C D) by (apply sac__conga; auto).
  destruct (t22_8_aux A B C D R S J) as [HCR [HSac1 [HSac2 [HOS HCop]]]]; [Out; Cong..|].
  apply (acute_lea_acute _ _ _ B C D); Lea.
  apply (acute_chara _ _ _ R); auto.
  assert(等角 A B J B J S) by (apply sac__conga; auto).
  assert(等角 D C J C J S) by (apply sac__conga; auto).
  assert_diffs.
  assert(HPar1 := sac__pars1234 A B J S HSac1).
  assert(HPar2 := sac__pars1423 D C J S HSac2).
  assert(HNCol1 : ~ Col B J S) by (apply (par_strict_not_col_2 A), HPar1).
  assert(TS C J D R).
  { apply (l9_8_2 _ _ S).
      apply par_strict_not_col_2 in HPar2; apply invert_two_sides, bet__ts; Col.
    apply l12_6; Par.
  }
  assert (TS J B C S).
  { assert (HTS : TS J B R S) by (apply l9_2, bet__ts; Col).
    apply (l9_8_2 _ _ R); trivial.
    apply two_sides_not_col in HTS.
    apply invert_one_side, out_one_side; [Col|Out].
  }
  assert (HNCol2 : ~ Col J B C) by (apply two_sides_not_col with S; auto).
  apply (sams_lta2_suma2__lta A B J J B C _ _ _ D C J J C R); [..|和角].
  - apply (conga_preserves_lta S J B S J C); 等角.
    split.
      apply inangle__lea; Side.
    intro Habs.
    apply HNCol2, out_col, (conga_os__out S); Side.

  - apply (conga_preserves_lta C B J J C R); 等角.
    apply l11_41; Col.

  - apply os_ts__sams; trivial.
    apply par_strict_all_one_side with S; Col.
    apply sac__pars1234, HSac2.

  - exists C.
    repeat (split; 等角); [|Cop].
    assert(HPar3 := sac__pars1423 A B J S HSac1).
    apply l9_9, (l9_8_2 _ _ S); [|Side].
    apply l9_2, (l9_8_2 _ _ R).
      apply l9_2, invert_two_sides, bet__ts; Col.
      apply out_one_side; [Col|Out].
Qed.

Lemma t22_8__obtuse : forall A B C D R S,
  萨凯里四边形 A B C D ->
  Bet B C R -> Bet A D S ->
  D <> S ->
  Per A S R ->
  Lt R S A B ->
  为钝角 A B C.
Proof.
  intros A B C D R S HSac HR HS HDS HPer Hlt.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  assert(HI := l5_5_1 S R A B).
  destruct HI as [I []]; Le.
  assert_diffs.
  assert(HPar := sac__pars1423 A B C D HSac).
  assert(R <> I) by (intro; subst I; destruct Hlt; Cong).
  assert(R <> S) by (intro; apply HPar; exists R; subst; split; Col).
  assert(等角 A B C B C D) by (apply sac__conga; auto).
  destruct (t22_8_aux A B C D R S I) as [HCR [HSac1 [HSac2 [HOS HCop]]]]; [Out; Cong..|].
  apply (lea_obtuse_obtuse _ _ _ B C D); [|apply 等角小于等于自己; 等角].
  apply (obtuse_chara _ _ _ R); auto.
  assert(等角 A B I B I S) by (apply sac__conga; auto).
  assert(等角 D C I C I S) by (apply sac__conga; auto).
  assert_diffs.
  assert(HPar1 := sac__pars1234 A B I S HSac1).
  assert(HPar2 := sac__pars1423 D C I S HSac2).
  assert(HOS1 : OS C R S D).
  { apply one_side_symmetry, col_one_side with B; Col.
    apply par_strict_all_one_side with A; Par; Col.
  }
  assert(HNCol1 := one_side_not_col123 C R S D HOS1).
  assert(HNCol2 : ~ Col B C I) by (intro; apply HNCol1; ColR).
  assert(HTS : TS C R I D).
  { apply l9_2, (l9_8_2 _ _ S); Side.
    apply invert_two_sides, bet__ts; Col.
  }
  apply(sams_lta2_suma2__lta456 I C R _ _ _ D C I I B C _ _ _ A B I).
  - apply 角度小于的左交换性, l11_41; Col.

  - assert(OS R S C B) by (apply out_one_side; Out; Col).
    apply (conga_preserves_lta S I C S I B); 等角.
    split.
    { exists C.
      split; 等角.
      apply os2__inangle; Side.
      apply one_side_transitivity with R.
      - apply par_strict_not_col_2 in HPar1.
        apply out_one_side; Out; Col.
      - apply invert_one_side, out_one_side; Out; Col.
    }
    intro Habs.
    apply conga_os__out in Habs; trivial.
    apply HNCol2; Col.

  - apply os_ts__sams; trivial.
    apply one_side_transitivity with S; Side.
    apply two_sides_not_col in HTS.
    apply out_one_side; Out; Col.

  - 和角.

  - exists A.
    repeat (split; 等角); [|Cop].
    assert (OS B C A S) by (apply par_strict_all_one_side with D; Par; Col).
    apply l9_9, l9_2, (l9_8_2 _ _ S); Side.
    repeat split; Col.
      intro; apply (one_side_not_col124 B C A S); Col.
    exists R; split; Col.
Qed.

Lemma t22_8__cong : forall A B C D R S,
  萨凯里四边形 A B C D -> Bet B C R -> Bet A D S ->
  D <> S -> Per A S R -> Per A B C -> Cong R S A B.
Proof.
  intros A B C D R S HSac.
  intros.
  elim(等长的决定性 R S A B); auto.
  intro.
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  exfalso.
  apply (nlta A B C).
  destruct(长度小于等于的决定性 R S A B).
  - apply obtuse_per__lta; auto.
    apply (t22_8__obtuse _ _ _ D R S); auto.
    split; auto.

  - apply acute_per__lta; auto.
    apply (t22_8__acute _ _ _ D R S); auto.
    split; Cong.
Qed.

Lemma t22_8__lt1256 : forall A B C D R S,
  萨凯里四边形 A B C D ->
  Bet B C R -> Bet A D S ->
  D <> S ->
  Per A S R -> 为锐角 A B C ->
  Lt A B R S.
Proof.
  intros A B C D R S HSac.
  intros.
  assert_diffs.
  destruct(等长的决定性 R S A B).
  { exfalso.
    apply (nlta A B C), acute_per__lta; auto.
    apply (t22_8__per _ _ _ D R S); auto.
  }
  destruct(长度小于等于的决定性 R S A B); [|split; Cong].
  exfalso.
  apply (nlta A B C), acute_obtuse__lta; auto.
  apply (t22_8__obtuse _ _ _ D R S); auto.
  split; auto.
Qed.

Lemma t22_8__lt5612 : forall A B C D R S,
  萨凯里四边形 A B C D ->
  Bet B C R -> Bet A D S ->
  D <> S ->
  Per A S R -> 为钝角 A B C ->
  Lt R S A B.
Proof.
  intros A B C D R S HSac.
  intros.
  assert_diffs.
  destruct(等长的决定性 R S A B).
  { exfalso.
    apply (nlta A B C).
    apply obtuse_per__lta; auto.
    apply (t22_8__per _ _ _ D R S); auto.
  }
  destruct(长度小于等于的决定性 R S A B).
    split; auto.
  exfalso.
  apply (nlta A B C).
  apply acute_obtuse__lta; auto.
  apply (t22_8__acute _ _ _ D R S); auto.
  split; Cong.
Qed.


Lemma t22_9_aux : forall N M P Q R S,
  Lambert四边形 N M P Q -> Lambert四边形 N M R S ->
  Bet M P R -> Bet N Q S ->
  (Per S R M <-> Per Q P M) /\ (为锐角 S R M <-> 为锐角 Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  destruct(两点重合的决定性 Q S).
  { assert (HPar := lam__pars1234 N M P Q HLamP).
    unfold Lambert四边形 in *.
    spliter.
    treat_equalities.
    assert(P = R); [|subst; split; reflexivity].
    apply (l6_21_两线交点的唯一性 M P Q P); Col.
      apply (par_strict_not_col_2 N), HPar.
    apply 等价共线CAB, cop_per2__col with N; Perp.
    apply coplanar_perm_5, col_cop__cop with M; Col; Cop.
  }
  assert(HP' := 构造对称点 P M).
  destruct HP' as [P' HP'].
  apply M是AB中点则M是BA中点 in HP'.
  assert(HQ' := 构造对称点 Q N).
  destruct HQ' as [Q' HQ'].
  apply M是AB中点则M是BA中点 in HQ'.
  assert(HR' := 构造对称点 R M).
  destruct HR' as [R' HR'].
  apply M是AB中点则M是BA中点 in HR'.
  assert(HS' := 构造对称点 S N).
  destruct HS' as [S' HS'].
  apply M是AB中点则M是BA中点 in HS'.
  assert(HSacR := lam6534_mid2__sac S' R' R S M N HLamR HR' HS').
  assert(HSacP := lam6534_mid2__sac Q' P' P Q M N HLamP HP' HQ').
  assert(Cong S' R' R S /\ Cong Q' P' P Q) by (unfold 萨凯里四边形 in *; spliter; split; auto).
  unfold Lambert四边形 in *.
  spliter.
  assert(HCongaR := sac__conga S' R' R S HSacR).
  assert(HCongaQ := sac__conga Q' P' P Q HSacP).
  assert(Bet P' P R) by (apply (中间性的外传递性1 _ M); Between).
  assert(Bet Q' Q S) by (apply (中间性的外传递性1 _ N); Between).
  assert(Bet R' P R) by (apply (中间性的内传递性2 _ M); Between).
  assert(Bet S' Q S) by (apply (中间性的内传递性2 _ N); Between).
  assert_diffs.
  assert(Per Q' S R) by (apply (l8_3_直角边共线点也构成直角1 N); auto; ColR).
  assert(Per S' Q P) by (apply (l8_3_直角边共线点也构成直角1 N); auto; ColR).
  assert(S' <> Q) by (intro; treat_equalities; auto).
  repeat split; intro.
  - apply (直角边共线点也构成直角2 _ _ P'); Col.
    apply (l11_17_等于直角的角是直角 Q' P' P); 等角.
    apply (t22_8__per _ _ _ Q R S); auto.
    apply 等长的对称性.
    apply (等长的传递性 _ _ S' R'); auto.
    apply (等长的传递性 _ _ P Q); auto.
    apply (t22_7__cong _ _ R S); Perp.
    apply (l11_17_等于直角的角是直角 S R R'); 等角.
    apply (直角边共线点也构成直角2 _ _ M); Col.

  - apply (直角边共线点也构成直角2 _ _ R'); Col.
    apply (l11_17_等于直角的角是直角 S' R' R); 等角.
    apply (t22_7__per _ _ _ S P Q); Perp.
    apply 等长的对称性.
    apply (等长的传递性 _ _ Q' P'); auto.
    apply (等长的传递性 _ _ R S); auto.
    apply (t22_8__cong _ _ P Q); auto.
    apply (l11_17_等于直角的角是直角 Q P P'); 等角.
    apply (直角边共线点也构成直角2 _ _ M); Col.

  - apply (acute_conga__acute Q' P' P).
    { apply (t22_8__acute _ _ _ Q R S); auto.
      apply (等长保持小于关系 P Q S' R'); Cong.
      apply (t22_7__lt5612 _ _ R S); Perp.
      apply (acute_conga__acute S R M); auto.
      apply (l11_10 S R R' S' R' R); [等角|Out..].
    }
    apply (l11_10 Q' P' P Q P P'); [等角|Out..].

  - apply (acute_conga__acute S' R' R).
    { apply (t22_7__acute _ _ _ S P Q); Perp.
      apply (等长保持小于关系 Q' P' R S); Cong.
      apply (t22_8__lt1256 _ _ P Q); auto.
      apply (acute_conga__acute Q P M); auto.
      apply (l11_10 Q P P' Q' P' P); [等角|Out..].
    }
    apply (l11_10 S' R' R S R R'); [等角|Out..].
Qed.

Lemma t22_9__per : forall N M P Q R S,
  Lambert四边形 N M P Q -> Lambert四边形 N M R S ->
  Bet M P R -> Bet N Q S ->
  (Per S R M <-> Per Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  apply (t22_9_aux N); assumption.
Qed.

Lemma t22_9__acute : forall N M P Q R S,
  Lambert四边形 N M P Q -> Lambert四边形 N M R S ->
  Bet M P R -> Bet N Q S ->
  (为锐角 S R M <-> 为锐角 Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  apply (t22_9_aux N); assumption.
Qed.

Lemma t22_9__obtuse : forall N M P Q R S,
  Lambert四边形 N M P Q -> Lambert四边形 N M R S ->
  Bet M P R -> Bet N Q S ->
  (为钝角 S R M <-> 为钝角 Q P M).
Proof.
  intros N M P Q R S HLamP HLamR HR HS.
  destruct (t22_9_aux N M P Q R S HLamP HLamR HR HS) as [[][]].
  unfold Lambert四边形 in HLamP.
  unfold Lambert四边形 in HLamR.
  spliter.
  split; intro.
  - destruct(angle_partition Q P M) as [|[|]]; auto; exfalso; apply (nlta S R M).
      apply acute_obtuse__lta; auto.
      apply obtuse_per__lta; auto.
  - destruct(angle_partition S R M) as [|[|]]; auto; exfalso; apply (nlta Q P M).
      apply acute_obtuse__lta; auto.
      apply obtuse_per__lta; auto.
Qed.

(** The two following lemmas come from Theorem 22.4 *)

Lemma cong2_lam2__cong_conga : forall N M P Q N' M' P' Q',
  Lambert四边形 N M P Q -> Lambert四边形 N' M' P' Q' ->
  Cong N Q N' Q' -> Cong P Q P' Q' ->
  Cong N M N' M' /\ 等角 M P Q M' P' Q'.
Proof.
  intros N M P Q N' M' P' Q' HLam HLam' HCong1 HCong2.
  assert(严格平行 N Q M P) by (apply lam__pars1423, HLam).
  assert(严格平行 N M P Q) by (apply lam__pars1234, HLam).
  assert(严格平行 N' Q' M' P') by (apply lam__pars1423, HLam').
  assert(严格平行 N' M' P' Q') by (apply lam__pars1234, HLam').
  unfold Lambert四边形 in *.
  spliter.
  assert(~ Col N M P) by (apply 成直角三点不共线; auto).
  assert(~ Col M N Q) by (apply 成直角三点不共线; auto).
  assert(~ Col M' N' Q') by (apply 成直角三点不共线; auto).
  assert_diffs.
  assert(HSAS := l11_49 N Q P N' Q' P').
  destruct HSAS as [HCong3 [HConga1 HConga2]]; Cong; [等角|].
  assert(等角 M N P M' N' P').
  { apply (l11_22b _ _ _ Q _ _ _ Q').
    repeat (split; 等角); Side.
  }
  assert(HAAS := l11_50_2 P N M P' N' M').
  destruct HAAS as [HCong4 [HCong5 HCong6]]; [Col|等角..|Cong|].
  split; trivial.
  apply (l11_22a _ _ _ N _ _ _ N').
  repeat (split; Side; 等角).
Qed.

Lemma cong2_sac2__cong : forall A B C D A' B' C' D',
  萨凯里四边形 A B C D -> 萨凯里四边形 A' B' C' D' ->
  Cong A B A' B' -> Cong A D A' D' ->
  Cong B C B' C'.
Proof.
  intros A B C D A' B' C' D' HSac HSac' HCongB HCongL.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  unfold 萨凯里四边形 in *.
  spliter.
  destruct (l11_49 B A D B' A' D') as [HCongD [HConga1 HConga2]]; Cong; 等角.
  destruct (l11_49 B D C B' D' C'); Cong;
  [|apply (等长的传递性 _ _ A B); Cong; apply (等长的传递性 _ _ A' B'); Cong].
  apply (l11_22b _ _ _ A _ _ _ A').
  repeat (split; 等角); Side.
Qed.

Lemma sac__perp1214 : forall A B C D, 萨凯里四边形 A B C D -> Perp A B A D.
Proof.
  intros A B C D HSac.
  assert (Hdiff := sac_distincts A B C D HSac).
  unfold 萨凯里四边形 in HSac; spliter.
  apply 垂直的左交换性, 直角转L形垂直; auto.
Qed.

Lemma sac__perp3414 : forall A B C D, 萨凯里四边形 A B C D -> Perp C D A D.
Proof.
  intros A B C D HSac.
  apply 垂直的交换性, (sac__perp1214 _ _ B), sac_perm; trivial.
Qed.

Lemma cop_sac2__sac : forall A B C D E F,
  萨凯里四边形 A B C D -> 萨凯里四边形 A B E F -> D<>F -> 共面 A B D F -> 萨凯里四边形 D C E F.
Proof.
  intros A B C D E F HSac HSac2 HDF HCop.
  assert(HPerp := sac__perp1214 _ _ _ _ HSac); assert(HPerp2 := sac__perp1214 _ _ _ _ HSac2).
  assert(HPerp3 := sac__perp3414 _ _ _ _ HSac); assert(HPerp4 := sac__perp3414 _ _ _ _ HSac2).
  assert(Col A D F).
    apply cop_perp2__col with A B; Perp.
  assert(Hdiff := sac_distincts _ _ _ _ HSac).
  assert(Hdiff2 := sac_distincts _ _ _ _ HSac2).
  unfold 萨凯里四边形 in *; spliter; repeat split.
  - apply L形垂直转直角1, 与垂线共线之线也为垂线1 with D A; Col; Perp.
  - apply L形垂直转直角1, 垂直的对称性, 与垂线共线之线也为垂线1 with F A; Col; Perp.
  - apply 等长的传递性 with A B; Cong.
  - apply one_side_transitivity with B.
      apply col_one_side with A; Col; Side.
    apply invert_one_side, col_one_side with A; Col; Side.
Qed.

(** This comes from Martin's proof in Theorem 22.10 *)

Lemma three_hypotheses_aux : forall A B C D M N A' B' C' D' M' N',
  萨凯里四边形 A B C D -> 萨凯里四边形 A' B' C' D' ->
  中点 M B C -> 中点 M' B' C' -> 中点 N A D -> 中点 N' A' D' ->
  Le M N M' N' ->
  (Per A B C <-> Per A' B' C') /\ (为锐角 A B C <-> 为锐角 A' B' C').
Proof.
  intros A B C D M N A' B' C' D' M' N' HSac HSac' HM HM' HN HN' Hle.
  assert(HLam1 := mid2_sac__lam6534 A B C D M N HSac HM HN).
  assert(HLam1' := mid2_sac__lam6534 A' B' C' D' M' N' HSac' HM' HN').
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  spliter.
  assert(HNCol1 : ~ Col C D A) by (apply (par_strict_not_col_3 _ B), sac__pars1234, HSac).
  assert_diffs.
  rename H into HA'B'.
  assert(HH := 由一点往一方向构造等长线段_3 N D N' D').
  destruct HH as [H []]; auto.
  assert(Col A D H) by ColR.
  assert(G0 := l10_15 A D H C).
  destruct G0 as [G0 []]; Col.
  assert_diffs.
  assert(HG := 由一点往一方向构造等长线段_3 H G0 C' D').
  destruct HG as [G []]; auto.
  assert_diffs.
  assert(OS N D C G).
  { apply invert_one_side.
    apply (col_one_side _ A); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ G0); auto.
    apply(l9_19 _ _ _ _ H); Col.
    split; auto.
    apply one_side_not_col124 with C; assumption.
  }
  assert(Perp A D H G) by (apply (垂线共线点也构成垂直2 _ _ _ G0); Perp; Col).
  clear dependent G0.
  assert(HNCol2 : ~ Col M N H).
  { unfold Lambert四边形 in HLam1.
    spliter.
    apply 成直角三点不共线; auto.
    apply (直角边共线点也构成直角2 _ _ D); auto; ColR.
  }
  assert (HCop : 共面 A D M G).
  { apply coplanar_trans_1 with C; Col.
      apply coplanar_perm_12, col_cop__cop with B; Col; Cop.
      apply coplanar_perm_5, col_cop__cop with N; Col; Cop.
  }
  assert (HNCol3 : ~ Col M N G).
  { unfold Lambert四边形 in HLam1.
    spliter.
    apply (one_side_not_col123 _ _ _ H).
    apply l12_6.
    apply (par_not_col_strict _ _ _ _ H); Col.
    apply (l12_9 _ _ _ _ A D); Cop; [|Perp].
    apply 垂直的右交换性; apply (垂线共线点也构成垂直2 _ _ _ N); Col; Perp.
  }
  assert_diffs.
  assert(A <> H) by (intro; subst H; assert(Habs := l6_4_1 D A N); destruct Habs; Between).
  assert(Col H A N) by ColR.
  assert(HL := l8_18_过一点垂线之垂点的存在性 M N G).
  destruct HL as [L []]; auto.
  assert(HNCol4 : ~ Col M A D).
    apply sac__pars1423 in HSac; apply (par_not_col B C); Par; Col.
  assert(HLam2 : Lambert四边形 N L G H).
  { assert(Per N H G).
    { apply (l8_3_直角边共线点也构成直角1 A); Col.
      apply (L形垂直转直角1); auto.
      apply 垂直的交换性.
      apply (垂线共线点也构成垂直1 _ D); Col.
    }
    assert(~ Col N H G) by (apply 成直角三点不共线; auto).
    assert(Per A N M).
    { apply L形垂直转直角1, 垂直的左交换性, (垂线共线点也构成垂直1 _ D); Col.
      apply (mid2_sac__perp_lower _ B C); auto.
    }
    assert(Per L N H) by (apply (l8_3_直角边共线点也构成直角1 M); Col; apply (直角边共线点也构成直角2 _ _ A); Col; Perp).
    assert(N <> L).
    { intro.
      subst L.
      assert(Col G H N); Col.
      apply cop_per2__col with M; [|Perp..|apply (l8_3_直角边共线点也构成直角1 A); Col].
      apply coplanar_pseudo_trans with A D M; Cop; Col.
    }
    repeat split; auto.
      intro; subst; apply HNCol3; assumption.
      apply L形垂直转直角1, 垂直的左交换性, (垂线共线点也构成垂直1 _ M); Col; Perp.
      apply coplanar_pseudo_trans with A D M; [Col|Cop| |Cop..].
      exists N; left; split; Col.
  }
  assert(严格平行 N D M C) by (apply lam__pars1423, HLam1).
  assert(Bet N M L).
  { destruct (cong2_lam2__cong_conga N' M' C' D' N L G H); Cong.
    apply l6_13_1; [|apply (l5_6_等长保持小于等于关系 M N M' N'); Cong].
    apply (col_one_side_out _ D); Col.
    apply (one_side_transitivity _ _ _ G).
      apply (one_side_transitivity _ _ _ C); auto; apply l12_6; auto.
    apply (col_one_side _ H); [ColR..|].
    apply one_side_symmetry, l12_6, lam__pars1423, HLam2.
  }
  assert(HNCol5 : ~ Col N M C) by (unfold Lambert四边形 in HLam1; spliter; apply 成直角三点不共线; auto).
  assert(HNCol6 : ~ Col N D M) by (apply (par_strict_not_col_1 _ _ _ C); auto).
  assert (共面 M C D A).
    apply pars__coplanar, par_strict_col_par_strict with N; Col; Par.
  assert(HK : exists K, Col K M C /\ Bet G K H).
  { elim(两点重合的决定性 L M).
    { intro.
      subst L.
      exists G.
      split; Between.
      apply 等价共线ACB.
      unfold Lambert四边形 in *.
      spliter.
      apply cop_per2__col with N; Perp.
      apply coplanar_pseudo_trans with A D M; Col; Cop.
    }
    intro.
    assert(HNCol7 : ~ Col L M C) by (intro; apply HNCol5; ColR).
    assert(Hts : TS M C G H); [|unfold TS in Hts; spliter; auto].
    apply (l9_8_2 _ _ L).
    - apply l9_2.
      apply (l9_8_2 _ _ N).
        repeat split; Col; exists M; Col.
      apply l12_6, (par_strict_col_par_strict _ _ _ D); Par; ColR.
    - apply l12_6, (par_not_col_strict _ _ _ _ L); Col.
      unfold Lambert四边形 in *.
      spliter.
      apply (l12_9 _ _ _ _ M N); Perp; [Cop..|].
      apply coplanar_pseudo_trans with A D M; Col; Cop.
  }
  destruct HK as [K []].
  assert(HNCol7 : ~ Col H M C) by (apply (par_not_col N D); Col).
  assert(K <> H) by (intro; subst K; auto).
  assert(严格平行 N M C D) by (apply lam__pars1234, HLam1).
  assert(HNCol8 : ~ Col N C D) by (apply (par_strict_not_col_2 M); Par).
  assert(严格平行 M N H K).
  { apply par_strict_col_par_strict with G; Col.
    apply par_strict_comm, par_strict_symmetry, par_strict_col_par_strict with L; Col.
    apply par_strict_symmetry, lam__pars1234, HLam2.
  }
  assert(HNCol9 : ~ Col N H K) by (apply (par_strict_not_col_2 M); auto).
  assert(HMout : Out M C K).
  { apply (col_one_side_out _ N); Col.
    apply (one_side_transitivity _ _ _ D).
      apply l12_6; Par.
    apply (one_side_transitivity _ _ _ H).
      apply invert_one_side; apply out_one_side; Col.
    apply l12_6; auto.
  }
  assert_diffs.
  assert(HLam3 : Lambert四边形 N M K H).
  { unfold Lambert四边形 in *.
    spliter.
    repeat split; auto.
      apply (l8_3_直角边共线点也构成直角1 L); Col.
      apply (直角边共线点也构成直角2 _ _ G); Col.
      apply (直角边共线点也构成直角2 _ _ C); Col.
      apply coplanar_perm_7, pars__coplanar; assumption.
  }
  assert(HConga := sac__conga A B C D HSac).
  assert(等角 A' B' C' H G L).
  { apply (角等的传递性 _ _ _ M' C' D').
      apply (l11_10 A' B' C' B' C' D'); [apply sac__conga, HSac'|Out..].
    apply 等角的右交换性, (cong2_lam2__cong_conga N' _ _ _ N); Cong.
  }
  assert((Bet M C K -> Bet N D H) /\ (Bet M K C -> Bet N H D)).
  { destruct(两点重合的决定性 D H) as [|HDH].
      subst; split; intro; Between.
    assert(HPar : Par C D K H).
    { unfold Lambert四边形 in *.
      spliter.
      apply (l12_9 _ _ _ _ N D); [|Cop..|Perp|].
        apply os__coplanar, par_strict_all_one_side with M; Par; Col.
      apply 垂直的交换性, (垂线共线点也构成垂直1 _ G); Col; apply (垂线共线点也构成垂直2 _ _ _ A); Perp; Col.
    }
    assert (严格平行 C D K H).
    { destruct HPar; auto.
      exfalso.
      unfold Lambert四边形 in *.
      spliter.
      apply HDH.
      apply (l8_18_过一点垂线之垂点的唯一性 C D N); Col.
        Perp.
        ColR.
      apply (垂线共线点也构成垂直1 _ H); auto; [|ColR].
      apply 垂直的左交换性, (垂线共线点也构成垂直1 _ G); Perp; ColR.
    }
    split; intro; apply 中间性的对称性, not_out_bet; Col; intro.
    - assert(Out C K M); [|assert(Habs := l6_4_1 K M C); destruct Habs; Between].
      apply (col_one_side_out _ D); Col.
      apply (one_side_transitivity _ _ _ N); [|Side].
      apply (one_side_transitivity _ _ _ H); [Side|apply invert_one_side; apply out_one_side; Col].
    - assert(Out K C M); [|assert(Habs := l6_4_1 C M K); destruct Habs; Between].
      apply (col_one_side_out _ H); Col.
      apply (one_side_transitivity _ _ _ N); [|Side].
      apply (one_side_transitivity _ _ _ D); [Side|apply invert_one_side; apply out_one_side; Col].
  }
  spliter; split; split; intro.

  - apply (l11_17_等于直角的角是直角 L G H); 等角.
    apply (t22_9__per N _ K M); try (apply lam_perm); Between.
    apply 直角的对称性.
    assert(Per D C M).
    { apply (l11_17_等于直角的角是直角 A B C); auto.
      apply (l11_10 A B C D C B); [等角|Out..].
    }
    destruct HMout as [_ [_ [HMCK|HMKC]]].
      apply (t22_9__per N _ C D); auto.
      apply (t22_9__per N _ _ _ C D); auto.

  - apply (l11_17_等于直角的角是直角 D C M).
    { assert(Per H K M).
        apply 直角的对称性, (t22_9__per N _ _ _ G L); try (apply lam_perm); Between.
        apply (l11_17_等于直角的角是直角 A' B' C'); 等角.
      destruct HMout as [_ [_ [HMCK|HMKC]]].
        apply (t22_9__per N _ _ _ K H); auto.
        apply (t22_9__per N _ K H); auto.
    }
    apply (l11_10 D C B A B C); [等角|Out..].

  - apply (acute_conga__acute L G H); 等角.
    apply (t22_9__acute N _ K M); try (apply lam_perm); Between.
    apply acute_sym.
    assert(为锐角 D C M).
    { apply (acute_conga__acute A B C); auto.
      apply (l11_10 A B C D C B); [等角|Out..].
    }
    destruct HMout as [_ [_ [HMCK|HMKC]]].
      apply (t22_9__acute N _ C D); auto.
      apply (t22_9__acute N _ _ _ C D); auto.

  - apply (acute_conga__acute D C M).
    { assert(为锐角 H K M).
        apply acute_sym.
          apply (t22_9__acute N _ _ _ G L); try (apply lam_perm); Between.
          apply (acute_conga__acute A' B' C'); 等角.
      destruct HMout as [_ [_ [HMCK|HMKC]]].
        apply (t22_9__acute N _ _ _ K H); auto.
        apply (t22_9__acute N _ K H); auto.
    }
    apply (l11_10 D C B A B C); [等角|Out..].
Qed.


(** 萨凯里四边形's three hypotheses *)

Definition hypothesis_of_right_saccheri_quadrilaterals := forall A B C D, 萨凯里四边形 A B C D -> Per A B C.

Definition hypothesis_of_acute_saccheri_quadrilaterals := forall A B C D, 萨凯里四边形 A B C D -> 为锐角 A B C.

Definition hypothesis_of_obtuse_saccheri_quadrilaterals := forall A B C D, 萨凯里四边形 A B C D -> 为钝角 A B C.

Lemma per_sac__rah : forall A B C D,
  萨凯里四边形 A B C D -> Per A B C -> hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(HM := 中点的存在性 B C).
  assert(HM' := 中点的存在性 B' C').
  assert(HN := 中点的存在性 A D).
  assert(HN' := 中点的存在性 A' D').
  destruct HM as [M].
  destruct HM' as [M'].
  destruct HN as [N].
  destruct HN' as [N'].
  elim(长度小于等于的决定性 M N M' N');
  intro Hle;
  [assert(Haux := three_hypotheses_aux A B C D M N A' B' C' D' M' N')
  |assert(Haux := three_hypotheses_aux A' B' C' D' M' N' A B C D M N)];
  destruct Haux as [[] _]; auto.
Qed.

Lemma acute_sac__aah : forall A B C D,
  萨凯里四边形 A B C D -> 为锐角 A B C -> hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(HM := 中点的存在性 B C).
  assert(HM' := 中点的存在性 B' C').
  assert(HN := 中点的存在性 A D).
  assert(HN' := 中点的存在性 A' D').
  destruct HM as [M].
  destruct HM' as [M'].
  destruct HN as [N].
  destruct HN' as [N'].
  elim(长度小于等于的决定性 M N M' N');
  intro Hle;
  [assert(Haux := three_hypotheses_aux A B C D M N A' B' C' D' M' N')
  |assert(Haux := three_hypotheses_aux A' B' C' D' M' N' A B C D M N)];
  destruct Haux as [_ []]; auto.
Qed.

Lemma obtuse_sac__oah : forall A B C D,
  萨凯里四边形 A B C D -> 为钝角 A B C -> hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros A B C D HSac HPer A' B' C' D' HSac'.
  assert(Hdiff := sac_distincts A B C D HSac).
  assert(Hdiff' := sac_distincts A' B' C' D' HSac').
  spliter.
  elim(angle_partition A' B' C'); auto.
  { intro Hacute'.
    exfalso.
    apply (nlta A B C).
    apply (acute_obtuse__lta); auto.
    assert(aah := acute_sac__aah A' B' C' D' HSac' Hacute').
    apply (aah _ _ _ D); auto.
  }
  intro HUn.
  destruct HUn as [HPer'|]; auto.
  exfalso.
  apply (nlta A B C).
  apply (obtuse_per__lta); auto.
  assert(rah := per_sac__rah A' B' C' D' HSac' HPer').
  apply (rah _ _ _ D); auto.
Qed.

Lemma per__ex_saccheri : forall A B D, Per B A D -> A <> B -> A <> D ->
  exists C, 萨凯里四边形 A B C D.
Proof.
  intros A B D HPer HAB HBD.
  assert (HNCol : ~ Col B A D) by (apply 成直角三点不共线; auto).
  destruct (l10_15 A D D B) as [C0 []]; Col.
  assert(~ Col A D C0) by (apply (one_side_not_col123 _ _ _ B); Side).
  assert_diffs.
  destruct (由一点往一方向构造等长线段_3 D C0 A B) as [C []]; auto.
  exists C.
  repeat split; Cong.
    apply (直角边共线点也构成直角2 _ _ C0); Col; Perp.
    apply invert_one_side; apply (out_out_one_side _ _ _ C0); Side.
Qed.

Lemma ex_saccheri : exists A B C D, 萨凯里四边形 A B C D.
Proof.
  destruct 防降维公理_老版本 as [A [D [E]]].
  assert(HNCol : ~ Col A D E) by (unfold Col; assumption).
  destruct (l10_15 A D A E) as [B []]; Col.
  assert(~ Col A D B) by (apply (one_side_not_col123 _ _ _ E); Side).
  assert_diffs.
  destruct (per__ex_saccheri A B D) as [C HSac]; Perp.
  exists A; exists B; exists C; exists D; trivial.
Qed.

Lemma ex_lambert : exists A B C D, Lambert四边形 A B C D.
Proof.
  destruct ex_saccheri as [D [C [C' [D' HSac]]]].
  destruct (中点的存在性 D D') as [A HA].
  destruct (中点的存在性 C C') as [B HB].
  exists A, B, C, D.
  apply mid2_sac__lam6521 with C' D'; trivial.
Qed.

Lemma saccheri_s_three_hypotheses :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  destruct (angle_partition A B C) as [|HUn]; [auto..| |right; destruct HUn].
    left; apply (acute_sac__aah A B C D); trivial.
    left; apply (per_sac__rah A B C D); trivial.
    right; apply (obtuse_sac__oah A B C D); trivial.
Qed.

Lemma not_aah :
  hypothesis_of_right_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals -> ~ hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros HUn aah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(为锐角 A B C) by (apply (aah _ _ _ D); auto).
  destruct HUn as [rah|oah].
  - apply (acute_per__lta); auto.
    apply (rah _ _ _ D); auto.

  - apply (acute_obtuse__lta); auto.
    apply (oah _ _ _ D); auto.
Qed.

Lemma not_rah :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_obtuse_saccheri_quadrilaterals -> ~ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros HUn rah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(Per A B C) by (apply (rah _ _ _ D); auto).
  destruct HUn as [aah|oah].
  - apply (acute_per__lta); auto.
    apply (aah _ _ _ D); auto.

  - apply (obtuse_per__lta); auto.
    apply (oah _ _ _ D); auto.
Qed.

Lemma not_oah :
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals -> ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros HUn oah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  apply (nlta A B C).
  assert(为钝角 A B C) by (apply (oah _ _ _ D); auto).
  destruct HUn as [aah|rah].
  - apply (acute_obtuse__lta); auto.
    apply (aah _ _ _ D); auto.

  - apply (obtuse_per__lta); auto.
    apply (rah _ _ _ D); auto.
Qed.


Lemma lam_per__rah : forall A B C D,
  Lambert四边形 A B C D -> (Per B C D <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := 构造对称点 C B).
  destruct HC' as [C'].
  assert(HD' := 构造对称点 D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (per_sac__rah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert四边形 in HLam.
    spliter.
    apply 直角的对称性.
    apply (l8_3_直角边共线点也构成直角1 B); Col.

  - intro rah.
    apply (l8_3_直角边共线点也构成直角1 C'); Col ;[|unfold Lambert四边形 in HLam; spliter; assert_diffs; auto].
    apply 直角的对称性.
    apply (rah _ _ _ D').
    apply (lam6521_mid2__sac _ _ _ _ B A); auto.
Qed.

Lemma lam_acute__aah : forall A B C D,
  Lambert四边形 A B C D -> (为锐角 B C D <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := 构造对称点 C B).
  destruct HC' as [C'].
  assert(HD' := 构造对称点 D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (acute_sac__aah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert四边形 in HLam.
    spliter.
    assert_diffs.
    apply (acute_conga__acute B C D); auto.
    apply 等角的左交换性, out2__conga; [apply out_trivial|apply l6_6, bet_out]; Between.

  - intro aah.
    apply (acute_conga__acute D C C'); auto.
      apply (aah _ _ _ D'); apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert四边形 in HLam.
    spliter.
    assert_diffs.
    apply 等角的左交换性, out2__conga; [apply bet_out|apply out_trivial]; Between.
Qed.

Lemma lam_obtuse__oah : forall A B C D,
  Lambert四边形 A B C D -> (为钝角 B C D <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C D HLam.
  assert(HC' := 构造对称点 C B).
  destruct HC' as [C'].
  assert(HD' := 构造对称点 D A).
  destruct HD' as [D'].
  split.
  - intro.
    apply (obtuse_sac__oah D C C' D').
      apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert四边形 in HLam.
    spliter.
    assert_diffs.
    apply (conga_obtuse__obtuse B C D); auto.
    apply 等角的左交换性, out2__conga; [apply out_trivial|apply l6_6, bet_out]; Between.

  - intro oah.
    apply (conga_obtuse__obtuse D C C'); auto.
      apply (oah _ _ _ D'); apply (lam6521_mid2__sac _ _ _ _ B A); auto.
    unfold Lambert四边形 in HLam.
    spliter.
    assert_diffs.
    apply 等角的左交换性, out2__conga; [apply bet_out|apply out_trivial]; Between.
Qed.


Lemma t22_11__per : forall A B C D,
  萨凯里四边形 A B C D -> (等角 A B D B D C <-> Per A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (cong_sac__per _ _ _ D); auto.
    unfold 萨凯里四边形 in HSac.
    spliter.
    assert(HSAS := l11_49 A B D C D B).
    destruct HSAS; Cong; 等角.

  - intro HPer.
    apply <- (cong_sac__per A B C D) in HPer; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold 萨凯里四边形 in HSac.
    spliter.
    assert(HSSS := l11_51 A B D C D B).
    destruct HSSS as [_ []]; Cong; 等角.
Qed.

Lemma t22_11__acute : forall A B C D,
  萨凯里四边形 A B C D -> (角度小于 A B D B D C <-> 为锐角 A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (lt_sac__acute _ _ _ D); auto.
    unfold 萨凯里四边形 in HSac.
    spliter.
    apply 长度小于的右交换性.
    apply (t18_18 D _ _ B); Cong.
    apply 角度小于的左交换性; auto.

  - intro Hacute.
    apply <- (lt_sac__acute A B C D) in Hacute; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold 萨凯里四边形 in HSac.
    spliter.
    apply 角度小于的左交换性.
    apply t18_19; Cong.
    apply 长度小于的右交换性; Cong.
Qed.

Lemma t22_11__obtuse : forall A B C D,
  萨凯里四边形 A B C D -> (角度小于 B D C A B D <-> 为钝角 A B C).
Proof.
  intros A B C D HSac.
  split.
  - intro.
    apply (lt_sac__obtuse _ _ _ D); auto.
    unfold 萨凯里四边形 in HSac.
    spliter.
    apply 长度小于的右交换性.
    apply (t18_18 B _ _ D); Cong.
    apply 角度小于的左交换性; auto.

  - intro Hobtuse.
    apply <- (lt_sac__obtuse A B C D) in Hobtuse; trivial.
    assert(Hdiff := sac_distincts A B C D HSac).
    unfold 萨凯里四边形 in HSac.
    spliter.
    apply 角度小于的左交换性.
    apply t18_19; Cong.
    apply 长度小于的右交换性; Cong.
Qed.


Lemma t22_12__rah : forall A B C,
  A <> B -> B <> C -> Per A B C ->
  (和角 B C A C A B A B C <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C HAB HBC HPer.
  destruct (per__ex_saccheri B A C) as [D HSac]; auto.
  assert(HPars1 := sac__pars1423 B A D C HSac).
  assert(HPars2 := sac__pars1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; Side).
  assert_diffs.
  assert(等角 B C D A B C) by (unfold 萨凯里四边形 in HSac; spliter; 等角).
  split.
  - intro.
    apply (per_sac__rah B A D C); auto.
    apply (t22_11__per _ _ _ C); auto.
    apply 等角的左交换性.
    apply (sams2_suma2__conga456 B C A _ _ _ _ _ _ A B C); try (apply sams123231); auto.
      apply os_ts__sams; Side.
    exists D.
    repeat (split; 等角); Side; Cop.

  - intro rah.
    apply (等角保持和角 B C A A C D B C D); try (apply 同角相等); auto.
      exists D; repeat (split; 等角); Side; Cop.
    apply 等角的对称性.
    apply 等角的左交换性.
    apply t22_11__per; auto.
    apply (rah _ _ _ C); auto.
Qed.

Lemma t22_12__aah : forall A B C P Q R,
  Per A B C -> 和角 B C A C A B P Q R ->
  (为锐角 P Q R <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C P Q R HPer HSuma.
  suma.assert_diffs.
  destruct (per__ex_saccheri B A C) as [D HSac]; auto.
  assert(HSac' := HSac).
  unfold 萨凯里四边形 in HSac'.
  spliter.
  assert_diffs.
  assert(HPars1 := sac__pars1423 B A D C HSac).
  assert(HPars2 := sac__pars1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; Side).
  assert(等角 B C D A B C) by 等角.
  split.
  - intro.
    apply (acute_sac__aah B A D C); auto.
    apply (t22_11__acute _ _ _ C); auto.
    apply 角度小于的左交换性.
    apply (sams_lea_lta789_suma2__lta456 B C A _ _ _ P Q R B C A _ _ _ B C D); Lea; 和角.

  - intro aah.
    exists B, C, D.
    split; trivial.
    apply (sams_lea_lta456_suma2__lta B C A C A B _ _ _ B C A A C D); auto.
      apply 任何角小于等于自己; auto.
      apply 角度小于的左交换性; apply t22_11__acute; try (apply (aah _ _ _ C)); auto.
      apply os_ts__sams; Side.
      和角.
Qed.

Lemma t22_12__oah : forall A B C P Q R,
  Per A B C -> 和角 B C A C A B P Q R ->
  (为钝角 P Q R <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C P Q R HPer HSuma.
  suma.assert_diffs.
  destruct (per__ex_saccheri B A C) as [D HSac]; auto.
  assert(HSac' := HSac).
  unfold 萨凯里四边形 in HSac'.
  spliter.
  assert_diffs.
  assert(HPars1 := sac__pars1423 B A D C HSac).
  assert(HPars2 := sac__pars1234 B A D C HSac).
  assert(TS C A B D) by (apply l9_31; Side).
  assert(等角 B C D A B C) by 等角.
  split.
  - intro.
    apply (obtuse_sac__oah B A D C); auto.
    apply (t22_11__obtuse _ _ _ C); auto.
    apply 角度小于的右交换性.
    apply (sams_lea_lta789_suma2__lta456 B C A _ _ _ B C D B C A _ _ _ P Q R); Lea; [|和角].
    apply os_ts__sams; Side.

  - intro oah.
    exists B, C, D.
    split; trivial.
    apply (sams_lea_lta456_suma2__lta B C A A C D _ _ _ B C A C A B); 和角.
      apply 任何角小于等于自己; auto.
      apply 角度小于的右交换性; apply t22_11__obtuse; try (apply (oah _ _ _ C)); auto.
Qed.

Lemma t22_14_aux : forall A B C,
  ~ Col A B C -> 为锐角 A B C -> 为锐角 A C B ->
  exists A', Bet B A' C /\ Per B A' A /\ Per C A' A /\
  等角 B A' A C A' A /\ 等角 A B C A B A' /\ 等角 B C A A' C A /\ TS A A' B C.
Proof.
  intros A B C HNCol HacuteB HacuteC.
  destruct (l8_18_过一点垂线之垂点的存在性 B C A) as [A' [HCol HPerp]]; Col.
  exists A'.
  assert(Out B A' C) by (apply (acute_col_perp__out A); auto).
  assert(Out C A' B) by (apply (acute_col_perp__out A); Col; Perp).
  assert(Bet B A' C) by (apply (out2__bet); [|apply l6_6]; auto).
  assert_diffs.
  assert(Per B A' A) by (apply L形垂直转直角1, 垂直的左交换性, (垂线共线点也构成垂直1 _ C); Col).
  assert(Per C A' A) by (apply (l8_3_直角边共线点也构成直角1 B); Col).
  do 4 (split; [等角|]).
  split; [|split]; [apply out2__conga; Out..|].
  assert(~ Col B A' A) by (apply 成直角三点不共线; auto).
  apply invert_two_sides, bet__ts; Col.
Qed.

Lemma t22_14__bet_aux : forall A B C P Q R,
  hypothesis_of_right_saccheri_quadrilaterals ->
  ~ Col A B C -> 三角形内角和 A B C P Q R -> 为锐角 A B C -> 为锐角 A C B -> Bet P Q R.
Proof.
  intros A B C P Q R rah HNCol HTri HacuteB HacuteC.
  apply trisuma_perm_312 in HTri.
  destruct HTri as [D [E [F []]]].
  destruct (t22_14_aux A B C) as [A']; [assumption..|spliter].
  assert_diffs.

  apply (bet_conga__bet B A' C); auto.
  apply (suma2__conga D E F B C A); auto.
  apply (suma_assoc B A' A C A A' _ _ _ _ _ _ _ _ _ A A' C); [..|和角].
    apply (conga2_sams__sams C A' A A' A C); 等角; 和角.
    apply (conga2_sams__sams A' A C A C A'); 等角; 和角.
    { apply suma_sym, (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
      - apply os_ts__sams; Side.
        apply out_one_side; [Col|Out].
      - apply (conga2_sams__sams A' A B A B A'); 等角; 和角.
      - 和角.
      - apply (等角保持和角 A' A B A B A' B A' A); 等角; apply t22_12__rah; auto.
    }
  apply (等角保持和角 A' A C A C A' C A' A); 等角; apply t22_12__rah; auto.
Qed.

(** Under the Right angle hypothesis,
    the sum of the three angles of a triangle is equal to 180
 *)

Lemma t22_14__bet :
  hypothesis_of_right_saccheri_quadrilaterals ->
  forall A B C P Q R, 三角形内角和 A B C P Q R -> Bet P Q R.
Proof.
  intros rah A B C P Q R HTri.
  elim(共线的决定性 A B C).
    intro; apply (col_trisuma__bet A B C); auto.
  intro.
  assert_diffs.
  destruct (angle_partition A B C); auto; [destruct (angle_partition A C B); auto|].
  - apply (t22_14__bet_aux A B C); auto.

  - destruct (l11_43 C A B); auto.
    apply (t22_14__bet_aux C A B); Col.
    apply trisuma_perm_312; auto.

  - destruct (l11_43 B A C); auto.
    apply (t22_14__bet_aux B A C); Col.
    apply trisuma_perm_213; auto.
Qed.


Lemma t22_14__sams_nbet_aux : forall A B C D E F P Q R,
  hypothesis_of_acute_saccheri_quadrilaterals ->
  ~ Col A B C ->
  和角 C A B A B C D E F -> 和角 D E F B C A P Q R ->
  为锐角 A B C -> 为锐角 A C B ->
  角度之和小于平角 D E F B C A /\ ~ Bet P Q R.
Proof.
  intros A B C D E F P Q R aah HNCol HSuma1 HSuma2 HacuteB HacuteC.
  destruct (t22_14_aux A B C) as [A']; [assumption..|spliter].
  assert_diffs.
  rename H into HBet.

  assert(HSuma3 := 和角的存在性 B A' A C A A').
  destruct HSuma3 as [G [H [I HSuma3]]]; auto.
  suma.assert_diffs.
  assert(角度小于 D E F G H I).
  { assert(HSuma4 := 和角的存在性 A' A B A B C).
    destruct HSuma4 as [V [W [X HSuma4]]]; auto.
    suma.assert_diffs.
    apply (sams_lea_lta456_suma2__lta C A A' V W X _ _ _ C A A' B A' A); [Lea|..|和角].
      apply (acute_per__lta); auto; apply (t22_12__aah B A' A); auto; apply (等角保持和角 A' A B A B C V W X); 等角.
      apply (conga2_sams__sams C A A' A A' C); 和角; 等角.
    apply (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
    - apply os_ts__sams; Side.
      apply out_one_side; [Col|Out].
    - apply (conga2_sams__sams A' A B A B A'); 和角; 等角.
    - exists B; repeat (split; 等角); Side.
      exists C; left; split; Col.
  }
  assert(HSuma4 := 和角的存在性 C A A' B C A).
  destruct HSuma4 as [J [K [L HSuma4]]]; auto.
  suma.assert_diffs.
  assert(角度小于 J K L A A' C).
    apply (acute_per__lta); Perp; apply (t22_12__aah C A' A); auto; apply (等角保持和角 C A A' B C A J K L); 等角.
  assert(角度之和小于平角 G H I B C A).
  { apply (sams_assoc B A' A C A A' _ _ _ _ _ _ J K L); auto.
      apply (conga2_sams__sams C A' A A' A C); 和角; 等角.
      apply (conga2_sams__sams A' A C A C A'); 和角; 等角.
      apply (sams_chara _ _ _ _ _ _ C); Lea.
  }
  assert(HSuma5 := 和角的存在性 G H I B C A).
  destruct HSuma5 as [S [T [U HSuma5]]]; auto.
  suma.assert_diffs.
  assert(角度小于 S T U B A' C).
  { apply (sams_lea_lta456_suma2__lta B A' A J K L _ _ _ B A' A A A' C); [Lea..|和角| |和角].
    apply (suma_assoc _ _ _ C A A' B C A _ _ _ G H I); auto;
      [apply (conga2_sams__sams C A' A A' A C)|apply (conga2_sams__sams A' A C A C A')];
      和角; 等角.
  }

  split.
    apply (sams_lea2__sams _ _ _ _ _ _ G H I B C A); Lea.
  intro.
  apply (nlta P Q R).
  apply (conga_preserves_lta P Q R B A' C); 等角.
  apply (lta_trans _ _ _ S T U); auto.
  apply (sams_lea_lta123_suma2__lta D E F B C A _ _ _ G H I B C A); Lea.
Qed.

(** Under the 为锐角 angle hypothesis,
    the sum of the three angles of a triangle is less than 180
 *)

Lemma t22_14__sams_nbet :
  hypothesis_of_acute_saccheri_quadrilaterals ->
  forall A B C D E F P Q R, ~ Col A B C ->
  和角 C A B A B C D E F -> 和角 D E F B C A P Q R ->
  角度之和小于平角 D E F B C A /\ ~ Bet P Q R.
Proof.
  intros aah A B C D E F P Q R HNCol HSuma1 HSuma2.
  assert_diffs.
  destruct (angle_partition A B C); auto; [destruct (angle_partition A C B); auto|].
  - apply (t22_14__sams_nbet_aux A B C); auto.

  - destruct (l11_43 C A B); auto.
    assert(HSuma3 := 和角的存在性 B C A C A B).
    rename H into H为锐角.
    destruct HSuma3 as [G [H [I HSuma3]]]; auto.
    suma.assert_diffs.
    assert(HInter := t22_14__sams_nbet_aux C A B G H I P Q R).
    destruct HInter as [HIsi HNBet]; Col.
      apply (suma_assoc B C A C A B _ _ _ _ _ _ _ _ _ D E F); 和角.
    split; auto.
    apply sams_sym; apply (sams_assoc _ _ _ C A B A B C G H I); 和角.

  - destruct (l11_43 B A C); auto.
    assert(HInter := t22_14__sams_nbet_aux B A C D E F P Q R).
    destruct HInter as [HIsi HNBet]; Col; 和角.
Qed.

Lemma t22_14__nsams_aux : forall A B C D E F,
  hypothesis_of_obtuse_saccheri_quadrilaterals ->
  ~ Col A B C ->
  和角 C A B A B C D E F -> 为锐角 A B C -> 为锐角 A C B ->
  ~ 角度之和小于平角 D E F B C A.
Proof.
  intros A B C D E F oah HNCol HSuma1 HacuteB HacuteC HIsi.
  destruct (t22_14_aux A B C) as [A']; [assumption..|spliter].
  assert_diffs.

  assert(HSuma2 := 和角的存在性 D E F B C A).
  destruct HSuma2 as [P [Q [R HSuma2]]]; suma.assert_diffs; auto.
  absurd (角度小于 B A' C P Q R).
    apply (lea__nlta); apply l11_31_1_任何角小于等于平角_Bet表述; auto.
  assert(HSuma3 := 和角的存在性 B A' A C A A').
  rename H into HBet.
  destruct HSuma3 as [G [H [I HSuma3]]]; auto.
  assert(角度小于 G H I D E F).
  { assert(HSuma4 := 和角的存在性 A' A B A B C).
    destruct HSuma4 as [V [W [X HSuma4]]]; auto.
    suma.assert_diffs.
    assert(角度之和小于平角 C A A' A' A B).
    { apply os_ts__sams; Side.
      apply out_one_side; [Col|Out].
    }
    assert(角度之和小于平角 A' A B A B C) by (apply (conga2_sams__sams A' A B A B A'); 和角; 等角).
    assert(和角 C A A' A' A B C A B) by (exists B; repeat (split; 等角); Side; Cop).
    apply (sams_lea_lta456_suma2__lta C A A' B A' A _ _ _ C A A' V W X); Lea.
      apply (obtuse_per__lta); auto; apply (t22_12__oah B A' A); auto; apply (等角保持和角 A' A B A B C V W X); 等角.
      apply (sams_assoc _ _ _ A' A B A B C C A B); 和角.
      和角.
      apply (suma_assoc _ _ _ A' A B A B C _ _ _ C A B); auto.
  }
  assert(HSuma4 := 和角的存在性 C A A' B C A).
  destruct HSuma4 as [J [K [L HSuma4]]]; auto.
  suma.assert_diffs.
  assert(角度小于 A A' C J K L).
    apply (obtuse_per__lta); Perp; apply (t22_12__oah C A' A); auto; apply (等角保持和角 C A A' B C A J K L); 等角.
  assert(HSuma5 := 和角的存在性 B A' A J K L).
  destruct HSuma5 as [S [T [U HSuma5]]]; auto.
  suma.assert_diffs.
  apply (lta_trans _ _ _ S T U).
  - apply (sams_lea_lta456_suma2__lta B A' A A A' C _ _ _ B A' A J K L); Lea;
    [|exists C; repeat (split; 等角); Side; Cop].
    apply (sams_assoc _ _ _ C A A' B C A G H I); auto.
      apply (conga2_sams__sams C A' A C A A'); 和角; 等角.
      apply (conga2_sams__sams C A A' A' C A); 和角; 等角.
    apply (sams_lea2__sams _ _ _ _ _ _ D E F B C A); Lea.

  - apply (sams_lea_lta123_suma2__lta G H I B C A _ _ _ D E F B C A); Lea.
    apply (suma_assoc B A' A C A A' _ _ _ _ _ _ _ _ _ J K L); auto.
      apply (conga2_sams__sams C A' A C A A'); 和角; 等角.
      apply (conga2_sams__sams C A A' A' C A); 和角; 等角.
Qed.

(** Under the 为钝角 angle hypothesis,
    the sum of the three angles of a triangle is greater than 180
 *)

Lemma t22_14__nsams :
  hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F, ~ Col A B C ->
  和角 C A B A B C D E F ->
  ~ 角度之和小于平角 D E F B C A.
Proof.
  intros oah A B C D E F HNCol HSuma1.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro; elim(angle_partition A C B); auto.
  - intro.
    apply (t22_14__nsams_aux A B C); auto.

  - intro.
    assert(HInter := l11_43 C A B).
    destruct HInter; Col.
    assert(HSuma3 := 和角的存在性 B C A C A B).
    rename H into H为锐角.
    destruct HSuma3 as [G [H [I HSuma3]]]; auto.
    suma.assert_diffs.
    assert(HNIsi := t22_14__nsams_aux C A B G H I).
    intro HIsi.
    absurd(角度之和小于平角 G H I A B C).
      apply HNIsi; Col.
      apply (sams_assoc B C A C A B _ _ _ _ _ _ D E F); 和角.

  - intro.
    assert (HInter := l11_43 B A C).
    destruct HInter; Col.
    intro.
    absurd(角度之和小于平角 D E F A C B).
      apply (t22_14__nsams_aux B A C D E F); Col; 和角.
      和角.
Qed.


(** If the sum of the angles of a non-degenerate triangle is equal to 180,
    then the Right angle hypothesis holds
 *)

Lemma t22_14__rah : forall A B C P Q R,
  ~ Col A B C -> 三角形内角和 A B C P Q R -> Bet P Q R -> hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C P Q R HNCol HTri HBet.
  apply trisuma_perm_312 in HTri.
  destruct (saccheri_s_three_hypotheses) as [aah|[|oah]]; auto; exfalso.
  - destruct HTri as [D [E [F []]]].
    assert(HInter := t22_14__sams_nbet aah A B C D E F P Q R).
    destruct HInter; auto.

  - exfalso.
    destruct HTri as [D [E [F [HSuma1 HSuma2]]]].
    apply (t22_14__nsams oah A B C D E F); auto.
    destruct HSuma2 as [G [HConga1 [HNos [HCop HConga2]]]].
    apply 等角的对称性 in HConga1.
    assert_diffs.
    apply (sams_chara _ _ _ _ _ _ G); Lea.
    apply (bet_conga__bet P Q R); 等角.
Qed.

(** If the sum of the angles of a triangle is less than 180,
    then the 为锐角 angle hypothesis holds
 *)

Lemma t22_14__aah : forall A B C D E F P Q R,
  和角 C A B A B C D E F -> 和角 D E F B C A P Q R ->
  角度之和小于平角 D E F B C A ->
  ~ Bet P Q R ->
  hypothesis_of_acute_saccheri_quadrilaterals.
Proof.
  intros A B C D E F P Q R HSuma1 HSuma2 HIsi HNBet.
  destruct(saccheri_s_three_hypotheses) as [|[rah|oah]]; auto; exfalso.
  - apply HNBet.
    apply (t22_14__bet rah A B C).
    apply trisuma_perm_231.
    exists D, E, F.
    split; auto.

  - destruct (共线的决定性 A B C).
    { apply HNBet.
      apply (col_trisuma__bet C A B); Col.
      exists D, E, F.
      split; auto.
    }
    absurd(角度之和小于平角 D E F B C A); auto.
    apply t22_14__nsams; auto.
Qed.

(** If the sum of the angles of a triangle is greater than 180,
    then the 为钝角 angle hypothesis holds
 *)

Lemma t22_14__oah : forall A B C D E F,
  和角 C A B A B C D E F -> ~ 角度之和小于平角 D E F B C A -> hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HSuma1 HNIsi.
  suma.assert_diffs.
  destruct(共线的决定性 A B C).
  { exfalso.
    apply HNIsi.
    destruct(中间性的决定性 A B C).
    - apply out546__sams; Out.
    - apply (conga2_sams__sams C A B B C A); try (apply 同角相等); 和角.
      apply (out546_suma__conga _ _ _ A B C); auto.
      apply not_bet_out; auto.
  }
  assert(HSuma2 := 和角的存在性 D E F B C A).
  destruct HSuma2 as [P [Q [R HSuma2]]]; auto.
  destruct (saccheri_s_three_hypotheses) as [aah|[rah|]]; auto; exfalso; apply HNIsi.
  - apply t22_14__sams_nbet with P Q R; assumption.
  - apply bet_suma__sams with P Q R; trivial.
    apply (t22_14__bet rah C A B).
    exists D, E, F; split; assumption.
Qed.


(** If C is on the circle of diameter AB, then we have the angles equation A + B = C *)

Lemma cong_mid__suma : forall A B C M,
  ~ Col A B C ->
  中点 M A B -> Cong M A M C ->
  和角 C A B A B C A C B.
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(等角 A B C M C B).
  { apply (l11_10 M B C M C B); Out.
    apply l11_44_1_a; auto; apply (等长的传递性 _ _ M A); Cong.
  }
  assert(等角 B A C M C A).
  { apply (l11_10 M A C M C A); Out.
    apply l11_44_1_a; Cong.
  }
  apply (等角保持和角 A C M M C B A C B); 等角.
  assert (TS M C A B) by (apply bet__ts; Between; intro; apply HNCol; ColR).
  exists B.
  repeat (split; 等角); Side; Cop.
Qed.


(** The three following lemmas link 萨凯里四边形's three hypotheses
    with triangles ABC having C on the circle of diameter AB;
    the first one states the equivalence between the Right angle hypothesis and Thales' theorem
 *)

Lemma t22_17__rah : forall A B C M,
  ~ Col A B C ->
  中点 M A B -> Cong M A M C ->
  (Per A C B <-> hypothesis_of_right_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(和角 C A B A B C A C B) by (apply (cong_mid__suma _ _ _ M); auto).
  assert(HSuma := 和角的存在性 A C B B C A).
  destruct HSuma as [P [Q [R]]]; auto.
  split; intro HR.
  - apply (t22_14__rah C A B P Q R); Col.
      exists A; exists C; exists B; auto.
      apply (per2_suma__bet A C B B C A); Perp.

  - apply (bet_suma__per _ _ _ P Q R); 和角.
    apply (t22_14__bet HR C A B).
    exists A, C, B; auto.
Qed.

Lemma t22_17__oah : forall A B C M,
  ~ Col A B C ->
  中点 M A B -> Cong M A M C ->
  (为钝角 A C B <-> hypothesis_of_obtuse_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  assert(和角 C A B A B C A C B) by (apply (cong_mid__suma _ _ _ M); auto).
  assert(HSuma := 和角的存在性 A C B B C A).
  destruct HSuma as [P [Q [R]]]; auto.
  split; intro HO.
  - apply (t22_14__oah A B C B C A); Col; 和角.
    apply obtuse__nsams; apply obtuse_sym; auto.

  - apply obtuse_sym.
    apply nsams__obtuse; auto.
    apply (t22_14__nsams HO A B C); Col; 和角.
Qed.

Lemma t22_17__aah : forall A B C M,
  ~ Col A B C ->
  中点 M A B -> Cong M A M C ->
  (为锐角 A C B <-> hypothesis_of_acute_saccheri_quadrilaterals).
Proof.
  intros A B C M HNCol HM HCong.
  assert_diffs.
  split; intro.
  - destruct (saccheri_s_three_hypotheses) as [|[|]]; auto; exfalso; apply (nlta A C B).
      apply (acute_per__lta); auto; rewrite (t22_17__rah _ _ _ M); auto.
      apply (acute_obtuse__lta); auto; rewrite (t22_17__oah _ _ _ M); auto.

  - destruct (angle_partition A C B) as [|[|]]; auto;
    absurd(hypothesis_of_acute_saccheri_quadrilaterals); auto; apply not_aah.
      left; apply (t22_17__rah A B C M); auto.
      right; apply (t22_17__oah A B C M); auto.
Qed.

Lemma t22_20 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F, 和角 A B C B C A D E F -> 角度之和小于平角 D E F C A B.
Proof.
  intros noah A B C D E F HS.
  destruct(sams_dec D E F C A B); trivial.
  exfalso.
  apply noah, (t22_14__oah B C A D E F); trivial.
Qed.

Lemma absolute_exterior_angle_theorem : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D E F B', Bet B A B' -> A <> B' -> 和角 A B C B C A D E F ->
  角度小于等于 D E F C A B'.
Proof.
  intros noah A B C D E F B' HBet HAB' HSuma.
  assert (HIsi := t22_20 noah A B C D E F HSuma).
  assert_diffs.
  apply sams_chara with B; 和角.
Qed.

End 萨凯里四边形.

Hint Resolve sac__pars1423 sac__pars1234 sac__par1423 sac__par1234
             lam__pars1234 lam__pars1423 lam__par1234 lam__par1423 : Par.