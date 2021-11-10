Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_posidonius.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__posidonius_aux : postulate_of_right_saccheri_quadrilaterals ->
  forall A1 A2 A3 B1 B2 B3,
  Per A2 A1 B1 -> Per A1 A2 B2 -> Cong A1 B1 A2 B2 -> OS A1 A2 B1 B2 ->
  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
  Cong A3 B3 A1 B1.
Proof.
  intros rah A1 A2 A3 B1 B2 B3 HPer1 HPer2 HCong HOS HA HB HPerp.
  assert (HSac : 萨凯里四边形 A1 B1 B2 A2) by (repeat split; Perp; Cong).
  assert(Hdiff := sac_distincts A1 B1 B2 A2 HSac).
  spliter.
  统计不重合点.
  elim(两点重合的决定性 A1 A3).
  { intro.
    subst A3.
    assert(B1 = B3); [|subst; Cong].
    apply (l6_21_两线交点的唯一性 B1 B2 A1 B1); Col.
      apply 共线否定排列BCA, par_strict_not_col_1 with A2, sac__pars1234, HSac.
      unfold 萨凯里四边形 in HSac; spliter; apply (cop_perp2__col _ _ _ A1 A2); Perp.
      apply col_cop__cop with B2; Cop.
  }
  intro.
  destruct(由一点往一方向构造等长线段_3 A3 B3 A1 B1) as [B'3 []]; auto.
  统计不重合点.
  assert(B3 = B'3); [|subst; assumption].
  assert(严格平行 B1 B2 A1 A3).
  { apply (par_strict_col_par_strict _ _ _ A2); auto.
    apply par_strict_symmetry.
    apply sac__pars1423; assumption.
  }
  apply (l6_21_两线交点的唯一性 B1 B2 A3 B3); Col.
    apply (par_strict_not_col_4 _ _ A1); auto.
  apply 等价共线CAB.
  assert (共面 A1 B2 B'3 B1).
  { apply coplanar_perm_15, coplanar_trans_1 with A3.
      apply 共线否定排列CAB, par_strict_not_col_4 with A1; assumption.
      apply coplanar_perm_18, pars__coplanar; assumption.
    exists B3; right; right; split; Col.
  }
  apply cop_per2__col with A1; auto; apply 直角的对称性.
    apply (rah _ _ _ A2); auto.
  apply (rah _ _ _ A3).
  unfold 萨凯里四边形 in *.
  spliter.
  assert(B1 <> B3).
  { intro.
    subst B3.
    assert(A1 = A3); auto.
    apply (l8_18_过一点垂线之垂点的唯一性 A1 A2 B1); Col; Perp.
    apply 共线否定排列BCA; apply 成直角三点不共线; auto.
  }
  assert(Per A1 A3 B'3).
  { apply L形垂直转直角1, 垂直的交换性, (垂线共线点也构成垂直1 _ A2); Col.
    apply (垂线共线点也构成垂直2 _ _ _ B3); Col.
  }
  repeat split; Cong.
    apply (直角边共线点也构成直角2 _ _ A2); auto.
  apply (one_side_transitivity _ _ _ B3).
    apply l12_6; auto; apply (par_strict_col_par_strict _ _ _ B2); Col; Par.
    apply invert_one_side; apply out_one_side; auto; right; apply 共线否定排列BAC; apply 成直角三点不共线; auto.
Qed.

Lemma rah__posidonius :
  postulate_of_right_saccheri_quadrilaterals -> posidonius_postulate.
Proof.
intro HP.
destruct ex_saccheri as [A1 [B1 [B2 [A2 [HPer1 [HPer2 [HCong HOS]]]]]]].
exists A1; exists A2; exists B1; exists B2.
assert (HNE : A1 <> A2) by (destruct HOS as [X [[H ?] ?]]; intro; subst A2; Col).
split; [destruct HOS; unfold TS in *; spliter; Col|].
split; [intro; treat_equalities; apply ABC和ACB均直角则B与C重合 in HPer1; intuition|split; [Cop|]].
intros A3 A4 B3 B4 HC1 HC2 HPerp1 HC3 HC4 HPerp2.
assert (HCong1 := rah__posidonius_aux HP A1 A2 A3 B1 B2 B3).
assert (HCong2 := rah__posidonius_aux HP A1 A2 A4 B1 B2 B4).
apply 等长的内传递性 with A1 B1; apply 等长的对称性;
[apply HCong1|apply HCong2]; Cong; apply 直角的对称性; auto.
Qed.

End rah_posidonius.