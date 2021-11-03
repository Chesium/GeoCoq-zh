Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_perp_2_par_par_perp_perp.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma par_perp_2_par_implies_par_perp_perp :
  postulate_of_parallelism_of_perpendicular_transversals ->
  perpendicular_transversal_postulate.
Proof.
intros HPPP A B C D P Q HPar HPerp HCop.
elim HPar; clear HPar; intro HPar;
[|spliter; apply 与垂线共线之线也为垂线2 with A B; auto; ColR].
assert (HX := HPerp); destruct HX as [X HX].
elim (共线的决定性 C D X); intro HCDX.

  exfalso; apply HPar; exists X; unfold 垂直于 in HX; spliter; Col.

  assert (HY := l8_18_过一点垂线之垂点的存在性 C D X HCDX); destruct HY as [Y [HCDY HPerp']].
  assert (HPar' : Par P Q X Y).
    {
    destruct HX as [_ [_ [HCol [ ]]]]; assert_diffs.
    assert (共面 C D X A)
      by (apply col2_cop__cop with A B; Col; apply pars__coplanar; Par).
    assert (共面 C D X B)
      by (apply col2_cop__cop with A B; Col; apply pars__coplanar; Par).
    assert (共面 C D X P)
      by (apply col2_cop__cop with P Q; Col; apply perp__coplanar; Perp).
    assert (共面 C D X Q)
      by (apply col2_cop__cop with P Q; Col; apply perp__coplanar; Perp).
    assert (共面 C D X Y) by Cop.
    apply HPPP with A B C D; Perp; try solve [left; auto];
    try solve [apply col2_cop__cop with P Q; Col; Cop]; CopR.
    }
  elim HPar'; clear HPar'; intro HPar'.

    exfalso; apply HPar'; exists X; unfold 垂直于 in HX; spliter; Col.

    destruct HPar' as [HPQ [HXY [HCol1 HCol2]]].
    apply 垂直的对称性; apply 与垂线共线之线也为垂线2 with X Y; Col; Perp.
Qed.

End par_perp_2_par_par_perp_perp.