Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_universal_posidonius_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma playfair__universal_posidonius_postulate : playfair_s_postulate -> universal_posidonius_postulate.
Proof.
intros HP A1 A2 A3 A4 B1 B2 B3 B4 HPar HC1 HC2 HPerp1 HC3 HC4 HPerp2.
elim HPar; intro HParS; [|destruct HParS as [HD1 [HD2 [HC5 HC6]]];
                           统计不重合点; assert_cols;
                           elim (垂直推出不共线 _ _ _ _ HPerp1);
                           intro HF; exfalso; apply HF; ColR].
destruct (l8_18_过一点垂线之垂点的存在性 A1 A2 B1) as [A1' [HC5 HPerp3]];
try apply par_strict_not_col_1 with B2; Par.
assert (HCong : forall A3 B3,
                  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
                  Cong A3 B3 A1' B1);
[|assert (HCong1 := HCong A3 B3 HC1 HC2 HPerp1);
  assert (HCong2 := HCong A4 B4 HC3 HC4 HPerp2);
  apply 等长的传递性 with A1' B1; Cong].
clear HC1; clear HC2; clear HC3; clear HC4; clear HPerp1; clear HPerp2;
clear A3; clear A4; clear B3; clear B4; intros A3 B3 HC1 HC2 HPerp1;
rename HC5 into HC3; rename HPerp3 into HPerp2.
destruct (由一点往一方向构造等长线段_2 B3 A3 A1' B1) as [B3' [HC4 HCong]];
[统计不重合点; auto|]; elim (两点重合的决定性 A1' A3); intro HD; treat_equalities.
  {
  assert (HC1 : Col A1' B1 B3).
    apply cop_perp2__col with A1 A2; Perp.
    统计不重合点; apply col_cop__cop with B2; Col.
    apply 平行蕴含共面, HPar.
  assert (B1 = B3); treat_equalities; Cong.
  统计不重合点; apply l6_21_两线交点的唯一性 with B1 B2 A1' B1; Col.
  elim (两点重合的决定性 A1' A1); intro HD1.
   treat_equalities; apply par_strict_not_col_1 with A2;
   apply par_strict_col2_par_strict with A1' A2; Col; Par.
   apply par_strict_not_col_1 with A1;
   apply par_strict_col2_par_strict with A1 A2; Col; Par.
  }

  {
  assert (HParS' : 严格平行 A1' A3 B1 B3').
    {
    apply sac__pars1423; repeat split; [apply L形垂直转直角1..|Cong|].
      apply 与垂线共线之线也为垂线1 with A1 A2; Perp.
      统计不重合点.
      apply 与垂线共线之线也为垂线1 with A3 B3; [apply 与垂线共线之线也为垂线1 with A1 A2| |induction HC4|]; Col.
    apply one_side_transitivity with B3.

      {
      elim (两点重合的决定性 B1 B3); intro HD';
      [treat_equalities; apply one_side_reflexivity; apply par_strict_not_col_1 in HParS;
       intro; apply HParS; ColR|].
      apply (col2_os__os A1 A2); Col.
      apply par_strict_one_side with B2; Col.
      }

      {
      统计不重合点.
      apply invert_one_side, out_one_side; [|repeat split; auto].
      elim (垂直推出不共线 _ _ _ _ HPerp1); intro HNC; [contradiction|].
      left; intro; apply HNC; ColR.
      }
    }
  统计不重合点.
  destruct (HP A1 A2 B1 B2 B1 B3' B1) as [_ HC5]; Col;
  [apply par_symmetry; apply par_col2_par with A1' A3; Par; ColR|].
  assert (B3 = B3'); [|subst; Cong].
  apply l6_21_两线交点的唯一性 with B1 B3' A3 B3; Col;
  [apply par_strict_not_col_1 with A1'; Par|ColR|induction HC4; Col].
  }
Qed.

End playfair_universal_posidonius_postulate.