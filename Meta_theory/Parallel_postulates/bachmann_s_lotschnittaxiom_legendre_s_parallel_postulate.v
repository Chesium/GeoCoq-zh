Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate :
  bachmann_s_lotschnittaxiom -> legendre_s_parallel_postulate.
Proof.
rewrite bachmann_s_lotschnittaxiom_aux.
intro bla.
cut (exists A B C, ~ Col A B C /\ 为锐角 A B C /\ forall P Q,
          Out B A P -> P <> Q -> Per B P Q -> 共面 A B C Q ->
          exists Y, Out B C Y /\ Col P Q Y).
  {
  clear bla.
  intros [A [B [C [HNC [H为锐角 HP]]]]]; exists A, B, C; repeat split; Col.
  intros T H在角内; elim (共线的决定性 A B T); intro HABT.

    {
    assert (HNC' : ~ Col B C T)
      by (intro; apply HNC; ColR).
    destruct (l8_18_过一点垂线之垂点的存在性 B C T HNC') as [Y [HC HPerp]].
    exists T, Y.
    assert (HOut : Out B A T).
      {
      apply col_in_angle_out with C; [|intro; apply HNC|]; Col.
      }
    split; [|split]; Between.
    apply l6_6, acute_col_perp__out with T; Col.
    apply acute_conga__acute with A B C; auto.
    apply 零角加上任何角后者大小不变 with T B A; [|Out].
    统计不重合点.
    exists C; repeat (split; try (apply 同角相等; auto)).
      apply col123__nos; Col.
      Cop.
    }

    {
    destruct (l8_18_过一点垂线之垂点的存在性 A B T) as [X [HC HPerp]]; Col.
    assert (HOut1 : Out B A X).
      {
      apply l6_6, acute_col_perp__out with T; Col; Perp.
      apply 小于等于锐角之角为锐角 with A B C; auto.
      apply 角度小于等于的左交换性, l11_29_b_能在其内找一点构造等角之角较大.
      exists C; split; trivial.
      统计不重合点; apply 同角相等; auto.
      }
    destruct (HP X T) as [Y [HOut2 H]].
      assumption.
      统计不重合点; auto.
      统计不重合点; apply L形垂直转直角1, 垂直的对称性, 与垂线共线之线也为垂线1 with A B; Col.
      Cop.
    exists X, Y; repeat (split; [assumption|]).
    elim H; clear H; intro H; auto.
    elim (两点重合的决定性 T Y); intro HTY.
      subst; Between.
    assert (HACT : ~ Col B C T).
      {
      统计不重合点; intro; apply HTY, l6_21_两线交点的唯一性 with B C X T; Col.
        intro; apply HNC; ColR.
        right; assumption.
      }
    elim H; clear H; intro HBet.

      {
      assert (HOS : OS C B T A)
        by (apply 角内点和一端点在角另一边同侧; [Col..|apply l11_24_在角内的对称性, H在角内]).
      exfalso; apply (l9_9_bis _ _ _ _ HOS).
      apply l9_2, l9_8_2 with X.

        {
        repeat split; [intro; apply HNC; ColR..|].
        exists Y; split; [Col|Between].
        }

        {
        apply l9_19 with B; Col.
        split; [Out|intro; apply HNC; ColR].
        }
      }

      {
      assert (HOS : OS A B T C) by (apply 角内点和一端点在角另一边同侧; Col).
      exfalso; apply (l9_9_bis _ _ _ _ HOS).
      apply l9_2; apply l9_8_2 with Y.

        {
        repeat split; [intro; 统计不重合点; apply HNC; ColR..|].
        exists X; split; Col.
        }

        {
        apply l9_19 with B; Col.
        split; [Out|intro; apply HNC; ColR].
        }
      }
    }
  }

  {
  destruct 防降维公理_老版本 as [C [E [D H]]].
  assert (HNC : ~ Col C E D) by auto; clear H.
  destruct (l8_18_过一点垂线之垂点的存在性 D E C) as [B [HC1 HPerp]]; Col.
  assert (HF : exists F, Col D E F /\ B <> F).
    {
    统计不重合点; elim (两点重合的决定性 B E); intro;
    [exists D|exists E]; subst; split; Col.
    }
  destruct HF as [F [HC2 HNE]].
  destruct (由一点往一方向构造等长线段_2 F B B C) as [A [Hd HCong1]]; auto.
  assert (HC3 : Col D E A)
    by (assert (Col A B F) by (induction Hd; Col); ColR).
  clear Hd.
  assert (HPerp1 : Perp B A C B)
    by (统计不重合点; apply 垂直的对称性, 与垂线共线之线也为垂线1 with D E; Perp).
  clear dependent D; clear dependent F; clear E.
  assert (HNC := L形垂直推出不共线 _ _ _ HPerp1).
  destruct (中点的存在性 A C) as [D HD].
  exists A, B, D.
  split; [intro; apply HNC; ColR|split].

    {
    统计不重合点.
    assert (D <> B) by (intro; subst; apply HNC; Col).
    exists A, B, C; split; [Perp|split].

      {
      exists D; split; [repeat split|apply 同角相等]; auto.
      exists D; split; [Between|right; Out].
      }

      {
      intro H等角.
      assert (HPer1 : Per A B D).
        {
        apply l11_17_等于直角的角是直角 with A B C; [Perp|等角].
        }
      assert (HPer2 : Per C B D).
        {
        apply l11_17_等于直角的角是直角 with A B D; trivial.
        apply 三角形全等推角等1; auto.
        repeat split; Cong.
        }
      assert (H和角 : 和角 A B D C B D A B C).
        {
        exists C; repeat (split; 等角); [|Cop].
        apply l9_9.
        repeat split; [apply 成直角三点不共线; auto..|].
        exists D; split; [Col|Between].
        }
      assert (HC := 两直角之和为平角 _ _ _ _ _ _ _ _ _ HPer1 HPer2 H和角).
      apply HNC; Col.
      }
    }

    {
    intros P Q HOut1 HNE1 HPer HCop1.
    destruct (l6_11_existence B B P C) as [P' [HOut2 HCong2]]; [统计不重合点; auto..|].
    destruct (ex_perp_cop B C P' A) as [Q' [HPerp2 HCop2]]; [统计不重合点; auto|].
    assert (HPerp3 : Perp B A Q P).
      {
      统计不重合点.
      apply l8_16_2_共线四点和一直角推另一垂直 with B; Col; Perp.
      apply 成直角三点不共线 in HPer; auto.
      intro; apply HPer; ColR.
      }
    assert (共面 B Q A C)
      by (统计不重合点; apply col2_cop__cop with A D; Col; Cop).
    assert (B <> P') by (destruct HOut2; auto).
    assert (B <> P) by (intro; treat_equalities; auto).
    destruct (bla B A B C P Q P' Q' B P P') as [I [HC1 HC2]]; Col; Perp; [CopR..|].
    assert (HNE2 : B <> D)
      by (intro; treat_equalities; apply HNC; Col).
    assert (HOS : OS B C P I).
      {
      apply l12_6; apply par_strict_col_par_strict with Q; Col.

        {
        intro; treat_equalities; apply (L形垂直推出不共线 _ _ _ HPerp1).
        destruct (not_strict_par A B P' Q' P) as [HC3 HC4]; [|ColR..].
        apply l12_9 with B C; Perp; Cop.
        }

        {
        apply par_not_col_strict with P; [apply l12_9 with A B|..]; Perp; Col; Cop.
        intro; apply HNC; ColR.
        }
      }
    exists I; split; Col; apply l6_4_2; split.

      {
      elim (两点重合的决定性 D I); intro HNE3; [treat_equalities; Col|].
      assert (共面 A B C I) by (apply col_cop2__cop with P Q; Cop).
      统计不重合点.
      apply cop_perp2__col with A C;
      [Cop|apply 中垂线蕴含垂直, 中垂线左对称性, 距线两端点等距点与中点连线为该线中垂线; Cong..].
      assert (HPerp4 : Perp P I B P).
        {
        apply 与垂线共线之线也为垂线1 with A B; [apply 与垂线共线之线也为垂线1 with P Q|..]; Col; Perp.
        intro; treat_equalities; apply HNC.
        assert (HPar : Par B A P' Q') by (apply l12_9 with B C; Perp; Cop).
        destruct (not_strict_par B A P' Q' P); ColR.
        }
      assert (HPerp5 : Perp P' I B P').
        {
        apply 与垂线共线之线也为垂线1 with B C; [apply 与垂线共线之线也为垂线1 with P' Q'|..]; Col; Perp.
        intro; treat_equalities; apply HNC.
        assert (HPar : Par B C P Q) by (apply l12_9 with B A; Perp; Cop).
        destruct (not_strict_par B C P Q P'); ColR.
        }
      统计不重合点.
      destruct (per_lt B P I) as [HLt _]; [Perp..|].
      destruct (l11_52 I P B I P' B) as [_ [_ H等角2]]; Cong; Le.
        apply l11_16_直角相等; Perp.
      apply 等角两边等长则端点间距相等 with B B; Cong.
      apply l11_10 with P I P' I; Out.
      }

      {
      intro; apply (l9_9_bis _ _ _ _ HOS).
      assert (~ Col B C D) by (intro; apply HNC; ColR).
      apply l9_8_2 with D; try apply one_side_transitivity with A.

        {
        apply one_side_symmetry in HOS; apply one_side_not_col123 in HOS.
        repeat split; [..|exists B; split]; Col.
        }

        {
        统计不重合点.
        apply l9_19 with C; Col; split; Out.
        }

        {
        apply l9_19 with B; Col.
        }
      }
    }
  }
Qed.

End bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.