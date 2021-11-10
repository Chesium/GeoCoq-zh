Require Export GeoCoq.Highschool.泰勒斯定理.
Require Export GeoCoq.Highschool.exercises.

Section Circumcenter.

Context `{TE:塔斯基公理系统_欧几里得几何}.
(* 外接圆圆心 *)
Definition 外心 G A B C := Cong A G B G /\ Cong B G C G /\ 共面 G A B C.

Lemma 外心与三角形共面 : forall A B C G, 外心 G A B C -> 共面 G A B C.
Proof.
unfold 外心; intros; spliter; assumption.
Qed.

Lemma 外心与三角形顶点距离相等 : forall G A B C,
 外心 G A B C ->
 Cong A G B G /\ Cong B G C G /\ Cong C G A G.
Proof.
unfold 外心.
intros.
intuition eCong.
Qed.

Lemma 外心的等价排列 : forall A B C G,
 外心 G A B C ->
 外心 G A B C /\ 外心 G A C B /\
 外心 G B A C /\ 外心 G B C A /\
 外心 G C A B /\ 外心 G C B A.
Proof.
unfold 外心.
intros.
spliter.
repeat split;eauto using 等长的传递性 with cong;Cop.
Qed.

Lemma 外心的各排列情况 :
  forall A B C G,
  外心 G A B C \/
  外心 G A C B \/
  外心 G B A C \/
  外心 G B C A \/
  外心 G C A B \/
  外心 G C B A ->
  外心 G A B C.
Proof.
intros.
decompose [or] H;clear H; first [apply 外心的等价排列 in H0|apply 外心的等价排列 in H1];
spliter; assumption.
Qed.

Lemma 等价外心ACB : forall A B C G,
 外心 G A B C -> 外心 G A C B.
Proof.
intros.
apply 外心的等价排列 in H;intuition.
Qed.

Lemma 等价外心BAC : forall A B C G,
 外心 G A B C -> 外心 G B A C.
Proof.
intros.
apply 外心的等价排列 in H;intuition.
Qed.

Lemma 等价外心BCA : forall A B C G,
 外心 G A B C -> 外心 G B C A.
Proof.
intros.
apply 外心的等价排列 in H;intuition.
Qed.

Lemma 等价外心CAB : forall A B C G,
 外心 G A B C -> 外心 G C A B.
Proof.
intros.
apply 外心的等价排列 in H;intuition.
Qed.

Lemma 等价外心CBA : forall A B C G,
 外心 G A B C -> 外心 G C B A.
Proof.
intros.
apply 外心的等价排列 in H;intuition.
Qed.

End Circumcenter.

Hint Resolve
     等价外心ACB
     等价外心BAC
     等价外心BCA
     等价外心CAB
     等价外心CBA : Circumcenter.

Hint Resolve 外心与三角形共面 : cop.

Ltac 推导四点共面 :=
 repeat match goal with
      | H:Perp ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply perp__coplanar, H)
      | H:TS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply ts__coplanar, H)
      | H:OS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply os__coplanar, H)
      | H:严格对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply reflectl__coplanar, H)
      | H:对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply reflect__coplanar, H)
      | H:在角内 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply inangle__coplanar, H)
      | H:严格平行 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply pars__coplanar, H)
      | H:Par ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply par__coplanar, H)
      | H:Plg ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plg__coplanar, H)
      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plgs__coplanar, H)
      | H:退化平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plgf__coplanar, H)
      | H:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply parallelogram__coplanar, H)
      | H:菱形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply rhombus__coplanar, H)
      | H:长方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply rectangle__coplanar, H)
      | H:正方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply square__coplanar, H)
      | H:萨凯里四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply sac__coplanar, H)
      | H:Lambert四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply lambert__coplanar, H)
      | H:外心 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 外心与三角形共面, H)
 end.

Ltac Cop := auto; try (intros; solve [apply col__coplanar; Col
     |apply coplanar_perm_1, col__coplanar; Col|apply coplanar_perm_4, col__coplanar; Col
     |apply coplanar_perm_18, col__coplanar; Col
     |推导四点共面; auto 2 with cop_perm]).

Ltac copr_aux :=
 repeat match goal with
      | H: ~ Col ?X1 ?X2 ?X3, X4 : Tpoint |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4;
     first[exist_hyp_perm_col X1 X2 X4; assert (共面 X1 X2 X4 X3) by (apply col__coplanar; Col)
          |exist_hyp_perm_col X2 X3 X4; assert (共面 X2 X3 X4 X1) by (apply col__coplanar; Col)
          |exist_hyp_perm_col X1 X3 X4; assert (共面 X1 X3 X4 X2) by (apply col__coplanar; Col)]
 end.

Ltac CopR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
 let cop := constr:(共面) in
   treat_equalities; assert_cols; clean; assert_ncols; 推导四点共面; auto 2 with cop_perm;
   solve[apply col__coplanar; Col|apply coplanar_perm_1, col__coplanar; Col
        |apply coplanar_perm_4, col__coplanar; Col|apply coplanar_perm_18, col__coplanar; Col
        |copr_aux; Cop_refl tpoint col cop] || fail "Can not be deduced".

Section Circumcenter2 .

Context `{TE:塔斯基公理系统_欧几里得几何}.

(**
#
<script type="text/javascript" language="javascript" src="
http://www.geogebra.org/web/4.2/web/web.nocache.js"></script><article class="geogebraweb" data-param-width="800" data-param-height="600" 
data-param-showResetIcon="false" data-param-enableLabelDrags="false" data-param-showMenuBar="false" data-param-showToolBar="false" data-param-showAlgebraInput="false" enableLabelDrags="true" data-param-ggbbase64="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"></article>
#
**)

Lemma 外心与一边中点连线是该边中垂线 : forall A B C A' G,
  A<>B -> B<>C -> A<>C -> G <> A' ->
  外心 G A B C ->
  中点 A' B C ->
  Perp_bisect G A' B C.
Proof.
intros.
apply cong_cop_perp_bisect; try assumption;
unfold 中点, 外心 in *; spliter; Cong; Cop.
Qed.


Lemma 外心的存在性 : forall A B C,
  ~ Col A B C -> exists G, 外心 G A B C.
Proof.
intros.
assert (triangle_circumscription_principle).
apply (inter_dec_plus_par_perp_perp_imply_triangle_circumscription).
unfold decidability_of_intersection; apply inter_dec.
unfold perpendicular_transversal_postulate.
intros; apply cop_par_perp__perp with A0 B0; auto.
unfold triangle_circumscription_principle in *.
destruct (H0 A B C H) as [G HG].
exists G.
unfold 外心.
spliter.
repeat split;Cop;CongR.
Qed.

Lemma 外心与任一边中点连线是该边中垂线 : forall A B C A' B' C' G,
  A<>B -> B<>C -> A<>C -> G <> A' -> G <> B' -> G <> C' ->
  外心 G A B C ->
  中点 A' B C ->
  中点 B' A C ->
  中点 C' A B ->
  Perp_bisect G A' B C /\ Perp_bisect G B' A C /\ Perp_bisect G C' A B.
Proof.
intros.
unfold 外心 in *; spliter.
split; [|split]; apply cong_mid_perp_bisect; trivial; CongR.
Qed.

Lemma 三角形的三条中垂线交于一点 : forall A B C A' B' C' G,
  A<>B -> B<>C -> A<>C -> G <> A' -> G <> B' -> G <> C' ->
  中点 A' B C ->
  中点 B' A C ->
  中点 C' A B ->
  Perp_bisect G A' B C ->
  Perp_bisect G B' A C ->
  Perp G C' A B.
Proof.
intros.
assert (Cong B G C G).
 apply (perp_bisect_cong2 G A' B C ).
 assumption.
assert (Cong A G B G).
 assert (Cong A G C G).
  apply (perp_bisect_cong2 G B' A C).
  assumption.
 CongR.
apply 垂线共线点也构成垂直2 with C'; Col.
apply 垂直的右交换性.
apply 直角转L形垂直; auto.
 apply 严格中点组推论1 with B; 中点.
exists B.
split; Cong.
Qed.

Lemma 外心的唯一性 :
   forall A B C O O',
  A<>B -> B<>C -> A<>C ->
  外心 O A B C ->
  外心 O' A B C ->
  O = O'.
Proof.
intros A B C O O' HAB HBC HAC HIC1 HIC2.
elim (共线的决定性 A B C); intro HABC.

  {
  Name C' the midpoint of A and B.
  assert (HPer1 : Perp_bisect O C' A B).
    {
    unfold 外心 in *; spliter; apply cong_mid_perp_bisect; Cong.
    intro; treat_equalities; assert (HFalse := 共线点间距相同要么重合要么中点 O B C).
    destruct HFalse; Cong.
      ColR.
    treat_equalities; auto.
    }
  Name A' the midpoint of B and C.
  assert (HPer2 : Perp_bisect O A' B C).
    {
    unfold 外心 in *; spliter; apply cong_mid_perp_bisect; Cong.
    intro; treat_equalities; assert (HFalse := 共线点间距相同要么重合要么中点 O A B).
    destruct HFalse; Cong.
      ColR.
    treat_equalities; auto.
    }
  assert (HPar : 严格平行 O A' O C').
    {
    apply par_not_col_strict with C'; Col.

      {
      apply l12_9 with A B; [Cop..| |Cop| |apply perp_bisect_perp; assumption].
        apply col__coplanar; ColR.
      apply 与垂线共线之线也为垂线1 with B C; Perp; Col.
      }

      {
      show_distinct A' C'; try (apply HAC; apply 中点组的唯一性1 with B A';
      unfold 中点 in *; spliter; split; Cong; Between).
      intro; assert (HFalse := 共线点间距相同要么重合要么中点 O A B); elim HFalse; clear HFalse; try intro HFalse;
      unfold 外心 in *; spliter; Cong; 统计不重合点; assert_cols; try ColR.
      assert (HOC' : O <> C').
        {
        apply perp_bisect_equiv_def in HPer1.
        apply perp_bisect_equiv_def in HPer2.
        unfold Perp_bisect in *; unfold 垂直于 in *;
        destruct HPer1 as [I [HOC' Hc1]]; 统计不重合点; Col.
        }
      apply HOC'; apply 中点的唯一性1 with A B; Col.
      }
    }
  assert (HFalse := not_par_strict_id O A' C'); exfalso; apply HFalse; Col.
  }

  {
  Name C' the midpoint of A and B.
  elim (两点重合的决定性 O C'); intro HOC'; elim (两点重合的决定性 O' C'); intro HO'C';
  treat_equalities; Col.

    {
    assert (HPer : Per A C B).
      {
      apply 泰勒斯定理 with O; Col.
      apply 外心与三角形顶点距离相等 in HIC1; spliter; Cong.
      }
    Name B' the midpoint of A and C.
    assert (HO'B' : O' <> B').
      {
      intro; treat_equalities.
      assert (HPer2 : Per A B C).
        {
        apply 泰勒斯定理 with O'; Col.
        unfold 外心 in *; spliter; Cong.
        }
      assert (HPar : 严格平行 A B A C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with B C; [Cop..| |apply 垂直的右交换性]; apply 直角转L形垂直; Perp.
        }
      assert (HFalse := not_par_strict_id A B C); exfalso; apply HFalse; Col.
      }
    Name A' the midpoint of B and C.
    assert (HO'A' : O' <> A').
      {
      intro; treat_equalities.
      assert (HPer2 : Per B A C).
        {
        apply 泰勒斯定理 with O'; Col.
        unfold 外心 in *; spliter; Cong.
        }
      assert (HPar : 严格平行 B A B C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with A C; [Cop..| |apply 垂直的右交换性]; apply 直角转L形垂直; Perp.
        }
      assert (HFalse := not_par_strict_id B A C); exfalso; apply HFalse; Col.
      }
    assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' O A B).
      {
      apply 外心与任一边中点连线是该边中垂线; Col.
      }
    destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
    assert (HPer1 : Perp_bisect O A' B C).
      {
      unfold 外心 in *; spliter.
      apply cong_mid_perp_bisect; Cong.
      intro; treat_equalities; apply HABC; Col.
      }
    assert (HPer2 : Perp_bisect O B' A C).
      {
      apply 外心与三角形顶点距离相等 in HIC1; spliter.
      apply cong_mid_perp_bisect; Cong.
      intro; treat_equalities; apply HABC; Col.
      }
    apply l6_21_两线交点的唯一性 with O A' B' O'; Col.

      {
      assert (HRect : 长方形 C B' O A').
        {
        apply 直角三角形三边中点和直角顶点形成长方形 with B A; Perp; unfold 中点 in *; spliter;
        split; Between; Cong.
        }
      destruct HRect as [HPara Hc]; clear Hc.
      apply plg_to_parallelogram in HPara.
      apply plg_permut in HPara.
      intro HOA'B'; apply plg_col_plgf in HPara; Col.
      destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
      统计不重合点; assert_cols; apply HABC; ColR.
      }

      {
      apply 等价共线CAB, cop_perp2__col with B C; Perp; CopR.
      }

      {
      apply 等价共线ACB, cop_perp2__col with A C; Perp; CopR.
      }
    }

    {
    assert (HPer : Per A C B).
      {
      apply 泰勒斯定理 with O'; Col.
      apply 外心与三角形顶点距离相等 in HIC2; spliter; Cong.
      }
    Name B' the midpoint of A and C.
    assert (HOB' : O <> B').
      {
      intro; treat_equalities.
      assert (HPer2 : Per A B C).
        {
        apply 泰勒斯定理 with O; Col.
        unfold 外心 in *; spliter; Cong.
        }
      assert (HPar : 严格平行 A B A C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with B C; [Cop..| |apply 垂直的右交换性]; apply 直角转L形垂直; Perp.
        }
      assert (HFalse := not_par_strict_id A B C); exfalso; apply HFalse; Col.
      }
    Name A' the midpoint of B and C.
    assert (HOA' : O <> A').
      {
      intro; treat_equalities.
      assert (HPer2 : Per B A C).
        {
        apply 泰勒斯定理 with O; Col.
        unfold 外心 in *; spliter; Cong.
        }
      assert (HPar : 严格平行 B A B C).
        {
        apply par_not_col_strict with C; Col.
        apply l12_9 with A C; [Cop..| |apply 垂直的右交换性]; apply 直角转L形垂直; Perp.
        }
      assert (HFalse := not_par_strict_id B A C); exfalso; apply HFalse; Col.
      }
    assert (H : Perp_bisect O A' B C /\ Perp_bisect O B' A C /\ Perp_bisect O O' A B).
      {
      apply 外心与任一边中点连线是该边中垂线; Col.
      }
    destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
    assert (HPer1 : Perp_bisect O' A' B C).
      {
      unfold 外心 in *; spliter.
      apply cong_mid_perp_bisect; Cong.
      intro; treat_equalities; apply HABC; Col.
      }
    assert (HPer2 : Perp_bisect O' B' A C).
      {
      apply 外心与三角形顶点距离相等 in HIC2; spliter.
      apply cong_mid_perp_bisect; Cong.
      intro; treat_equalities; apply HABC; Col.
      }
    apply l6_21_两线交点的唯一性 with O' A' B' O; Col.

      {
      assert (HRect : 长方形 C B' O' A').
        {
        apply 直角三角形三边中点和直角顶点形成长方形 with B A; Perp; split; Between; Cong.
        }
      destruct HRect as [HPara Hc]; clear Hc.
      apply plg_to_parallelogram in HPara.
      apply plg_permut in HPara.
      intro HO'A'B'; apply plg_col_plgf in HPara; Col.
      destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
      统计不重合点; assert_cols; apply HABC; ColR.
      }

      {
      apply 等价共线CAB, cop_perp2__col with B C; Perp; CopR.
      }

      {
      apply 等价共线ACB, cop_perp2__col with A C; Perp; CopR.
      }
    }

    {
    Name B' the midpoint of A and C.
    elim (两点重合的决定性 O B'); intro HOB'; elim (两点重合的决定性 O' B'); intro HO'B';
    treat_equalities; Col.

      {
      assert (HPer : Per A B C).
        {
        apply 泰勒斯定理 with O; Col.
        unfold 外心 in *; spliter; Cong.
        }
      Name A' the midpoint of B and C.
      assert (HO'A' : O' <> A').
        {
        intro; treat_equalities.
        assert (HPer2 : Per B A C).
          {
          apply 泰勒斯定理 with O'; Col.
          unfold 外心 in *; spliter; Cong.
          }
        assert (HPar : 严格平行 A C B C).
          {
          apply par_not_col_strict with B; Col.
          apply l12_9 with A B; [Cop..|apply 垂直的左交换性|apply 垂直的交换性]; apply 直角转L形垂直; Perp.
          }
        assert (HFalse := not_par_strict_id C A B); exfalso; apply HFalse; Par.
        }
      assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' O A C /\ Perp_bisect O' C' A B).
        {
        apply 外心与任一边中点连线是该边中垂线; Col.
        }
      destruct H as [HPer3 [Hc HPer4]]; clear Hc.
      assert (HPer1 : Perp_bisect O A' B C).
        {
        unfold 外心 in *; spliter.
        apply cong_mid_perp_bisect; Cong.
        intro; treat_equalities; apply HABC; Col.
        }
      assert (HPer2 : Perp_bisect O C' A B).
        {
        unfold 外心 in *; spliter.
        apply cong_mid_perp_bisect; Cong.
        }
      apply l6_21_两线交点的唯一性 with O A' C' O'; Col.

        {
        assert (HRect : 长方形 B A' O C').
          {
          apply 直角三角形三边中点和直角顶点形成长方形 with A C; Perp; split; Between; Cong.
          }
        destruct HRect as [HPara Hc]; clear Hc.
        apply plg_to_parallelogram in HPara.
        apply plg_permut in HPara.
        intro HOA'C'; apply plg_col_plgf in HPara; Col.
        destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
        统计不重合点; assert_cols; apply HABC; ColR.
        }

        {
        apply 等价共线CAB, cop_perp2__col with B C; Perp; CopR.
        }

        {
        apply 等价共线ACB, cop_perp2__col with A B; Perp; CopR.
        }
      }

      {
      assert (HPer : Per A B C).
        {
        apply 泰勒斯定理 with O'; Col.
        unfold 外心 in *; spliter; Cong.
        }
      Name A' the midpoint of B and C.
      assert (HOA' : O <> A').
        {
        intro; treat_equalities.
        assert (HPer2 : Per B A C).
          {
          apply 泰勒斯定理 with O; Col.
          unfold 外心 in *; spliter; Cong.
          }
        assert (HPar : 严格平行 A C B C).
          {
          apply par_not_col_strict with B; Col.
          apply l12_9 with A B; [Cop..|apply 垂直的左交换性|apply 垂直的交换性]; apply 直角转L形垂直; Perp.
          }
        assert (HFalse := not_par_strict_id C A B); exfalso; apply HFalse; Par.
        }
      assert (H : Perp_bisect O A' B C /\ Perp_bisect O O' A C /\ Perp_bisect O C' A B).
        {
        apply 外心与任一边中点连线是该边中垂线; Col.
        }
      destruct H as [HPer3 [Hc HPer4]]; clear Hc.
      assert (HPer1 : Perp_bisect O' A' B C).
        {
        unfold 外心 in *; spliter.
        apply cong_mid_perp_bisect; Cong.
        intro; treat_equalities; apply HABC; Col.
        }
      assert (HPer2 : Perp_bisect O' C' A B).
        {
        unfold 外心 in *; spliter.
        apply cong_mid_perp_bisect; Cong.
        }
      apply l6_21_两线交点的唯一性 with O' A' C' O; Col.

        {
        assert (HRect : 长方形 B A' O' C').
          {
          apply 直角三角形三边中点和直角顶点形成长方形 with A C; Perp; split; Between; Cong.
          }
        destruct HRect as [HPara Hc]; clear Hc.
        apply plg_to_parallelogram in HPara.
        apply plg_permut in HPara.
        intro HO'A'C'; apply plg_col_plgf in HPara; Col.
        destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
        统计不重合点; assert_cols; apply HABC; ColR.
        }

        {
        apply 等价共线CAB, cop_perp2__col with B C; Perp; CopR.
        }

        {
        apply 等价共线ACB, cop_perp2__col with A B; Perp; CopR.
        }
      }

      {
      Name A' the midpoint of B and C.
      elim (两点重合的决定性 O A'); intro HOA'; elim (两点重合的决定性 O' A'); intro HO'A';
      treat_equalities; Col.
        {
        assert (HPer : Per C A B).
          {
          unfold 外心 in *; spliter.
          apply 直角的对称性, 泰勒斯定理 with O; Col; Cong.
          }
        assert (H : Perp_bisect O' O B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' C' A B).
          {
          apply 外心与任一边中点连线是该边中垂线; Col.
          }
        destruct H as [Hc [HPer3 HPer4]]; clear Hc.
        assert (HPer1 : Perp_bisect O B' A C).
          {
          apply 外心与三角形顶点距离相等 in HIC1; spliter.
          apply cong_mid_perp_bisect; Cong.
          }
        assert (HPer2 : Perp_bisect O C' A B).
          {
          unfold 外心 in *; spliter.
          apply cong_mid_perp_bisect; Cong.
          }
        apply l6_21_两线交点的唯一性 with O B' C' O'; Col.

          {
          assert (HRect : 长方形 A B' O C').
            {
            apply 直角三角形三边中点和直角顶点形成长方形 with B C; Perp; split; Between; Cong.
            }
          destruct HRect as [HPara Hc]; clear Hc.
          apply plg_to_parallelogram in HPara.
          apply plg_permut in HPara.
          intro HOB'C'; apply plg_col_plgf in HPara; Col.
          destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
          统计不重合点; assert_cols; apply HABC; ColR.
          }

          {
          apply 等价共线CAB, cop_perp2__col with A C; Perp; CopR.
          }

          {
          apply 等价共线ACB, cop_perp2__col with A B; Perp; CopR.
          }
        }

        {
        assert (HPer : Per C A B).
          {
          unfold 外心 in *; spliter.
          apply 直角的对称性, 泰勒斯定理 with O'; Col; Cong.
          }
        assert (H : Perp_bisect O O' B C /\ Perp_bisect O B' A C /\ Perp_bisect O C' A B).
          {
          apply 外心与任一边中点连线是该边中垂线; auto.
          }
        destruct H as [Hc [HPer3 HPer4]]; clear Hc.
        assert (HPer1 : Perp_bisect O' B' A C).
          {
          apply 外心与三角形顶点距离相等 in HIC2; spliter; apply cong_mid_perp_bisect; Cong.
          }
        assert (HPer2 : Perp_bisect O' C' A B).
          {
          unfold 外心 in *; spliter; apply cong_mid_perp_bisect; Cong.
          }
        apply l6_21_两线交点的唯一性 with O' B' C' O; Col.

          {
          assert (HRect : 长方形 A B' O' C').
            {
            apply 直角三角形三边中点和直角顶点形成长方形 with B C; Perp; split; Between; Cong.
            }
          destruct HRect as [HPara Hc]; clear Hc.
          apply plg_to_parallelogram in HPara.
          apply plg_permut in HPara.
          intro HO'B'C'; apply plg_col_plgf in HPara; Col.
          destruct HPara as [Hc1 [HCol2 Hc2]]; clear Hc1; clear Hc2.
          统计不重合点; assert_cols; apply HABC; ColR.
          }

          {
          apply 等价共线CAB, cop_perp2__col with A C; Perp; CopR.
          }

          {
          apply 等价共线ACB, cop_perp2__col with A B; Perp; CopR.
          }
        }

        {
        assert (H : Perp_bisect O A' B C /\ Perp_bisect O B' A C /\ Perp_bisect O C' A B).
          {
          apply 外心与任一边中点连线是该边中垂线; auto.
          }
        destruct H as [HPer1 [HPer2 Hc]]; clear Hc.
        assert (H : Perp_bisect O' A' B C /\ Perp_bisect O' B' A C /\ Perp_bisect O' C' A B).
          {
          apply 外心与任一边中点连线是该边中垂线; auto.
          }
        destruct H as [HPer3 [HPer4 Hc]]; clear Hc.
        apply l6_21_两线交点的唯一性 with O A' B' O; Col.

          {
          intro HOA'B'; assert (HPar : 严格平行 A C C B).
            {
            apply par_not_col_strict with B; Col.
            apply l12_9 with O A'; try CopR.
              apply 与垂线共线之线也为垂线1 with O B'; Col; Perp.
            Perp.
            }
          assert (HFalse := not_par_strict_id C A B); apply HFalse; Par.
          }

          {
          apply 等价共线CAB, cop_perp2__col with B C; Perp; CopR.
          }

          {
          apply 等价共线ACB, cop_perp2__col with A C; Perp; CopR.
          }
        }
      }
    }
  }
Qed.


End Circumcenter2.

Section Circumcenter3.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma 直角三角形斜边中点是其外心 :
  forall A B C O: Tpoint,
   Per A C B ->
   中点 O A B ->
   外心 O A B C.
Proof.
intros.
assert (T:= 直角三角形斜边中线是斜边一半 A B C O H H0).
spliter.
split;finish.
Qed.

Lemma 直角三角形的外心是斜边中点 :
 forall A B C O,
 A<>B -> B<>C ->
 Per A B C ->
 外心 O A B C ->
 中点 O A C.
Proof.
intros.

Name O' the midpoint of A and C.
assert (T:= 直角三角形斜边中点是其外心 A C B O' H1 H4).
assert (O=O').
apply 外心的唯一性 with A B C;finish.
intro.
treat_equalities.
apply ABA直角则A与B重合 in H1.
intuition.
auto using 等价外心ACB.
subst;auto.
Qed.

End Circumcenter3.