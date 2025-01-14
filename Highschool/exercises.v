Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Highschool.varignon.

Section Exercises.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma 直角三角形三边中点和直角顶点形成长方形 : forall A B C I J K,
  A <> B ->
  B <> C ->
  Per B A C ->
  中点 I B C ->
  中点 J A C ->
  中点 K A B ->
  长方形 A J I K.
Proof.
intros.
统计不重合点.
assert_cols.
elim (两点重合的决定性 A C); intro; apply plg_per_rect.

  treat_equalities.
  assert (HM : exists M : Tpoint, 中点 M J I) by (apply 中点的存在性); decompose [ex] HM; repeat split; intuition; exists x; intuition.

  treat_equalities; intuition.

  assert( Par A B J I /\ Par A C I K /\ Par B C J K /\
    Cong A K I J /\ Cong B K I J /\ Cong A J I K /\ Cong C J I K /\ Cong B I J K /\ Cong C I J K)
  by (apply 广义三角形中位线定理综合; intuition).
  分离合取式.

  elim (共线的决定性 A B C); intro; 统计不重合点.

    apply parallelogram_to_plg; unfold 平行四边形; right; unfold 退化平行四边形; repeat split.
    ColR.
    ColR.
    assumption.

    assumption.

    right; intro; subst; assert (B = C) by (apply 中点组的唯一性1 with A K; assumption); contradiction.

    apply pars_par_plg.

      assert (严格平行 A B J I /\ 严格平行 A C I K /\ 严格平行 B C J K /\
        Cong A K I J /\ Cong B K I J /\ Cong A J I K /\ Cong C J I K /\ Cong B I J K /\ Cong C I J K)
      by (apply 三角形中位线定理综合; intuition).
      分离合取式.
      apply par_strict_symmetry; apply par_strict_col_par_strict with C; intuition; apply par_strict_symmetry; apply par_strict_right_comm; assumption; Col.
      Par.
      Col.

      assert (严格平行 A B J I /\ 严格平行 A C I K /\ 严格平行 B C J K /\
        Cong A K I J /\ Cong B K I J /\ Cong A J I K /\ Cong C J I K /\ Cong B I J K /\ Cong C I J K)
      by (apply 三角形中位线定理综合; intuition).
      分离合取式.
      apply par_symmetry; apply par_col_par with B; intuition; apply par_symmetry; apply par_strict_par; assumption.

  left; apply l8_3_直角边共线点也构成直角1 with B; try apply 直角的对称性; try apply l8_3_直角边共线点也构成直角1 with C; try apply 直角的对称性; try assumption; intuition; Col.

Qed.

(**
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
        codebase="http://www.geogebra.org/webstart/4.0/unsigned/"
        width="796" height="466">
        <param name="ggbBase64" value="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" />
        <param name="image" value="http://www.geogebra.org/webstart/loading.gif" />
        <param name="boxborder" value="false" />
        <param name="centerimage" value="true" />
        <param name="java_arguments" value="-Xmx512m -Djnlp.packEnabled=true" />
        <param name="cache_archive" value="geogebra.jar, geogebra_main.jar, geogebra_gui.jar, geogebra_cas.jar, geogebra_algos.jar, geogebra_export.jar, geogebra_javascript.jar, jlatexmath.jar, jlm_greek.jar, jlm_cyrillic.jar, geogebra_properties.jar" />
        <param name="cache_version" value="4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0, 4.0.19.0" />
        <param name="showResetIcon" value="false" />
        <param name="showAnimationButton" value="true" />
        <param name="enableRightClick" value="false" />
        <param name="errorDialogsActive" value="true" />
        <param name="enableLabelDrags" value="false" />
        <param name="showMenuBar" value="false" />
        <param name="showToolBar" value="false" />
        <param name="showToolBarHelp" value="false" />
        <param name="showAlgebraInput" value="false" />
        <param name="useBrowserForJS" value="true" />
        <param name="allowRescaling" value="true" />
C'est une appliquette Java créée avec GeoGebra ( www.geogebra.org) - Il semble que Java ne soit pas installé sur votre ordinateur, merci d'aller sur www.java.com
</applet>
*)

Ltac 统计不重合点_by_cases :=
 repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;induction (两点重合的决定性 A B);[treat_equalities;solve [finish|trivial] |idtac]
end.

Lemma 四边形对边中点连线互相平分:
 forall A B C D I J K L X Y,
  ~ Col I J K ->
  中点 I A B ->
  中点 J B C ->
  中点 K C D ->
  中点 L A D ->
  中点 X I K ->
  中点 Y J L ->
  X = Y.
Proof.
intros.
统计不重合点_by_cases.
assert (平行四边形 I J K L)
  by (apply (瓦里尼翁平行四边形 A B C D I J K L);finish).
assert (中点 X J L)
  by (perm_apply (plg_mid_2 I J K L X)).
treat_equalities;trivial.
Qed.


End Exercises.
