Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Highschool.circumcenter.
Require Export GeoCoq.Highschool.orthocenter.
Require Export GeoCoq.Highschool.midpoint_thales.
Require Export GeoCoq.Highschool.concyclic.
Require Export GeoCoq.Highschool.gravityCenter.

Import concyclic.

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
      | H:垂心 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 垂心与三角形共面, H)
      | H:重心 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 重心与三角形共面, H)
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

Section 欧拉线定理.

Context `{TE:塔斯基公理系统_欧几里得几何}.

(**
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
        codebase="http://www.geogebra.org/webstart/4.0/unsigned/"
        width="796" height="466">
        <param name="ggbBase64" value="UEsDBBQACAAIALt4u0QAAAAAAAAAAAAAAAAWAAAAZ2VvZ2VicmFfamF2YXNjcmlwdC5qc0srzUsuyczPU0hPT/LP88zLLNHQVKiuBQBQSwcI1je9uRkAAAAXAAAAUEsDBBQACAAIALt4u0QAAAAAAAAAAAAAAAAMAAAAZ2VvZ2VicmEueG1s3VvbcptIGr7OPEWXLvYqQn0GsnKmnGRm4qpkPLXObm3tTQpBWyJGoAFkS6l5qX2Rfab9uxsQCEuxHNtRksRpoH/68H3/qbvx+OfVPEHXKi/iLD0ZEAcPkErDLIrT6clgWV4OvcHPL38aT1U2VZM8QJdZPg/KkwHXknF0MsBeNPGFr4ZcRRL+CydDf3JJhhPJsO9j5bJADBBaFfGLNPs9mKtiEYTqIpypefAuC4PSdDwry8WL0ejm5sapu3KyfDqaTifOqogGCIaZFieD6uIFNNd56YYZcYoxGf37/Tvb/DBOizJIQzVAegrL+OVPz8Y3cRplN+gmjsrZycDDMI2ZiqczmJPUNyMttABAFios42tVwKutWzPncr4YGLEg1fXP7BVKmukMUBRfx5HKAR+HCuYCBFkeq7SsBEjV0ahuYnwdqxvblr4y3fABKrMsmQS6GfTXX4hiitFzXRBbUCiktFXYPsPMFtQW3BbCynD7Orei3MpwK8PZAF3HRTxJ1MngMkgKgC1OL3OgrLkvynWizHiqB5spk+cwpyL+DMJM42hxhucYP9c/AO5zXgPcmiRp9VrmywM7rbsUHrt7l/RrumR1lxTf0iUVO2Yp94Brx3CXaRLRQha6Mv/MT69HRg/o0d5/XYeSP8kUx6PaUsaVcaBipmUrJks1L7S5MB8JX2s9QQJMQ7qg5AIRHwqXIjAGRATiAm6Jh6QuXcRcqOCIIQ9pOcKQsQ3hwX/cNY1JJKAx/dQFk0QEOuJIMESMSXEEhoSMWYKJUgYSQiABL+nuCdVNMIm4hDvmIQ5j1BbpEhBk8CLcQ/cUMYKYfpm4iEokdXuEa0uXnh46NEmRxEgS3SAYNRi0NWaQ9xDTs5EVXHG6WJYdiMJ5VF+W2aLhAqTBHW08nXVPHUf4bJwEE5VAbLjQTCJ0HSTaIkxHl1laoppEap9N82Axi8PiQpUlvFWgT8F18C4o1epXkC7qvo1smKXFH3lWvs6S5TwtEAqzBDdjzhLSuqbNqOGGtSp4u0K0KmTr2r213wxq0LJQ0H+WF7V4EEVnWmLjGgDJ8zRZv8pVcLXI4u40xiMTZsZqGSZxFAfpv0BZdS8aF1RHHeOt6qjDuVcPJMuji3UBGoxW/1F5Bj6GE4eL1l93gNa2imHpEG/zF8y9CANte1x034HYs95ZZXpW1w1BwUpt5jrNtWG3bs6KV1myeWSm/zpYlMvc5Aswq1xP6jSdJsqoiDFsCMbh1SRbXVjdYLatD+sF3GE7gsnUwI7ANVABA55W5cSWRkYPrZHCRgYbCVwrWxw19cSnRsKUE1saKdBeO7RqqqSeJsF1N3FhM5tBZTa1s9K6r2P7Mo3Ld/VNGYdXm6nqF35fzieq0aBum+Sh2hyPtlRsfKXyVCWVRgOZy2xZWANtKXukwngOt7aigiTQdP0TBmCfRmqaq3rgicnFLGCmFreVtffYNPVrns3P0usPoAtbAxiP6lGOizCPF1rn0ASiwJXaaFUUFwEEkaj9njZBmHqogwXAU2powDiX5SzLTboFPgVKbXmJmkOehUqjXkZDG5hPTdam8UTZ5BO4tSby2foNYVB9q6oZpQySxSzQmV016SRYq7wDg2nvfRZtgwPYmxmAjS8stwulrFrY8cLFApoz1tTxUYB2gVYwAAf0ea3zbx/i7WebstucVU9Vm1jHK9unWzyB8liUvoDXq+8fryFzhGcQw452BY+M2OvvHzHu6GR1rXFiD6NiYTafB2mEUpMK/pEl62mWDjbJSYC1aaKAaI1DAdUwWoyWZV2/gLeIlQmtTAAFhP6J7a3q4xZ6bG81AbadbiAoIUW5gmVYYZYGZRWXzMXbOIqUSU9H+4ltQdlmlghmuBWkilQbaskh1O7Wv0JN9V0zkPALGnj4QA/UwbYmwXq1/UcYvRoKx/WsYvmOi/2WDNuO0XenRv2Z2lcKGzjj+SKJw7hsNCnROn+WlhBGlYkj/eh4pdRCpyXn6Yc8SAu912FlWlH3jjQEx0PDEDu8ywPmhgjXca2BDz1HUs439eSH4WFyRDwwR3ZpqOyBOL609uCCBG3x8D3ZQ9fLv48jGxlvdfN9//7mS268HWXf3CvK6g2KqS0mtvh6ThmswQyJcPEYwfIdML8F4SsL4ZsehNF+CLUSNQhFfQS7K5IddtFddj2EUUBCazNa6bjWCoZEpyDS25hBb+n2MGZwsPZW0J/2oP/lEO395Wi0FyKD9A341PHZ06jvL7s8gDpAfdWxqC9xhF+txzxRaS+4AgKZ8xOrbOPJt/COLN6qh/dvh+jsb0ejs5Az+syVmPnVH2bwF8SRTFZxlAItRPAHVOTzvJxlsI4IkltUugpqQQ/iywNU+vJYVHpo08L1rsTR5u0E02/poPfyUbnpSY+P6QF8TI+FD5sdrnfkj5oN7DDqtdh4pOz9cN9zaYmY9oh4e4jveXs0vkdyhzPie7wB2uyTQNrOPMlb1mCcECyqPLdlPw/pj7TWv4o15Fm+BXrfDc0OUPvZsaj9HdwQdVzS3j14rOXSvWjoe5/4ABriY6Hhi95HONglLRKePBTscj4z63ziHg/nhzif86NxPq4jhU9JQ4J1Ppw7wsMbN1OtQh/V+byP87yn71USdN6D+/RvwSIr/n4I6PUr94H+wfbSW64IckspMfGES13OKOey3rjxIBxwxrkAXijB3iOsoV7HeZhspzjn9Xb5NtpX+3EOszQOGwSv7rc59kBO5l4uIp6q9Nr42wKhFa4+WVtj2z/6XD9ZERM4dB2pHn0mLWrmQZnHK3Ray5/WUqdUE6tDi8CccNcnVAq9X33Kqj5OuWmaSun74PuYpB5zjYQwOiEEh+SYui6HVMGvT/e3nZv+rCK+BDL2kr/3sKQ2E3Mc0lcFfdRBq1T4I6kOTcwFzCS4m1X2D0/o0x+emLJnzvwQbTtgw/gj+bot49tHe/+c03Hdto8hdTT2Oi7JBmPuEN/3hCRSr4yJFI+0DfEtDlSOjJchuAjRcf5us5tPmO8RTl0qpCuEqM9YsE+wzyXFwncfa4PoWzBzp2j9xOzsOHtsjh6H3/XZYzdImM+ttkNEExs2p+r9fev//Xd/ADCf8zQUgrR+H0a1rHCHYOdi15eMShcinS+9L7n6fUkbwf2c4q6n5F+x7AjysJWj1V9SJEl28w91maiVgfeuXNwesF9bHt7WodqE4FZi3IvbrPrUoY7bszpuTz7qkM4bq/tIDg/h7OlCOO4Y91N8/nDfMLF7pA8XIojcGyIIOC1CPb3BxJmPBfueXNJ+WmZHRAtzSDejaj5L8WhnlWdJkXopwDdx+8cJ3NqXHAspO7KpHZbyo+dSR2Qtw21zqZi53VqEwzyPNx6M+nuYYUfGzJ0+AXjbXXpvx+6zQ7a5zo5mbxE71O/tsBvzI6zz+DE+EriobOAgoD/tB3rbrj59052uDdDC8SlYiPR8zPQv4NF6Ne8TiplLuOCehESa1QccGDJr7rrg6KRHiHsXR0eOxJ5G7Y/2za/GVL/Z+fL/UEsHCHiX1BNKCgAAdjoAAFBLAQIUABQACAAIALt4u0TWN725GQAAABcAAAAWAAAAAAAAAAAAAAAAAAAAAABnZW9nZWJyYV9qYXZhc2NyaXB0LmpzUEsBAhQAFAAIAAgAu3i7RHiX1BNKCgAAdjoAAAwAAAAAAAAAAAAAAAAAXQAAAGdlb2dlYnJhLnhtbFBLBQYAAAAAAgACAH4AAADhCgAAAAA=" />
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

Lemma concyclic_not_col_or_eq_aux :
  forall A B C D, 共圆 A B C D -> A = B \/ A = C \/ B = C \/ ~ Col A B C.
Proof.
intros A B C D HC.
elim (两点重合的决定性 A B); intro HAB; Col.
elim (两点重合的决定性 A C); intro HAC; Col.
elim (两点重合的决定性 B C); intro HBC; Col5.
right; right; right; intro HCol.
destruct HC as [HCop [O [HCong1 [HCong2 HCong3]]]].
assert (H := 中点的存在性 A B); destruct H as [M1 HMid1].
assert (HOM1 : O <> M1).
  {
  intro; treat_equalities.
  assert (H := 共线点间距相同要么重合要么中点 O A C); elim H; clear H; try intro H; Cong;
  try (apply HBC; apply 中点组的唯一性1 with A O; Col);
  assert_cols; ColR.
  }
assert (H := 中点的存在性 A C); destruct H as [M2 HMid2].
assert (HOM2 : O <> M2).
  {
  intro; treat_equalities.
  assert (H := 共线点间距相同要么重合要么中点 O A B); elim H; clear H; try intro H; Cong;
  try (apply HBC; apply 中点组的唯一性1 with A O; Col);
  assert_cols; ColR.
  }
assert (HM1M2 : M1 <> M2) by (intro; treat_equalities; Col).
assert (HPerp1 : Perp_bisect O M1 A B)
  by (apply cong_mid_perp_bisect; spliter; Cong).
assert (HPerp2 : Perp_bisect O M2 A C)
  by (apply cong_mid_perp_bisect; spliter; Cong).
assert (HOM1M2 : ~ Col O M1 M2).
  {
  intro HOM1M2; assert (H := 共线点间距相同要么重合要么中点 O A B); elim H; clear H; try intro H; Cong;
  try (apply HOM1; apply 中点的唯一性1 with A B; Col); 统计不重合点; assert_cols; ColR.
  }
assert (H严格平行 : 严格平行 O M1 O M2).
  {
  apply par_not_col_strict with M2; Col.
  apply l12_9 with A B; try CopR.
    apply coplanar_perm_16, col_cop__cop with C; Col; Cop.
    apply perp_bisect_perp; Col.
  apply 与垂线共线之线也为垂线1 with A C; Col; perm_apply perp_bisect_perp.

  }
assert (H := not_par_strict_id O M1 M2); Col.
Qed.

Lemma concyclic_not_col_or_eq :
  forall A B C A', 共圆 A B C A' ->
  A'=C \/ A'=B \/ A=B \/ A=C \/ A=A' \/ (~ Col A B A' /\ ~ Col A C A').
Proof.
intros A B C A' H.
assert (H' := H); apply 等价共圆ABDC in H; apply 等价共圆ACDB in H'.
apply concyclic_not_col_or_eq_aux in H; apply concyclic_not_col_or_eq_aux in H'.
elim (两点重合的决定性 A' C); intro; try tauto.
elim (两点重合的决定性 A' B); intro; try tauto.
elim (两点重合的决定性 A B); intro; try tauto.
elim (两点重合的决定性 A C); intro; try tauto.
elim (两点重合的决定性 A A'); intro; try tauto.
do 3 (elim H; clear H; intro H; try tauto); Col.
do 3 (elim H'; clear H'; intro H'; try tauto); Col.
Qed.

Lemma 直角三角形上的欧拉线定理 :
  forall A B C G H O,
  Per A B C ->
  重心 G A B C ->
  垂心 H A B C ->
  外心 O A B C ->
  Col G H O.
Proof.
intros.
assert (H=B).
  apply 直角三角形的垂心与直角顶点重合 with A C;finish.
subst.
assert (中点 O A C).
 apply 直角三角形的外心是斜边中点 with B;finish.
 unfold 垂心 in *;spliter;统计不重合点;finish.
 unfold 垂心 in *;spliter;统计不重合点;finish.
assert (重心 G A C B).
 apply 重心的等价排列 in H1;intuition.
perm_apply (重心在中线上 A C B G O).
Qed.

Lemma gravity_center_change_triangle:
 forall A B C G I B' C',
 重心 G A B C ->
 中点 I B C ->
 中点 I B' C' ->
 ~ Col A B' C' ->
 重心 G A B' C'.
Proof.
intros.
Name G' the midpoint of A and G.
assert (中点 G I G')
  by (apply (重心截中线为二比一 A B C G G' I);finish).
apply (截中线为二比一的点为重心 A B' C' G I G');finish.
Qed.

Lemma 欧拉线定理 :
 forall A B C G H O,
  ~ Col A B C ->
  重心 G A B C ->
  垂心 H A B C ->
  外心 O A B C ->
  Col G H O.
Proof.
intros.
elim (等长的决定性 A B A C); intro.

Name A' the midpoint of B and C.
Name B' the midpoint of A and C.
Name C' the midpoint of A and B.

assert (Perp_bisect A A' B C)
  by (apply cong_mid_perp_bisect; Cong; intro; treat_equalities; apply H0; Col).

assert (Col G A' A)
  by (apply 重心的等价排列 in H1; apply 重心在中线上 with B C; spliter; Col).

unfold 垂心 in *; spliter.

elim (两点重合的决定性 O G); intro; treat_equalities; Col;
elim (两点重合的决定性 O H); intro; treat_equalities; Col.

elim (两点重合的决定性 O A'); intro; treat_equalities.

assert (Col A H O) by (apply cop_perp2__col with B C; Col; Cop; apply perp_bisect_perp; Col).
apply 重心与三角形共面 in H1.
apply 等价共线BCA; apply cop_perp2__col with B C.

CopR.
apply 垂直的对称性; apply 与垂线共线之线也为垂线1 with A O; try apply perp_bisect_perp; Col.
apply 垂直的对称性; apply 与垂线共线之线也为垂线1 with A H; Col.

assert (Col A A' H) by (apply cop_perp2__col with B C; Cop; apply perp_bisect_perp; auto).
assert (Perp_bisect O A' B C) by (统计不重合点; apply 外心与一边中点连线是该边中垂线 with A; auto).
assert (Col A' A O)
  by (apply cop_perp2__col with B C; Perp; Cop).
show_distinct A A'.
  apply H0; Col.
ColR.

Name A' the symmetric of A wrt O.

统计不重合点.

assert (共圆 A B C A').
 unfold 共圆.
 split.
 destruct (两点重合的决定性 A O).
  treat_equalities; Cop.
 apply coplanar_perm_12, col_cop__cop with O; Col; Cop.
 exists O.
 apply 外心与三角形顶点距离相等 in H3.
 spliter.
 assert_congs_perm.
 spliter;repeat (split;finish).

assert (T:=concyclic_not_col_or_eq A B C A' H5).
decompose [or] T;clear T;try contradiction.
 - subst.
   assert (Per A B C).
    apply 泰勒斯定理 with O;finish.
    unfold 外心 in *;spliter;finish.
   apply (直角三角形上的欧拉线定理 A B C G H O);finish.
 - subst.
   assert (Per A C B).
    apply 泰勒斯定理 with O;finish.
    unfold 外心 in *;spliter.
    apply 等长的传递性 with O B;finish.

   apply (直角三角形上的欧拉线定理 A C B G H O);finish.
   apply 等价重心ACB; assumption.
   auto with Orthocenter.
   auto with Circumcenter.

 - unfold 外心 in *;spliter.
   treat_equalities.
   intuition.
 - spliter.

统计不重合点.

assert (Per A B A').
 apply 泰勒斯定理 with O;finish.
 unfold 外心 in *;spliter;finish.

assert (Perp C H A B)
 by (unfold 垂心 in *;spliter;finish).

assert (Perp A' B B A)
 by (apply 直角转L形垂直;finish).

assert (Par C H A' B).
 unfold 共圆 in *; spliter.
 apply 垂心与三角形共面 in H2.
 apply l12_9 with A B; try CopR; Perp.

assert (Perp B H A C)
 by (unfold 垂心 in *;spliter;finish).

assert (Per A C A').
 {
 apply 泰勒斯定理 with O;finish.
 unfold 外心 in *;spliter;finish.
 apply 等长的传递性 with B O;finish.
 }

assert (Perp A' C C A) by (apply 直角转L形垂直;finish).

assert (Par B H C A').
 unfold 共圆 in *; spliter.
 apply l12_9 with A C; try CopR; Perp.

induction (共线的决定性 B H C).
 * assert (H=B \/ H=C) by (apply (垂心与一边共线则必与该边一端点重合 A B C H);finish).
   induction H26.
   + subst H.
     assert (中点 O A C) by (apply (直角三角形的外心是斜边中点) with B;finish).
     assert (Col G O B).
        apply (重心在中线上 A C B G O).
        apply 重心的等价排列 in H1;intuition idtac.
        assumption.
     Col.
   (*  perm_apply (重心在中线上 A C B G O). bug in 8.5 *) 
   + subst H;统计不重合点; intuition.
 * assert (平行四边形 B H C A')
     by (apply par_2_plg;finish).

   assert (T:exists I : Tpoint, 中点 I B C /\ 中点 I H A')
     by (apply plg_mid;finish).

   destruct T as [I [HI1 HI2]].

   elim (直角的决定性 B A C); intro.

   apply 直角三角形上的欧拉线定理 with B A C;
   try apply 重心的各排列情况; auto;
   try apply 垂心的各排列情况; auto;
   try apply 外心的各排列情况; auto.

   assert (重心 G A H A').
     {
     apply gravity_center_change_triangle with B C I;finish.
     show_distinct A' H; treat_equalities.
     apply plg_par in H26; spliter; 统计不重合点; Col.
     intro.
     Name A'' the midpoint of B and C.
     show_distinct A'' O; treat_equalities.
     apply H27; apply L形垂直转直角1; 统计不重合点; Perp.
     assert (Perp_bisect O A'' B C) by (apply 外心与一边中点连线是该边中垂线 with A; Col).
     elim (两点重合的决定性 A A''); intro; treat_equalities.
     eauto using perp_bisect_cong_2 with cong.
     assert (Perp_bisect A'' A B C).
     apply perp_mid_perp_bisect; Col.
     apply 垂直的对称性; apply 与垂线共线之线也为垂线1 with O A''; Col;
     try (apply perp_bisect_perp; assumption); assert_cols; try ColR.
     eauto using perp_bisect_cong_2 with cong.
     }

   assert (重心 G A A' H)
     by (apply 重心的各排列情况;auto).

   perm_apply (重心在中线上 A A' H G O).
Qed.

End 欧拉线定理.
