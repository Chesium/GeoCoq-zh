Require Export GeoCoq.Highschool.circumcenter.

Section Orthocenter.

Context `{TE:塔斯基公理系统_欧几里得几何}.

(**
Orthocenter

#
<applet name="ggbApplet" code="geogebra.GeoGebraApplet" archive="geogebra.jar"
	codebase="http://jars.geogebra.org/webstart/4.2/unsigned/"
	width="1669" height="873">
	<param name="ggbBase64" value="UEsDBBQACAAIAKZIxkIAAAAAAAAAAAAAAAAWAAAAZ2VvZ2VicmFfamF2YXNjcmlwdC5qc0srzUsuyczPU0hPT/LP88zLLNHQVKiuBQBQSwcI1je9uRkAAAAXAAAAUEsDBBQACAAIAKZIxkIAAAAAAAAAAAAAAAAMAAAAZ2VvZ2VicmEueG1s3VpZc9tGEn52fsUUH/bJAuc+vJRTtsuOvVES18q7tbVvIDAiEYEAAoCSqPKP354ZgKcohzpc3NimBkfP9HR//XX3UB79eDPL0ZWtm6wsTgckwgNki6RMs2JyOpi3Fyd68OPrH0YTW07suI7RRVnP4vZ0wCM6WM2Du4grNzlLTweGWyOJHJ+MKfzgKeEnWiTiJBFUEXIRm4uxHSB002SvivLXeGabKk7seTK1s/isTOLWrzlt2+rVcHh9fR312qOyngwnk3F006QDBDsvmtNBd/EKltuYdM28OMWYDP/zy1lY/iQrmjYuEtDvrJpnr394MbrOirS8RtdZ2k7BB1KDaVObTaZgJ8FYDdDQiVVgbWWTNruyDUxeu/VWt7Nq4MXiwr1/Ea5QvjRogNLsKkttfTrAEcEKE8GFUlozrkBjWWe2aDtZ0ukc9quNrjJ7HZZ1V14jxwb2dpU12Ti3p4OLOG/Arqy4qMGnsKF6DrdNu8jtOK77+9V+yEv4CwLZrXVrAXjBEd7ol+6j4CMEDntZVzxAbVnmflWMhEFfvyKKKUYv3UDCQGGQMrzC4RlmYaBh4GEQQYaH6TyI8iDDgwxn99jZ3a8M7R5sWNrbye6yU8LHO2DLTr1mJ3FGfEXE7d4PDLl9E79/N/DuVoZb5QeCw0C6l9r98P6Sj7SIPcgisqY1xMMhSnuVhCvz53XSx+hcmkn0HWZSscfMR3p3qVSsKQVd/p//7Khk9BCVO1x8gEbJH0P+ByhU+HsoHA37VDfqyIeaqZPtYqe1s8alHWZ85kEECWCmVJAoBCIGBuUYShERiAu4JRpJNyrEHCk5YkgjJ0cY8vlFaPjBPWElErCWe6gCcxHjSDBEfFbiCHIR8pkNshxlICEEEjDJaSdOLZOIS7hhGnHYoMtpyuUNBvPgHpRTxAhibi5RiEokKVIuLxLu0qXUbu+wKEUSI+mmQmKEpBgSIszQiDlrIMKrssmWzp3avFqi4v2YFdW83fBdMkv7y7bckk7L5PLtlq9t3LT9NQhBNVrVvFCdNkrii1Eej20OrcO5CwOEruLcMdivf1EWLepDgIZnkzquplnSnNu2hVkN+j2+is/i1t58AOmm36BX7Wv1yM6TPEuzuPg3xIhbwi2IlqXb56W+dGvRqU7Ksk7PFw1EDrr5r61Ll0C0jLgxhhEmGZMGUv0ivFIK3nCmoT4zbLgARzdJ7EKeGhJRLQwlwmgMZRteLbp3xPBIaS41loRTZrQKuu3V0rj4xja9Nye1I1Tnf3fzqXlb5qtHVZkV7bu4aue178QgDdbOqjfFJLfeux506GmSy3F5cx7cysJaXxYV3OGwgfHkXZmXNQJKUiFAoBvHYfQybmdLKexlsJfAPU5ZunxPDPUSfhyH0UsB8GFrnaWkN5PgXk3W+EQCi6+HmY8a1x/Ni6w962/aLLlcWerkf53PxhBw3bTNJckTLTkaboXY6NLWhc1DHBWA5LycNyGyl9H5YjRv7Oe4nb4p0n/aCVDyc+yyYgtLB9HVjlObZDOYGJ53rosdrP+CrYanqZ3Utrcw961vcKx/i9ejeuexX+pDXc4+FVdfIGa2tjoa9vaMmqTOKheaaAxp+tKuoi/NmhiSfLo+D4xvwIrEJRxwZOuc+P7G1kmWWATejOfttKx9lwsEhuqE/jHPCsiXEJWOuLmdQXuLWh+bPryXKL3xfbODA5Xj3yGdbKG4ch68vjNOfUTHeTWNXW/deSKPF7be8I1f75cy3fYYAOLNggxRhdCorA1BFfYLFxUs56m4hrqHoEE3p4MTEkHK4EoA/6FbFZQCFxfA24gLqo3CWlBo111fchuOWeFI4fzgyLuRKsPTLWQhMIMLv+HMt38BZ1J3kgTv+fGZ/fXuL+AvHDEKVcxowxllmHLTu48pyiWcL43iWPGnib6knM3iIkWF7/s+l/liUhaDVccRY0dpFBMXjCimzsfBgfO2f1/BLBJkkiATw8BOB+OgrdNxB3ZBW49OWGez+rTQUlzCqbnxR4+2K4b+4mOWptb3S8P7UV/z8zrsRDAPvCBdeVzhTg7BfX9wNnbi7pYbSb4Rnodv9MAAXYUZ2c5l1EcZRJ+QBB4Rw4yQXCnlw4xHmGrNgR2aGa76hughOEHg5C7+PxWuolpfg3Zr8KW1lWt9fiu+1HHRuG+qNovvn/d6fDxeB/dusVi4lnTh8JCKSYkJFlJJo4R3+wmUHEo0oQYrSAUYWtz/I8ePj8jxEO9ESAFuVFRKzYkK8U4iQihhwhCiKOYASpdWNQBFiCBUYsGpOq6A38zav9XQrUEijfMz2N7dyTveydpTaPLuz8/O2CVYXvyx1fWpsNzhymIvt259C0KVdghLBi0spvQRaNo/ijClCWePbFblWZK190O0xH4LHe/VPQB9/Fb1XO98Pj4IG6k9OG4Yh+EJ4GGRAa4B0QAjBYwL/YuIJKdYwYmawDPpviS/dV2NxlRQwZlRwD9p5BN2M4ewIT2ACumR8ODQYiIizaCCgyTBGFPSf2Pw/WhwByJvAyLjXUT+Fldl8/dDcOlmHAc6B1YcQFMCPaiRgmBDpdbfHZ19Sar3qwcq3QHq/SF56v3x5CkVCezoQLgBSqgAj44o43Dm0owRzo0RXZriBPhFiHTfLsLwvFnqXX+Y2na1PYAN9mHd15MT4cCTBuQuaHgxgWMGVAOpel8fGQ3sDjY/HUKDn46HBjQiHEN4CyyYBp+LroRwrBXhmhLAhivMnp0Ie/2+z+MfDvH4h6PxuAt8CG3NlTvaaeV+9eczDycMCjTnREooDM+fee49N+ytyxcH5KCLo8lBuzV3sadG37peFQsBHSw1rrGS0MEeSQq62AfKz4dQ4eejoQKcFaDnx8JgLRmcznAowiaCKqEN4AGUgD42HONY5OsHoAJPqGCcfy8u7K3HkwO4MDkSLtxVdxd3l+lwdlZKSpgBpww4VEC/dGRkmOygcnYIGc6OiQwQ8PBHSTieSZf3u5OzOw4IyFwa4NJCP0NhGK7/RtD/hr77X3qv/wdQSwcI1ynnbdsIAABVKAAAUEsBAhQAFAAIAAgApkjGQtY3vbkZAAAAFwAAABYAAAAAAAAAAAAAAAAAAAAAAGdlb2dlYnJhX2phdmFzY3JpcHQuanNQSwECFAAUAAgACACmSMZC1ynnbdsIAABVKAAADAAAAAAAAAAAAAAAAABdAAAAZ2VvZ2VicmEueG1sUEsFBgAAAAACAAIAfgAAAHIJAAAAAA==" />
	<param name="java_arguments" value="-Xmx1024m -Djnlp.packEnabled=true" />
	<param name="cache_archive" value="geogebra.jar, geogebra_main.jar, geogebra_gui.jar, geogebra_cas.jar, geogebra_algos.jar, geogebra_export.jar, geogebra_javascript.jar, jlatexmath.jar, jlm_greek.jar, jlm_cyrillic.jar, geogebra_properties.jar" />
	<param name="cache_version" value="4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0, 4.2.47.0" />
	<param name="showResetIcon" value="false" />
	<param name="enableRightClick" value="true" />
	<param name="errorDialogsActive" value="true" />
	<param name="enableLabelDrags" value="false" />
	<param name="showMenuBar" value="true" />
	<param name="showToolBar" value="false" />
	<param name="showToolBarHelp" value="false" />
	<param name="showAlgebraInput" value="false" />
	<param name="useBrowserForJS" value="true" />
	<param name="allowRescaling" value="true" />
C'est une appliquette Java créée avec GeoGebra ( www.geogebra.org) - Il semble que Java ne soit pas installé sur votre ordinateur, merci d'aller sur www.java.com
</applet>
#

**)

(*
Definition 垂心 H A B C :=
 ~ Col A B C /\
 exists A1, exists B1, Perp A A1 B C /\ Perp B B1 A C /\ Col H A A1 /\ Col H B B1.
*)

Definition 垂心 H A B C :=
 ~ Col A B C /\ Perp A H B C /\ Perp B H A C /\ Perp C H A B.

Lemma 垂心与三角形共面 : forall A B C H, 垂心 H A B C -> 共面 H A B C.
Proof.
intros A B C H [HNCol [HPerp]].
apply 等价共面BACD, 垂直蕴含共面, HPerp.
Qed.

Lemma 构造三角形两垂线的交点 : forall A B C X1 X2 X3,
 ~ Col A B C ->
 Par A C B X1 -> Par A B C X2 ->  Par B C A X3 ->
 exists E, Col E A X3 /\ Col E B X1.
Proof.
intros A B C X1 X2 X3 HNC HPar1 HPar2 HPar3.
apply cop_npar__inter_exists.
  CopR.
intro HNPar; apply HNC.
assert (HFalsePar : Par B C A C)
  by (apply (par_trans B C B X1 A C); finish; apply (par_trans B C A X3 B); finish).
perm_apply (par_id C B A).
Qed.

Lemma not_col_par_col_diff : forall A B C D E,
  ~ Col A B C -> Par A B C D -> Col C D E -> A <> E.
Proof.
intros A B C D E HNC HPar HC.
intro; subst.
apply HNC; apply not_strict_par1 with D E; finish.
Qed.

Lemma 反构造中点三角形 : forall A B C,
  ~ Col A B C -> exists D, exists E, exists F,
  Col B D F /\ Col A E F /\ Col C D E /\
  Par A B C D /\ Par A C B D /\ Par B C A E /\
  Par A B C E /\ Par A C B F /\ Par B C A F /\
  D <> E /\ D <> F /\ E <> F.
Proof.
intros A B C HNC.
统计不重合点; rename H2 into HAB; rename H1 into HBC; rename H4 into HAC.

elim (parallel_existence1 A B C HAB);intros X1 HX1.
elim (parallel_existence1 A C B HAC);intros X2 HX2.
elim (parallel_existence1 B C A HBC);intros X3 HX3.

assert (T : exists D, Col D B X2 /\ Col D C X1) by (apply 构造三角形两垂线的交点 with A X3; finish); DecompExAnd T D.
assert (T : exists E, Col E A X3 /\ Col E C X1) by (apply 构造三角形两垂线的交点 with B X2; finish); DecompExAnd T E.
assert (T : exists F, Col F A X3 /\ Col F B X2) by (apply 构造三角形两垂线的交点 with C X1; finish); DecompExAnd T F.

assert (A <> E) by (apply not_col_par_col_diff with B C X1; finish).
assert (A <> F) by (apply not_col_par_col_diff with C B X2; finish).
assert (B <> D) by (apply not_col_par_col_diff with A C X1; finish).
assert (B <> F) by (apply not_col_par_col_diff with C A X3; finish).
assert (C <> D) by (apply not_col_par_col_diff with A B X2; finish).
assert (C <> E) by (apply not_col_par_col_diff with B A X3; finish).

assert (Par A B C D) by (apply par_col_par with X1; finish).
assert (Par A C B D) by (apply par_col_par with X2; finish).
assert (Par B C A E) by (apply par_col_par with X3; finish).
assert (Par A B C E) by (apply par_col_par with X1; finish).
assert (Par A C B F) by (apply par_col_par with X2; finish).
assert (Par B C A F) by (apply par_col_par with X3; finish).

assert (~ (D = E /\ D = F)).

  intro; 分离合取式; treat_equalities.
  assert_paras_perm.
  assert_nparas_perm.
  permutation_intro_in_hyps.
  contradiction.

exists D; exists E; exists F.
统计不重合点.
(*
deduce_cols.
repeat split; try cols; finish; clear_cols; untag_hyps.
*)
repeat split; try ColR; finish.

intro; subst.
assert (E <> F) by (intro; subst; intuition).
apply HNC; apply 等价共线BCA; apply not_strict_par1 with E A; sfinish.

intro; subst.
assert (E <> F) by (intro; subst; intuition).
apply HNC; apply 等价共线CAB; apply not_strict_par1 with E C; sfinish.

intro; subst.
assert (D <> F) by (intro; subst; intuition).
apply HNC; apply not_strict_par1 with D B; sfinish.
Qed.
(* 没看懂 *)
Lemma diff_not_col_col_par4_mid: forall A B C D E,
  D <> E -> ~ Col A B C -> Col C D E -> Par A B C D ->
  Par A B C E -> Par A E B C -> Par A C B D -> 中点 C D E.
Proof.
intros A B C D E HD HNC HC HPar1 HPar2 HPar3 HPar4.
assert (HPara1 : 严格平行四边形 A B C E) by (apply parallel_2_plg; finish).
assert (HPara2 : 严格平行四边形 C A B D) by (apply parallel_2_plg; finish).
assert_congs_perm.
apply 不重合共线点间距相同则为中点组2; Col; CongR.
Qed.
(* 看上去像废话 *)
Lemma altitude_is_perp_bisect : forall A B C O A1 E F,
  A <> O -> E <> F -> Perp A A1 B C -> Col O A1 A -> Col A E F -> Par B C A E -> 中点 A E F ->
  中垂线 A O E F.
Proof with finish.
intros.
apply 过一线中点的垂线是该线中垂线...
apply 垂直的对称性.
apply cop_par_perp__perp with B C...
apply par_col_par with A...
apply 垂线共线点也构成垂直2 with A1...
Qed.

Lemma 两垂线交点在第三条垂线上:
 forall A  A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 Perp A A1 B C  -> Perp B B1 A C -> Perp C C1 A B ->
 Col O A A1 -> Col O B B1 ->
 Col O C C1.
Proof with finish.
intros A A1 B B1 C C1 O HNC HPerp1 HPerp2 HPerp3 HC1 HC2.
assert (HT := HNC).
apply 反构造中点三角形 in HT.
destruct HT as [D [E [F HT]]].
分离合取式.

assert (中点 A E F) by (apply diff_not_col_col_par4_mid with B C; finish).
assert (中点 B D F) by (apply diff_not_col_col_par4_mid with A C; finish).
assert (中点 C D E) by (apply diff_not_col_col_par4_mid with A B; finish).

统计不重合点.
elim (两点重合的决定性 A O); intro.

  treat_equalities; apply 等价共线BAC; apply cop_perp2__col with A B...
  apply 垂直的右交换性; apply 垂线共线点也构成垂直2 with B1...

elim (两点重合的决定性 B O); intro.

  treat_equalities; apply 等价共线BAC; apply cop_perp2__col with A B...
  apply 垂线共线点也构成垂直2 with A1...

elim (两点重合的决定性 C O); intro.

  subst; Col.

assert (中垂线 A O E F) by (apply altitude_is_perp_bisect with B C A1; finish).
assert (中垂线 B O D F) by (apply altitude_is_perp_bisect with A C B1; finish).

assert (Perp O C D E).

  apply 三角形的三条中垂线交于一点 with F A B; finish.
  apply 中垂线左对称性; assumption.
  apply 中垂线左对称性; assumption.

assert (Perp C1 C D E).

  apply 垂直的对称性; apply cop_par_perp__perp with A B...
  apply par_symmetry; apply par_col_par_2 with C...

apply 等价共线CAB; apply cop_perp2__col with D E; Perp.
apply coplanar_pseudo_trans with A B C; Cop.
apply 等价共面ACBD, col_cop__cop with B1; Col; Cop.

Qed.

Lemma 垂心的各排列情况 :
  forall A B C G,
  垂心 G A B C \/
  垂心 G A C B \/
  垂心 G B A C \/
  垂心 G B C A \/
  垂心 G C A B \/
  垂心 G C B A ->
  垂心 G A B C.
Proof.
intros.
decompose [or] H;clear H;
unfold 垂心 in *;分离合取式;
repeat (split; finish).
Qed.

Lemma 垂心的等价排列 : forall A B C G,
 垂心 G A B C ->
 垂心 G A B C /\ 垂心 G A C B /\
 垂心 G B A C /\ 垂心 G B C A /\
 垂心 G C A B /\ 垂心 G C B A.
Proof.
intros.
unfold 垂心 in *.
分离合取式.
repeat split;finish.
Qed.

Lemma 等价垂心ACB : forall A B C G,
 垂心 G A B C -> 垂心 G A C B.
Proof.
intros.
apply 垂心的等价排列 in H;intuition.
Qed.

Lemma 等价垂心BAC : forall A B C G,
 垂心 G A B C -> 垂心 G B A C.
Proof.
intros.
apply 垂心的等价排列 in H;intuition.
Qed.

Lemma 等价垂心BCA : forall A B C G,
 垂心 G A B C -> 垂心 G B C A.
Proof.
intros.
apply 垂心的等价排列 in H;intuition.
Qed.

Lemma 等价垂心CAB : forall A B C G,
 垂心 G A B C -> 垂心 G C A B.
Proof.
intros.
apply 垂心的等价排列 in H;intuition.
Qed.

Lemma 等价垂心CBA : forall A B C G,
 垂心 G A B C -> 垂心 G C B A.
Proof.
intros.
apply 垂心的等价排列 in H;intuition.
Qed.

Lemma 直角三角形的垂心与直角顶点重合 :
 forall A B C H,
 Per A B C ->
 垂心 H A B C ->
 H=B.
Proof.
intros.
unfold 垂心 in *;分离合取式.
统计不重合点.
assert (Perp A B B C) by (apply 直角转L形垂直;finish).
assert (Par A H A B)
 by (apply l12_9 with B C;Cop).
assert (Col A B H)
 by (perm_apply (par_id A B H)).

assert (Par C H B C)
 by (apply l12_9 with A B;finish).
assert (Col B C H)
 by (perm_apply (par_id C B H)).
apply l6_21_两线交点的唯一性 with A B C B;finish.
Qed.

Lemma 垂心与一边共线则必与该边一端点重合 :
 forall A B C H,
 Col H B C ->
 垂心 H A B C ->
 H = B \/ H = C.
Proof.
intros.
unfold 垂心 in *.
分离合取式.
assert (垂直于 H B C A H).
apply l8_14_2_1b_bis_交点是垂点;finish.
induction (两点重合的决定性 B H).
subst;auto.
assert (Perp A H B H)
 by (apply (垂线共线点也构成垂直2 A H B C H);finish).
assert (Par A H A C)
  by (apply l12_9 with B H;finish).
assert (Col H A C)
  by (perm_apply (par_id A C H)).
assert (H=C).
统计不重合点.
apply l6_21_两线交点的唯一性 with B C A C;finish.
subst.
auto.
Qed.

End Orthocenter.

Hint Resolve
     等价垂心ACB
     等价垂心BAC
     等价垂心BCA
     等价垂心CAB
     等价垂心CBA : Orthocenter.

Hint Resolve 垂心与三角形共面 : cop.