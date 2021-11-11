Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals_inter_dec.

Ltac assert_all := treat_equalities; assert_cols_perm; 统计不重合点; assert_congs_perm.

Section Triangle中点sTheorems.

Context `{TE:塔斯基公理系统_欧几里得几何}.
(*
Lemma col_permut132 : forall A B C, Col A B C -> Col A C B.
Proof. exact 等价共线ACB. Qed.

Lemma col_permut213 : forall A B C, Col A B C -> Col B A C.
Proof. exact 等价共线BAC. Qed.

Lemma 等价共线BCA : forall A B C, Col A B C -> Col B C A.
Proof. exact 等价共线BCA. Qed.

Lemma col_permut312 : forall A B C, Col A B C -> Col C A B.
Proof. exact 等价共线CAB. Qed.

Lemma col_permut321 : forall A B C, Col A B C -> Col C B A.
Proof. exact 等价共线CBA. Qed.

Lemma 共线的传递性2 : forall P Q A B,
  P <> Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof. exact 共线的传递性2. Qed.

Lemma 共线的传递性3 : forall P Q A B,
  P <> Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof. exact 共线的传递性3. Qed.
*)
Lemma 三角形中位线平行于第三边2 : forall A B C P Q,
 ~Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 严格平行 A B Q P.
Proof.
intros.
Name x the symmetric of P wrt Q.
assert_all.
assert (~ Col A P C) by (intro; apply H; ColR).
统计不重合点.
assert (严格平行四边形 A P C x) by (apply mid_plgs with Q;auto).
assert (Cong A x B P) by CongR.
assert (Par A x B P) by (assert_pars_perm; apply par_col2_par with P C; Col).
assert (HElim : 平行四边形 A x B P \/ 平行四边形 A x P B) by (apply par_cong_plg_2; assumption).

induction HElim.

 assert_paras_perm; assert_pars_perm.
 Name M the intersection of the diagonals (A B) and (x P) of the parallelogram H15.
 treat_equalities.
 search_contradiction.

apply par_strict_col2_par_strict with x P; Col.
统计不重合点; auto.
(*
apply ncol134_plg__pars1423; auto; intro; apply H; ColR.
*)
apply ncol123_plg__pars1423; auto; intro; apply H.
assert (P <> x) by (intro; treat_equalities; Col).
apply 等价共线BCA; apply 共线的传递性3 with P;
[| |apply 等价共线BCA]; Col.
apply 等价共线BCA; apply 共线的传递性2 with Q; Col.
apply 等价共线BCA; apply 共线的传递性2 with x; Col.
Qed.

Lemma 三角形中位线平行于第三边2且与其两半相等 : forall A B C P Q R,
 ~Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 严格平行 A B Q P  /\ Cong A R P Q /\ Cong B R P Q.
Proof.
intros.
Name x the symmetric of P wrt Q.
assert_all.
assert (~ Col A P C) by (intro; search_contradiction).
统计不重合点.
assert (严格平行四边形 A P C x) by (apply mid_plgs with Q;auto).
assert_all.
assert_pars_perm.
assert (Cong A x B P) by (apply 等长的传递性 with P C; Cong).
assert (Par A x B P) by (apply par_col2_par with P C; Col).
assert (HElim : 平行四边形 A x B P \/ 平行四边形 A x P B) by (apply par_cong_plg_2; assumption).

induction HElim.

 Name M the intersection of the diagonals (A B) and (x P) of the parallelogram H22.
 treat_equalities.
 search_contradiction.

assert_pars_perm.
assert (Par P Q A B) by (统计不重合点; apply par_col_par_2 with x; Col; Par).
split.

apply par_not_col_strict with x; Col; Par.
 intro.
 assert_cols_perm.
 apply H.
 ColR.
assert_congs_perm;split;CongR.
Qed.

Lemma 过三角形一边中点的一边平行线过第三边中点 : forall A B C P Q,
 ~ Col A B C ->
 中点 P B C ->
 Par A B Q P ->
 Col Q A C ->
 中点 Q A C.
Proof.
assert (H:=playfair_s_postulate_implies_midpoint_converse_postulate);
unfold midpoint_converse_postulate in H; intros; apply H with B P; Col.
unfold playfair_s_postulate.
apply parallel_uniqueness.
Qed.
(* 无用 *)
Lemma 三角形中位线平行于第三边2且与其一半相等1 : forall A B C P Q R,
 ~Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 严格平行 A B Q P  /\ Cong A R P Q.
Proof.
intros.
assert (严格平行 A B Q P /\ Cong A R P Q /\ Cong B R P Q)
  by (apply 三角形中位线平行于第三边2且与其两半相等 with C; assumption).
分离合取式.
split; assumption.
Qed.
(* 无用 *)
Lemma 三角形中位线平行于第三边2且与其一半相等2 : forall A B C P Q R,
 ~Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 严格平行 A B Q P  /\ Cong B R P Q.
Proof.
intros.
assert (严格平行 A B Q P /\ Cong A R P Q /\ Cong B R P Q)
  by (apply 三角形中位线平行于第三边2且与其两半相等 with C; assumption).
分离合取式.
split; assumption.
Qed.

Lemma 三角形中位线平行于第三边3 :
 forall A B C P Q,
 ~ Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 严格平行 A B Q P.
Proof.
apply 广义三角形中位线平行于第三边.
Qed.

Lemma 三角形中位线定理综合 : forall A B C P Q R,
 ~Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 严格平行 A B Q P /\ 严格平行 A C P R /\ 严格平行 B C Q R /\
 Cong A R P Q /\ Cong B R P Q /\ Cong A Q P R /\ Cong C Q P R /\ Cong B P Q R /\ Cong C P Q R.
Proof.
intros.
permutation_intro_in_hyps.
assert (严格平行 A B Q P /\ Cong A R P Q /\ Cong B R P Q)
  by (apply 三角形中位线平行于第三边2且与其两半相等 with C; assumption).
assert (严格平行 A C R P /\ Cong A Q P R /\ Cong C Q P R)
  by (apply 三角形中位线平行于第三边2且与其两半相等 with B; Col).
assert (严格平行 C B Q R /\ Cong C P R Q /\ Cong B P R Q)
  by (apply 三角形中位线平行于第三边2且与其两半相等 with A; Col).
分离合取式.

split; trivial.
split; Par.
split; Par.
repeat split; Cong.
Qed.

Lemma 退化三角形中位线平行于第三边且与其两半相等 : forall A B C P Q R,
 B <> A ->
 Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par A B Q P /\ Cong A R P Q /\ Cong B R P Q.
Proof.
intros.

elim (两点重合的决定性 A C); intro.

  assert_all.
  split; Cong.
  perm_apply col_par.

elim (两点重合的决定性 B C); intro.
  assert_all.
  split; Cong.
  perm_apply col_par.

elim (两点重合的决定性 A P); intro.
  assert_all.
  assert (Col A B Q) by ColR.
  split.
  perm_apply col_par.
  assert_congs_perm.
  split; Cong.

Name x the symmetric of P wrt Q.

elim (两点重合的决定性 P x); intro.
  treat_equalities; intuition.

assert_cols.
assert (平行四边形 A P C x) by (apply mid_plg_1 with Q;auto).
assert_all.
assert_pars_perm.
assert (Cong A x B P) by (apply 等长的传递性 with P C; Cong).
assert (Par A x B P) by (apply par_col2_par with P C; Col; Par).

assert (HElim : 平行四边形 A x B P \/ 平行四边形 A x P B) by (apply par_cong_plg_2; assumption).

induction HElim.

 Name M the intersection of the diagonals (A B) and (x P) of the parallelogram H11.
 treat_equalities.
 search_contradiction.

 assert_paras_perm.
 assert_pars_perm.
 assert (Par P Q A B) by (apply par_col_par_2 with x; Col; Par).
 assert_congs_perm.
 repeat split; Par; Cong.
Qed.

Lemma 退化三角形中位线平行于第三边2且与其一半相等1 : forall A B C P Q R,
 B <> A ->
 Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par A B Q P  /\ Cong A R P Q.
Proof.
intros.
assert (Par A B Q P /\ Cong A R P Q /\ Cong B R P Q)
  by (apply 退化三角形中位线平行于第三边且与其两半相等 with C; assumption).
分离合取式.
split; assumption.
Qed.

Lemma 退化三角形中位线平行于第三边2且与其一半相等2 : forall A B C P Q R,
 B <> A ->
 Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par A B Q P /\ Cong B R P Q.
Proof.
intros.
assert (Par A B Q P /\ Cong A R P Q /\ Cong B R P Q)
  by (apply 退化三角形中位线平行于第三边且与其两半相等 with C; assumption).
分离合取式.
split; assumption.
Qed.

Lemma 退化三角形中位线定理综合 : forall A B C P Q R,
 B <> A ->
 C <> A ->
 C <> B ->
 Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par A B Q P /\ Par A C P R /\ Par B C Q R /\
 Cong A R P Q /\ Cong B R P Q /\ Cong A Q P R /\ Cong C Q P R /\ Cong B P Q R /\ Cong C P Q R.
Proof.
intros.
permutation_intro_in_hyps.
assert (Par A B Q P /\ Cong A R P Q /\ Cong B R P Q) by (apply 退化三角形中位线平行于第三边且与其两半相等 with C; assumption).
assert (Par A C R P /\ Cong A Q P R /\ Cong C Q P R) by (apply 退化三角形中位线平行于第三边且与其两半相等 with B; Col).
assert (Par C B Q R /\ Cong C P R Q /\ Cong B P R Q) by (apply 退化三角形中位线平行于第三边且与其两半相等 with A; Col).
分离合取式.

repeat split; Cong; Par.

Qed.

Lemma 退化三角形中位线平行于第三边 : forall A B C P Q,
 B <> A ->
 Col A B C ->
 中点 P B C ->
 中点 Q A C ->
 Par A B Q P.
Proof.
intros.
elim (中点的存在性 A B); intro R; intro.
assert (HTMT := 退化三角形中位线平行于第三边且与其两半相等 A B C P Q R H H0 H1 H2 H3); 分离合取式.
assumption.
Qed.

Lemma 广义三角形中位线平行于第三边 : forall A B C P Q,
 A <> B ->
 中点 P B C ->
 中点 Q A C ->
 Par A B Q P.
Proof.
intros.

elim (共线的决定性 A B C); intro.
  apply 退化三角形中位线平行于第三边 with C; auto.

  apply par_strict_par; apply 三角形中位线平行于第三边2 with C; assumption.
Qed.

Lemma 广义三角形中位线定理综合 : forall A B C P Q R,
 B <> A ->
 C <> A ->
 C <> B ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par A B Q P /\ Par A C P R /\ Par B C Q R /\
 Cong A R P Q /\ Cong B R P Q /\ Cong A Q P R /\ Cong C Q P R /\ Cong B P Q R /\ Cong C P Q R.
Proof.
intros.

elim (共线的决定性 A B C); intro.
  apply 退化三角形中位线定理综合; assumption.

  assert (HTMT := 三角形中位线定理综合 A B C P Q R H5 H2 H3 H4); 分离合取式.
  repeat split; try apply par_strict_par; assumption.
Qed.


Lemma 广义三角形中位线平行于第三边且与其一半相等 : forall A B C P Q R,
 C <> B ->
 中点 P B C ->
 中点 Q A C ->
 中点 R A B ->
 Par B C Q R /\ Cong B P Q R .
Proof.
intros.
split.
perm_apply (广义三角形中位线平行于第三边 B C A Q R).
induction (共线的决定性 A B C).
 assert (Par C B Q R /\ Cong B P R Q).
  apply (退化三角形中位线平行于第三边2且与其一半相等2 C B A R Q P); 中点; Col.
  分离合取式.
  Cong.
 assert (HTMT := 三角形中位线定理综合 A B C P Q R H3 H0 H1 H2); 分离合取式.
 assumption.
Qed.

End Triangle中点sTheorems.