Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.
Require Export GeoCoq.Tarski_dev.Annexes.Tagged_predicates.

Ltac image_6 A B P' H P:=
 let T:= fresh in assert (T:= l10_6_existence A B P' H);
 ex_and T P.

Ltac image A B P P':=
 let T:= fresh in assert (T:= l10_2_existence A B P);
 ex_and T P'.

Ltac perp A B C X :=
 match goal with
   | H:(~Col A B C) |- _ =>
    let T:= fresh in assert (T:= l8_18_过一点垂线之垂点的存在性 A B C H);
    ex_and T X
 end.

Ltac parallel A B C D P :=
 match goal with
   | H:(A <> B) |- _ =>
    let T := fresh in assert(T:= parallel_existence A B P H);
    ex_and T C
 end.

Ltac par_strict :=
repeat
 match goal with
      | H: 严格平行 ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (严格平行 B A D C); assert (T := par_strict_comm A B C D H)  
      | H: 严格平行 ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (严格平行 C D A B); assert (T := par_strict_symmetry A B C D H)  
      | H: 严格平行 ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (严格平行 B A C D); assert (T := par_strict_left_comm A B C D H)   
      | H: 严格平行 ?A ?B ?C ?D |- _ =>
       let T := fresh in not_exist_hyp (严格平行 A B D C); assert (T := par_strict_right_comm A B C D H) 
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
   | H:(Par ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Par ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Per ?X1 ?X2 ?X2)     |- _ => clear H
   | H:(Per ?X1 ?X1 ?X2)     |- _ => clear H
   | H:(中点 ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac show_distinct2 := unfold not;intro;treat_equalities; try (solve [intuition]).

Ltac symmetric A B A' :=
 let T := fresh in assert(T:= 构造对称点 A B);
 ex_and T A'.

Tactic Notation "Name" ident(X) "the" "symmetric" "of" ident(A) "wrt" ident(C) :=
 symmetric A C X.

Ltac sfinish := 分离合取式; repeat match goal with
 | |- Bet ?A ?B ?C => Between; eBetween
 | |- Col ?A ?B ?C => ColR
 | |- ~ Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => intro;search_contradiction
 | |- Par ?A ?B ?C ?D => Par
 | |- 严格平行 ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- 垂直于 ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => CongR
 | |- 中点 ?A ?B ?C => 中点
 | |- ?A<>?B => assumption
 | |- ?A<>?B => apply 不重合的对称性;assumption
 | |- ?A<>?B => intro;treat_equalities; solve [search_contradiction]
 | |- ?G1 /\ ?G2 => split
 | |- _ => try assumption
end.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?B ?C ?D ?A |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?C ?D ?A ?B |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?D ?A ?B ?C |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?D ?C ?B ?A |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?C ?B ?A ?D |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?B ?A ?D ?C |- _ => clear H2
   | H:(平行四边形 ?A ?B ?C ?D), H2 : 平行四边形 ?A ?D ?C ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?A ?B ?D ?C |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?C ?D ?A ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?C ?D ?B ?A |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?D ?C ?B ?A |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?D ?C ?A ?B |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?B ?A ?C ?D |- _ => clear H2
   | H:(Par ?A ?B ?C ?D), H2 : Par ?B ?A ?D ?C |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?A ?B ?D ?C |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?C ?D ?A ?B |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?C ?D ?B ?A |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?D ?C ?B ?A |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?D ?C ?A ?B |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?B ?A ?C ?D |- _ => clear H2
   | H:(严格平行 ?A ?B ?C ?D), H2 : 严格平行 ?B ?A ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?D ?C |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?A ?B ?D ?C |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?C ?D ?A ?B |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?C ?D ?B ?A |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?D ?C ?B ?A |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?D ?C ?A ?B |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?B ?A ?C ?D |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?B ?A ?D ?C |- _ => clear H2
   | H:(Per ?A ?B ?C), H2 : Per ?C ?B ?A |- _ => clear H2
   | H:(中点 ?A ?B ?C), H2 : 中点 ?A ?C ?B |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?B ?A ?C) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?B ?C ?A) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?C ?B ?A) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?C ?A ?B) |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : (~Col ?A ?C ?B) |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
end.

Ltac clean := clean_trivial_hyps;clean_reap_hyps.

Ltac smart_subst X := subst X;clean.

Ltac treat_equalities_aux :=
  repeat
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst X2
end.

Ltac tag_hyps :=
  repeat
  match goal with
    | H : ?A <> ?B |- _ => apply Diff_Diff_tagged in H
    | H : Cong ?A ?B ?C ?D |- _ => apply Cong_Cong_tagged in H
    | H : Bet ?A ?B ?C |- _ => apply Bet_Bet_tagged in H
    | H : Col ?A ?B ?C |- _ => apply Col_Col_tagged in H
    | H : ~ Col ?A ?B ?C |- _ => apply NCol_NCol_tagged in H
    | H : 中点 ?A ?B ?C |- _ => apply Mid_Mid_tagged in H
    | H : Per ?A ?B ?C |- _ => apply Per_Per_tagged in H
    | H : 垂直于 ?X ?A ?B ?C ?D |- _ => apply Perp_in_Perp_in_tagged in H
    | H : Perp ?A ?B ?C ?D |- _ => apply Perp_Perp_tagged in H
    | H : 严格平行 ?A ?B ?C ?D |- _ => apply 严格平行_严格平行_tagged in H
    | H : Par ?A ?B ?C ?D |- _ => apply Par_Par_tagged in H
    | H : 平行四边形 ?A ?B ?C ?D |- _ => apply 平四_平四_tagged in H
  end.

Ltac permutation_intro_in_goal :=
 match goal with
 | |- Par ?A ?B ?C ?D => apply Par_cases
 | |- 严格平行 ?A ?B ?C ?D => apply 严格平行_cases
 | |- Perp ?A ?B ?C ?D => apply 垂直的各排列情况
 | |- 垂直于 ?X ?A ?B ?C ?D => apply 垂直于的各排列情况
 | |- Per ?A ?B ?C => apply 直角的各排列情况
 | |- 中点 ?A ?B ?C => apply 中点的各排列情况
 | |- ~ Col ?A ?B ?C => apply 共线否定的各排列情况
 | |- Col ?A ?B ?C => apply 共线的各排列情况
 | |- Bet ?A ?B ?C => apply 中间性的各排列情况
 | |- Cong ?A ?B ?C ?D => apply 等长的各排列情况
 | |- Out ?A ?B ?C => apply Out_cases
 | |- Le ?A ?B ?C ?D => apply 长度大于等于的各排列情况
 | |- Lt ?A ?B ?C ?D => apply 长度大于的各排列情况
 end.

Ltac perm_apply t :=
 permutation_intro_in_goal;
 try_or ltac:(apply t;solve [finish]).

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y H))

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);Side)

      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := 四点不共面则任三点不共线 A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:严格平行 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := par_strict_not_cols A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:严格平行四边形 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := plgs_not_col A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.

Ltac treat_equalities :=
treat_equalities_aux;
repeat
  match goal with
   | H : Cong ?X3 ?X3 ?X1 ?X2 |- _ =>
      apply 等长的对称性 in H; apply 等长的同一性 in H; smart_subst X2
   | H : Cong ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply 等长的同一性 in H;smart_subst X2
   | H : Bet ?X1 ?X2 ?X1 |- _ =>
      apply 中间性的同一律 in H;smart_subst X2
   | H : Le ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply AB小于等于CC推出A与B重合 in H;smart_subst X2
   | H : 中点 ?X ?Y ?Y |- _ => apply M是AA中点则M与A重合 in H; smart_subst Y
   | H : 中点 ?A ?B ?A |- _ => apply A是BA中点则A与B重合 in H; smart_subst A
   | H : 中点 ?A ?A ?B |- _ => apply A是AB中点则A与B重合 in H; smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in assert (T : A=B) by (apply (双中间性推出点重合 A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in assert (T : B=C) by (apply (双中间性推出点重合2 A B C); Between);
                       smart_subst B
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in assert (T : A=B) by (apply (双中间性推出点重合 A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in assert (T : B=C) by (apply (双中间性推出点重合2 A B C); Between);
                       smart_subst A
   | H : 中点 ?P ?A ?P1, H2 : 中点 ?P ?A ?P2 |- _ =>
     let T := fresh in assert (T := 中点组的唯一性1 A P P1 P2 H H2); smart_subst P1
   | H : 中点 ?A ?P ?X, H2 : 中点 ?A ?Q ?X |- _ =>
     let T := fresh in assert (T := 中点组的唯一性2 P Q A X H H2); smart_subst P
   | H : 中点 ?A ?P ?X, H2 : 中点 ?A ?X ?Q |- _ =>
     let T := fresh in assert (T := 中点组的唯一性3 P Q A X H H2); smart_subst P
   | H : 中点 ?A ?P ?P', H2 : 中点 ?B ?P ?P' |- _ =>
     let T := fresh in assert (T := 中点的唯一性1 P P' A B H H2); smart_subst A
   | H : 中点 ?A ?P ?P', H2 : 中点 ?B ?P' ?P |- _ =>
     let T := fresh in assert (T := 中点的唯一性2 P P' A B H H2); smart_subst A
end;
repeat
  match goal with
   | H:Par ?X1 ?X2 ?X1 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := par_id X1 X2 X3 H)
   | H:Par ?X1 ?X2 ?X3 ?X1 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_right_comm X1 X2 X3 X1 H))
   | H:Par ?X2 ?X1 ?X1 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_left_comm X2 X1 X1 X3 H))
   | H:Par ?X2 ?X1 ?X3 ?X1 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in
     assert (N := par_id X1 X2 X3 (par_comm X2 X1 X3 X1 H))
end.

Ltac CopR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
 let cop := constr:(共面) in
   treat_equalities; assert_cols; clean; assert_ncols; 推导四点共面; auto 2 with 共面的排列;
   solve[apply 共线三点和任一点共面; Col|apply 等价共面ABDC, 共线三点和任一点共面; Col
        |apply 等价共面ADBC, 共线三点和任一点共面; Col|apply 等价共面DABC, 共线三点和任一点共面; Col
        |copr_aux; Cop_refl tpoint col cop] || fail "Can not be deduced".

Section Quadrilateral_inter_dec_1.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma par_cong_mid_ts :
 forall A B A' B',
  严格平行 A B A' B' ->
  Cong A B A' B' ->
  TS A A' B B' ->
  exists M,  中点 M A A' /\ 中点 M B B'.
Proof.
intros.

assert(HH:= H1).
unfold TS in HH.
assert(~ Col B A A').
分离合取式; assumption.
分离合取式.
ex_and H5 M.
exists M.

assert(HH:= H).
unfold 严格平行 in HH.
分离合取式.

assert(HH:=(中点的存在性 A A')).
ex_and HH X.

prolong B X B'' B X.
assert(中点 X B B'').
unfold 中点.
split.
assumption.
Cong.

assert(严格平行 B A B'' A').
apply (midpoint_par_strict B A B'' A' X); auto.

assert(Col B'' B' A' /\ Col A' B' A').
apply(parallel_uniqueness B A B' A' B'' A' A').
apply par_comm.
unfold Par.
left.
assumption.
Col.
unfold Par.
left.
assumption.
Col.
分离合取式.

assert(Cong A B A' B'').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H9.
apply M是AB中点则M是BA中点.
assumption.
assert(Cong A' B' A' B'').
eapply 等长的传递性.
apply 等长的对称性.
apply H0.
assumption.

assert(B' = B'' \/ 中点 A' B' B'').
apply 共线点间距相同要么重合要么中点.
Col.
Cong.
induction H18.

subst B''.

assert(X = M).
apply (l6_21_两线交点的唯一性 A A' B B'); Col.

intro.
subst B'.
apply H8.
exists B.
split; Col.
subst X.
split; auto.

assert(TS A A' B B'').
unfold TS.
repeat split; auto.
intro.
apply H4.
apply 等价共线BCA.
apply (共线的传递性2 _ B'').
统计不重合点.
auto.
Col.
Col.
exists X.
split.
Col.
assumption.

assert(OS A A' B' B'').
eapply l9_8_1.
apply l9_2.
apply H1.
apply l9_2.
assumption.

assert(TS A A' B' B'').
unfold TS.
repeat split.
intro.
apply H4.
Col.
intro.
apply H4.

apply 等价共线BCA.
apply (共线的传递性2 _ B'').
统计不重合点.
auto.
Col.
Col.

exists A'.
split.
Col.
Between.
apply l9_9 in H21.
contradiction.
Qed.

Lemma par_cong_mid_os :
  forall A B A' B',
   严格平行 A B A' B' ->
   Cong A B A' B' ->
   OS A A' B B' ->
   exists M, 中点 M A B' /\ 中点 M B A'.
Proof.
intros.
assert(HH:= H).
unfold 严格平行 in HH.
分离合取式.

assert(HH:=(中点的存在性 A' B)).
ex_and HH X.
exists X.

prolong A X B'' A X.
assert(中点 X A B'').
unfold 中点.
split.
assumption.
Cong.

assert(~Col A B A').
intro.
apply H3.
exists A'.
split; Col.

assert(严格平行  A B B'' A').
apply (midpoint_par_strict A B  B'' A' X).
assumption.
assumption.
apply M是AB中点则M是BA中点.
assumption.

assert(Col B'' B' A' /\ Col A' B' A').
apply (parallel_uniqueness B A B' A' B'' A' A').

apply par_comm.
unfold Par.
left.
assumption.
Col.
apply par_left_comm.
unfold Par.
left.
assumption.
Col.
分离合取式.

assert(Cong A B  B'' A').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H7.
assumption.
assert(Cong A' B' A' B'').
eapply 等长的传递性.
apply 等长的对称性.
apply H0.
Cong.
assert(B' = B'' \/ 中点 A' B' B'').
apply 共线点间距相同要么重合要么中点.
Col.
Cong.

induction H14.
subst B''.
split.
assumption.
apply M是AB中点则M是BA中点.
assumption.

assert(OS A A' X B'').

eapply (out_one_side_1 _ _ _ _ A).

intro.
apply H8.
apply 等价共线BCA.
apply (共线的传递性2 _ X).
intro.
subst X.
apply A是AB中点则A与B重合 in H4.
subst A'.
apply H8.
Col.
Col.
Col.
Col.
统计不重合点.
repeat split; auto.

assert(TS A A' B' B'').
repeat split.
intro.
apply H3.
exists A.
split; Col.

unfold OS in H15.
ex_and H15 T.
unfold TS in H16.
分离合取式.
assumption.
exists A'.
split.
Col.
unfold 中点 in H14.
分离合取式.
assumption.

assert(TS A A' X B').
eapply l9_8_2.
apply l9_2.
apply H16.
apply one_side_symmetry.
assumption.

assert(OS A A' X B).

eapply (out_one_side_1).
intro.
apply H8.
apply 等价共线BCA.
eapply (共线的传递性2 _ X).
intro.
subst X.
apply A是AB中点则A与B重合 in H4.
subst A'.
apply H3.
exists B.
split; Col.
Col.
Col.
apply ABB型共线;Col.
统计不重合点.
repeat split; Between.

assert(OS A A' X B').
eapply one_side_transitivity.
apply H18.
assumption.
apply l9_9 in H17.
contradiction.
Qed.

Lemma par_strict_cong_mid :
 forall A B A' B',
  严格平行 A B A' B' ->
  Cong A B A' B' ->
  exists M,  中点 M A A' /\ 中点 M B B' \/
             中点 M A B' /\ 中点 M B A'.
Proof.
intros A B A' B' HParS HCong.
assert (HP:=parallel_uniqueness).
destruct (中点的存在性 A A') as [M1 HM1].
destruct (构造对称点 B M1) as [B'' HB''].
assert (HCol1 : Col B'' A' B').
  {
  assert (Col A' A' B' /\ Col B'' A' B'); [|分离合取式; Col].
  assert (HPar := par_strict_par A B A' B' HParS).
  apply HP with A B A'; Col.
  统计不重合点; apply l12_17 with M1; Col.
  }
assert (HCong1 : Cong A' B' A' B'')
  by (assert (H := l7_13_同中点组两侧等长 M1 A' B'' A B HM1 HB''); eCong).
destruct (中点的存在性 A B') as [M2 HM2].
destruct (构造对称点 B M2) as [A'' HA''].
assert (HCol2 : Col A'' A' B').
  {
  assert (Col B' A' B' /\ Col A'' A' B'); [|分离合取式; Col].
  assert (HPar := par_strict_par A B A' B' HParS).
  apply HP with A B B'; Col.
  统计不重合点; apply l12_17 with M2; Col.
  }
assert (HCong2 : Cong A' B' B' A'')
  by (assert (H := l7_13_同中点组两侧等长 M2 B' A'' A B HM2 HA''); eCong).
elim (共线点间距相同要么重合要么中点 A' B' B''); Col; intro HElim1; treat_equalities.

  {
  exists M1; left; Col.
  }


  {
  elim (共线点间距相同要么重合要么中点 B' A' A''); Cong; Col; intro HElim2; treat_equalities.

    {
    exists M2; right; Col.
    }

    {
    exfalso; destruct (outer_pasch B' A A' B'' M1) as [I [HAIB' HA''IM1]];
    unfold 中点 in*; 分离合取式; Between.
    assert (HM1I : M1 <> I).
      {
      intro; treat_equalities.
      assert_cols; show_distinct A M1; apply HParS; exists A; split; ColR.
      }
    assert (HB''M1 : B'' <> M1).
      {
      intro; treat_equalities; apply HParS; exists B; Col.
      }
    elim (l5_2 B'' M1 I B); Between; intro HBM1I.

      {
      show_distinct B' A''; [apply HParS; exists A; split; Col|].
      show_distinct A' B'; [apply HParS; exists A; split; Col|].
      assert (HFalse : TS A B' B A'').
        {
        split; [intro; apply HParS; exists B'; split; Col|].
        split; [assert_cols; intro; apply HParS; exists A; split; ColR|].
        exists M2; split; Col.
        }
      apply (l9_9 A B' B A''); trivial.
      exists A'; split.

        {
        show_distinct B' B''; [apply HParS; exists A; split; Col|].
        assert (~ Col B'' A B') by (intro; apply HParS; exists A; split; ColR).
        apply l9_2; apply l9_8_2 with B''.

          {
          destruct HFalse.
          repeat split; Col.
          exists I; split; [Col|eBetween].
          }

          {
          apply l9_19 with B'; Col.
          repeat split; Col.
          }
        }

        {
        split; [destruct HFalse as [_ []]; Col|].
        split; [intro; apply HParS; exists A; split; Col|].
        exists B'; split; Col; Between.
        }
      }

      {
      show_distinct A' B'; [apply HParS; exists A; split; Col|].
      show_distinct A' B''; [apply HParS; exists A; split; Col|].
      assert (HFalse : OS A A' B B').
        {
        exists B''; split.

          {
          split; [intro; apply HParS; exists A'; split; Col|].
          split; [intro; apply HParS; exists A; split; ColR|].
          exists M1; split; Col.
          }

          {
          apply invert_two_sides, bet__ts; auto.
          intro; apply HParS; exists A; split; Col.
          }
        }
      apply l9_9_bis in HFalse; apply HFalse; clear HFalse; apply l9_31.

        {
        apply l12_6, HParS.
        }

        {
        apply one_side_transitivity with B''.

          {
          apply l9_19 with B'; Col.
          split; [|intro; apply HParS; exists A; split; Col].
          repeat split; [intro; treat_equalities; apply HParS; exists A; split; Col..|Between].
          }

          {
          apply out_one_side_1 with I; Col; [intro; apply HParS; exists A; split; ColR|].
          split; [intro; treat_equalities; auto|].
          split; [intro; treat_equalities; apply HParS; exists B'; split; Col|].
          right; eBetween.
          }
        }
      }
    }
  }
Qed.

Lemma par_strict_cong_mid1 :
 forall A B A' B',
  严格平行 A B A' B' ->
  Cong A B A' B' ->
  (TS A A' B B'  /\ exists M,  中点 M A A' /\ 中点 M B B') \/ 
  (OS A A' B B' /\ exists M, 中点 M A B' /\ 中点 M B A').
Proof.
intros.
assert(HH:= H).
unfold 严格平行 in HH.
分离合取式.
destruct (cop__one_or_two_sides A A' B B').
Cop.
intro.
apply H2.
exists A'.
split; Col.
intro.
apply H2.
exists A.
split; Col.
left.
split.
assumption.
apply (par_cong_mid_ts A B A' B' H H0 H3).
right.
split.
assumption.
apply (par_cong_mid_os A B A' B' H H0 H3).
Qed.

Lemma par_cong_mid :
 forall A B A' B',
  Par A B A' B' ->
  Cong A B A' B' ->
  exists M,  中点 M A A' /\ 中点 M B B' \/
             中点 M A B' /\ 中点 M B A'.
Proof.
intros.
induction H.
apply par_strict_cong_mid; try assumption.
apply col_cong_mid.
unfold Par.
right.
assumption.
intro.
unfold 严格平行 in H1.
分离合取式.
apply H2.
exists A.
split; Col.
assumption.
Qed.

Lemma ts_cong_par_cong_par :
 forall A B A' B',
 TS A A' B B' ->
 Cong A B A' B' ->
 Par A B A' B' ->
 Cong A B' A' B /\ Par A B' A' B.
Proof.
intros A B A' B' HTS HCong HPar.
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in *; 分离合取式; Col).
destruct (par_cong_mid A B A' B') as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  assert(HAB' : A <> B') by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
  split; try apply l7_13_同中点组两侧等长 with M; try apply l12_17 with M; 中点.
  }

  {
  assert(HAA' : A <> A') by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
  assert (HFalse := HTS); apply l9_9 in HFalse; exfalso; apply HFalse; clear HFalse.
  unfold TS in HTS; 分离合取式; apply l12_6; apply par_not_col_strict with B; Col.
  assert (Par  A A' B' B); Par; apply l12_17 with M; 中点.
  }
Qed.

Lemma plgs_cong :
 forall A B C D,
 严格平行四边形 A B C D ->
 Cong A B C D /\ Cong A D B C.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]]; split; Col.
destruct (ts_cong_par_cong_par A B C D) as [HCong' HPar']; Cong.
Qed.

Lemma plg_cong :
 forall A B C D,
  平行四边形 A B C D ->
 Cong A B C D /\ Cong A D B C.
Proof.
intros.
induction H.
apply plgs_cong.
assumption.
apply plgf_cong.
assumption.
Qed.

Lemma rmb_cong :
 forall A B C D,
  菱形 A B C D ->
  Cong A B B C /\ Cong A B C D /\ Cong A B D A.
Proof.
intros.
unfold 菱形 in H.
分离合取式.
assert(HH:= plg_to_parallelogram A B C D H).
assert(HH1:= plg_cong A B C D HH).
分离合取式.
repeat split; trivial.
apply 等长的传递性 with B C; Cong.
Qed.

Lemma rmb_per:
 forall A B C D M,
  中点 M A C ->
  菱形 A B C D ->
  Per A M D.
Proof.
intros.
assert(HH:=H0).
unfold 菱形 in HH.
分离合取式.
assert(HH:=H1).
unfold 平四 in HH.
分离合取式.
ex_and H4 M'.
assert(M = M').
eapply 中点的唯一性1.
apply H.
assumption.
subst M'.
unfold Per.
exists B.
split.
apply M是AB中点则M是BA中点.
assumption.
apply rmb_cong in H0.
分离合取式.
Cong.
Qed.

Lemma per_rmb :
 forall A B C D M,
  平四 A B C D ->
  中点 M A C ->
  Per A M B ->
  菱形 A B C D.
Proof.
intros.
unfold Per in H1.
ex_and H1 D'.
assert(HH:=H).
unfold 平四 in HH.
分离合取式.
ex_and H4 M'.
assert(M = M').
eapply 中点的唯一性1.
apply H0.
apply H4.
subst M'.
assert(D = D').
eapply 中点组的唯一性1.
apply H5.
assumption.
subst D'.
unfold 菱形.
split.
assumption.
assert(Cong A D B C).
apply plg_to_parallelogram in H.
assert(HH:=plg_cong A B C D H).
分离合取式.
assumption.
eapply 等长的传递性.
apply H2.
assumption.
Qed.

Lemma perp_rmb :
 forall A B C D,
  平四 A B C D ->
  Perp A C B D ->
  菱形 A B C D.
Proof.
intros.
assert(HH:=中点的存在性 A C).
ex_and HH M.
apply (per_rmb A B C D M).
assumption.
assumption.
apply L形垂直于转直角.
unfold 平四 in H.
分离合取式.
ex_and H2 M'.
assert(M = M').
eapply 中点的唯一性1.
apply H1.
assumption.
subst M'.
assert(Perp A M B M).
eapply 垂线共线点也构成垂直1.
intro.
subst M.
apply A是AB中点则A与B重合 in H1.
subst C.
apply 垂直推出不重合1 in H0.
tauto.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
intro.
subst M.
apply A是AB中点则A与B重合 in H3.
subst D.
apply 垂直推出不重合2 in H0.
tauto.
apply 垂直的对称性.
apply H0.
unfold 中点 in H3.
分离合取式.
apply 中间性蕴含共线1 in H3.
Col.
unfold 中点 in H2.
分离合取式.
apply 中间性蕴含共线1 in H2.
Col.
apply 垂直的左交换性 in H4.
apply L形垂直转垂直于 in H4.
apply 垂直于的交换性.
assumption.
Qed.

Lemma plg_conga1 : forall A B C D, A <> B -> A <> C -> 平四 A B C D -> 等角 B A C D C A.
Proof.
intros.
apply 三角形全等推角等1; auto.
assert(HH := plg_to_parallelogram A B C D H1).
apply plg_cong in HH.
分离合取式.
repeat split; Cong.
Qed.

Lemma os_cong_par_cong_par :
 forall A B A' B',
  OS A A' B B' ->
  Cong A B A' B' ->
  Par A B A' B' ->
 Cong A A' B B' /\ Par A A' B B'.
Proof.
intros.

induction H1.

assert(A <> B /\ A <> A').
unfold OS in H.
ex_and H C.
unfold TS in H.
分离合取式.
split.
intro.
subst B.
apply H.
Col.
intro.
subst A'.
Col.
分离合取式.

assert(HH:= (par_strict_cong_mid1 A B A' B' H1 H0 )).
induction HH.
分离合取式.
apply l9_9 in H4.
contradiction.
分离合取式.
ex_and H5 M.
assert(HH:= mid_par_cong A B B' A' M H2 H3).
assert(Cong A B B' A' /\ Cong A A' B' B /\ Par A B B' A' /\ Par A A' B' B).
apply HH.
assumption.
assumption.
分离合取式.
split.
Cong.
Par.
分离合取式.
unfold OS in H.
ex_and H C.
unfold TS in H5.
分离合取式.
apply False_ind.
apply H5.
Col.
Qed.

Lemma plgs_permut :
 forall A B C D,
  严格平行四边形 A B C D ->
  严格平行四边形 B C D A.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]].
destruct (ts_cong_par_cong_par A B C D) as [HCong' HPar']; Col.
destruct (par_cong_mid A B C D) as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  assert (HAM : A <> M) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
  assert (HCM : C <> M) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
  assert (HBD : B <> D) by (intro; subst D; apply (not_two_sides_id B A C HTS)).
  destruct HTS as [HAC [HABC HTS]].
  repeat split; [intro; apply HABC; ColR..| |Par|Cong].
  exists M; split; [Col|Between].
  }

  {
  exfalso; apply (l9_9 A C B D HTS).
  unfold TS in HTS; 分离合取式.
  apply l12_6; apply par_not_col_strict with B; Col.
  apply par_right_comm; apply l12_17 with M; 中点.
  intro; subst; Col.
  }
Qed.

Lemma plg_permut :
 forall A B C D,
  平行四边形 A B C D ->
  平行四边形 B C D A.
Proof.
intros A B C D HPara.
elim HPara; clear HPara; intro HPara.

  {
  left; apply plgs_permut; Col.
  }

  {right; apply plgf_permut; Col.
  }
Qed.

Lemma plgs_mid :
 forall A B C D,
  严格平行四边形 A B C D ->
  exists M, 中点 M A C /\ 中点 M B D.
Proof.
intros A B C D HPara.
destruct HPara as [HTS [HCong HPar]].
destruct (par_cong_mid A B C D) as [M HM]; Col.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2]; try (exists M; Col).
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
assert(HAC : A <> C) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
assert (HFalse := HTS); apply l9_9 in HFalse; exfalso; apply HFalse; clear HFalse.
unfold TS in HTS; 分离合取式; apply l12_6; apply par_not_col_strict with B; Col.
assert (Par A C D B); Par; apply l12_17 with M; 中点.
Qed.

Lemma plg_mid :
 forall A B C D,
  平行四边形 A B C D ->
  exists M, 中点 M A C /\ 中点 M B D.
Proof.
intros A B C D HPara.
elim HPara; clear HPara; intro HPara.

  {
  apply plgs_mid; Col.
  }

  {
  apply plgf_mid; Col.
  }

Qed.

Lemma plg_mid_2 :
 forall A B C D I,
  平行四边形 A B C D ->
  中点 I A C ->
  中点 I B D.
Proof.
intros.
elim (plg_mid A B C D).
intros I' HI'.
分离合取式.
treat_equalities.
assumption.
assumption.
Qed.


Lemma plgs_not_comm :
  forall A B C D,
   严格平行四边形 A B C D ->
 ~ 严格平行四边形 A B D C /\ ~ 严格平行四边形 B A C D.
Proof.
intros.
unfold 严格平行四边形 in *.
split.
intro.
分离合取式.
assert(HH:=
ts_cong_par_cong_par A B C D H H4 H3).
分离合取式.

assert(严格平行 A D C B).
induction H6.
assumption.
分离合取式.

unfold 严格平行.
repeat split; Cop.
intro.
unfold TS in *.
分离合取式.
apply H.
Col.
apply l12_6 in H7.
apply l9_9 in H0.
apply one_side_symmetry in H7.
contradiction.

intro.
分离合取式.
assert(HH:=ts_cong_par_cong_par A B C D H H4 H3).
分离合取式.
apply par_symmetry in H6.

assert(严格平行 C B A D).
induction H6.
assumption.
分离合取式.
unfold 严格平行.
repeat split; Cop.
intro.
unfold TS in *.
分离合取式.
apply H13.
Col.
apply l12_6 in H7.
apply l9_9 in H0.
apply invert_one_side in H7.
contradiction.
Qed.

Lemma plg_not_comm :
 forall A B C D,
 A <> B ->
 平行四边形 A B C D ->
 ~ 平行四边形 A B D C /\ ~ 平行四边形 B A C D.
Proof.
intros.
unfold 平行四边形.
induction H0.
split.
intro.
induction H1.
apply plgs_not_comm in H0.
分离合取式.
contradiction.
unfold 严格平行四边形 in H0.
分离合取式.
unfold 退化平行四边形 in H1.
分离合取式.
apply par_symmetry in H2.
induction H2.
unfold 严格平行 in H2.
分离合取式.
apply H8.
exists D; Col.
分离合取式.
unfold TS in H0.
分离合取式.
apply H0.
Col.
intro.
assert(~ 严格平行四边形 A B D C /\ ~ 严格平行四边形 B A C D).
apply plgs_not_comm.
assumption.
分离合取式.
induction H1.
contradiction.
unfold 严格平行四边形 in H0.
unfold 退化平行四边形 in H1.
分离合取式.
unfold TS in H0.
分离合取式.
contradiction.
assert(~ 退化平行四边形 A B D C /\ ~ 退化平行四边形 B A C D).
apply plgf_not_comm.
assumption.
assumption.
分离合取式.
split.
intro.
induction H3.
unfold 严格平行四边形 in H3.
unfold 退化平行四边形 in H0.
分离合取式.
unfold TS in H3.
分离合取式.
apply H3.
Col.
apply plgf_not_comm in H0.
分离合取式.
contradiction.
assumption.
intro.
induction H3.
unfold 严格平行四边形 in H3.
unfold 退化平行四边形 in H0.
分离合取式.
unfold TS in H3.
分离合取式.
contradiction.
contradiction.
Qed.

Lemma parallelogram_to_plg : forall A B C D, 平行四边形 A B C D -> 平四 A B C D.
Proof.
intros A B C D HPara.
destruct (plg_mid A B C D) as [M HM]; Col.
split; try (exists M; Col).
elim HPara; clear HPara; intro HPara; try (apply plgs_diff in HPara; 分离合取式; Col);
unfold 退化平行四边形 in HPara; 分离合取式; Col.
Qed.

Lemma parallelogram_equiv_plg : forall A B C D, 平行四边形 A B C D <-> 平四 A B C D.
Proof.
intros.
split.
apply parallelogram_to_plg.
apply plg_to_parallelogram.
Qed.

Lemma plg_conga : forall A B C D, A <> B /\ A <> C /\ B <> C -> 平行四边形 A B C D -> 等角 A B C C D A /\ 等角 B C D D A B.
Proof.
intros.
assert(Cong A B C D /\ Cong A D B C).
apply plg_cong.
assumption.
分离合取式.
assert(HH:= plg_mid A B C D H0).
ex_and HH M.
split.
apply 三角形全等推角等1; auto.
repeat split; Cong.
apply 三角形全等推角等1; auto.
intro.
subst D.
apply H.
eapply 中点组的唯一性1;
apply M是AB中点则M是BA中点.
apply H5.
assumption.
repeat split; Cong.
Qed.

Lemma half_plgs :
 forall A B C D P Q M,
  严格平行四边形 A B C D ->
  中点 P A B ->
  中点 Q C D ->
  中点 M A C ->
  Par P Q A D /\ 中点 M P Q /\ Cong A D P Q.
Proof.
intros.
assert(HH:=H).
apply plgs_mid in HH.
ex_and HH M'.
assert(M=M').
eapply 中点的唯一性1.
apply H2.
assumption.
subst M'.
clear H3.

prolong P M Q' P M.
assert(中点 M P Q').
split.
assumption.
Cong.
assert(中点 Q' C D).
eapply 对称保持中点.
apply H2.
apply H6.
apply H4.
apply H0.
assert(Q=Q').
eapply 中点的唯一性1.
apply H1.
assumption.
subst Q'.
assert(HH:=H).
unfold 严格平行四边形 in HH.
分离合取式.

assert(Cong A P D Q).
eapply 两中点组全段等长则前半段等长.
apply H0.
apply M是AB中点则M是BA中点.
apply H1.
Cong.

assert(Par A P Q D).
eapply par_col_par_2.
intro.
subst P.
apply A是AB中点则A与B重合 in H0.
subst B.
apply par_neq1 in H9.
auto.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
apply 等价共线ACB.
apply H0.
apply par_symmetry.
apply par_left_comm.
eapply par_col_par_2.
intro.
subst Q.
apply 等长的同一性 in H11.
subst P.
apply A是AB中点则A与B重合 in H0.
subst B.
apply par_neq1 in H9.
auto.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
apply 等价共线CAB.
apply H1.
apply par_left_comm.
Par.


assert(Cong A D P Q /\ Par A D P Q).
apply(os_cong_par_cong_par A P D Q).

unfold TS in H8.
assert(~ Col B A C).
分离合取式.
assumption.
分离合取式.

assert(OS A D P B).
eapply out_one_side_1.
intro.
assert(Col P B D).
eapply (共线的传递性2 _ A).
intro.
subst P.
apply A是AB中点则A与B重合 in H0.
subst B.
apply 等长的对称性 in H10.
apply 等长的同一性 in H10.
subst D.
apply H14.
Col.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
Col.
Col.

assert(HH:=H).
apply plgs_permut in HH.
unfold 严格平行四边形 in HH.
分离合取式.
unfold TS in H18.
assert(~ Col C B D).
分离合取式.
assumption.
分离合取式.
apply H22.
apply 等价共线BCA.
eapply (共线的传递性2 _ P).
intro.
subst P.
apply H22.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
Col.
Col.
Col.
Col.
unfold 中点 in H0.
分离合取式.

repeat split.
intro.
subst P.
apply 等长的对称性 in H11.
apply 等长的同一性 in H11;

unfold TS in H8.
subst Q.
apply M是AB中点则M是BA中点 in H1.
apply A是AB中点则A与B重合 in H1.
subst D.
apply H14.
Col.
intro.
subst B.
apply 等长的对称性 in H10.
apply 等长的同一性 in H10;
unfold 严格平行 in H12.
subst D.
apply H13.
Col.
left.
assumption.

assert(OS A D Q C).
eapply out_one_side_1.
intro.
apply H14.
eapply (共线的传递性2 _ Q).
intro.
subst Q.
apply M是AB中点则M是BA中点 in H1.
apply A是AB中点则A与B重合 in H1.
subst D.
apply H14.
Col.
Col.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
Col.
apply ABB型共线;Col.

repeat split.
intro.
subst Q.
apply 等长的同一性 in H11.
subst P.
unfold OS in H16.
ex_and H16 K.
unfold TS in H11.
分离合取式.
apply H11.
Col.
intro.
subst D.
apply 等长的同一性 in H10.
subst B.
apply H14.
Col.

unfold 中点 in H1.
分离合取式.
left.
Between.

assert(OS A D B C).

apply ts_cong_par_cong_par in H9.
分离合取式.

induction H18.
apply l12_6.
unfold 严格平行 in *.
分离合取式.
split; Cop.
intro.
apply H19.
ex_and H20 X.
exists X.
split; Col.
分离合取式.
apply False_ind.
apply H13.
Col.
repeat split; auto.
Cong.
eapply one_side_transitivity.
apply H16.
eapply one_side_transitivity.
apply H18.
apply one_side_symmetry.
assumption.
assumption.
Par.
分离合取式.
apply par_symmetry in H14.
split; auto.
Qed.

Lemma plgs_two_sides :
 forall A B C D,
 严格平行四边形 A B C D ->
 TS A C B D /\ TS B D A C.
Proof.
intros.
assert(HH:= plgs_mid A B C D H).
ex_and HH M.
unfold 严格平行四边形 in H.
分离合取式.
split.
assumption.

unfold TS.
assert(~Col B A C).
unfold TS in H.
分离合取式.
Col.
assert(B <> D).
intro.
assert(HH:=one_side_reflexivity A C B H4).
apply l9_9 in H.
subst D.
contradiction.
unfold TS in H.
assert(~ Col B A C).
分离合取式.
assumption.
分离合取式.
repeat split.
intro.
assert(Col M A B).
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
ColR.

apply H4.
apply 等价共线CAB.
eapply (共线的传递性2 _ M).
intro.
subst M.
apply A是AB中点则A与B重合 in H0.
subst C.
Col.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1.
assumption.
Col.
intro.
assert(Col M B C).
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
ColR.
apply H6.
apply 等价共线BCA.
eapply (共线的传递性2 _ M).
intro.
subst M.
apply M是AB中点则M是BA中点 in H0.
apply A是AB中点则A与B重合 in H0.
subst C.
Col.
Col.
unfold 中点 in H0.
分离合取式.
apply 中间性蕴含共线1 in H0.
Col.
exists M.
unfold 中点 in *.
分离合取式.
apply 中间性蕴含共线1 in H1.
split; Col.
Qed.

Lemma plgs_par_strict :
 forall A B C D,
  严格平行四边形 A B C D ->
  严格平行 A B C D /\ 严格平行 A D B C.
Proof.
intros A B C D HPara.
destruct (plgs_mid A B C D) as [M [HMid1 HMid2]]; Col.
destruct HPara as [HTS [HCong HPar]].
assert(HAB : A <> B) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
assert(HAC : A <> D) by (intro; treat_equalities; unfold TS in HTS; 分离合取式; Col).
unfold TS in HTS; 分离合取式; split; try apply par_not_col_strict with C; Col.
assert (Par A D C B); Par; apply l12_17 with M; 中点.
Qed.

Lemma plgs_half_plgs_aux :
 forall A B C D P Q,
  严格平行四边形 A B C D ->
  中点 P A B ->
  中点 Q C D ->
  严格平行四边形 A P Q D.
Proof.
intros.
assert(HH:= H).
apply plgs_mid in HH.
ex_and HH M.
assert(HH:=half_plgs A B C D P Q M H H0 H1 H2).
分离合取式.

assert(HH:=H).
apply plgs_par_strict in HH.
分离合取式.

assert(HH:=par_cong_mid P Q A D H4 (等长的对称性 A D P Q H6)).
ex_and HH N.
induction H9.
分离合取式.
apply False_ind.
unfold 严格平行 in H7.
分离合取式.
apply H11.
exists N.
统计不重合点; split; ColR.

分离合取式.

assert(A <> P).
intro.
subst P.
apply A是AB中点则A与B重合 in H0.
subst B.
apply par_strict_distinct in H7.
分离合取式.
auto.

assert(D <> Q).
intro.
subst Q.
apply M是AB中点则M是BA中点 in H1.
apply A是AB中点则A与B重合 in H1.
subst D.
apply par_strict_distinct in H7.
分离合取式.
auto.

eapply mid_plgs.
intro.
unfold 严格平行 in H7.
分离合取式.
apply H14.
exists Q.
split.
ColR.
Col.
apply M是AB中点则M是BA中点.
apply H10.
assumption.
Qed.

Lemma plgs_comm2 :
 forall A B C D,
  严格平行四边形 A B C D ->
  严格平行四边形 B A D C.
Proof.
intros.
assert(HH:= H).
apply plgs_two_sides in HH.
分离合取式.
unfold 严格平行四边形 in *.
split.
assumption.
分离合取式.
split.
apply par_comm.
assumption.
Cong.
Qed.

Lemma plgf_comm2 :
 forall A B C D,
  退化平行四边形 A B C D ->
  退化平行四边形 B A D C.
Proof.
intros.
unfold 退化平行四边形 in *.
分离合取式.
repeat split; Col.
Cong.
Cong.
induction H3.
right; assumption.
left; assumption.
Qed.

Lemma plg_comm2 :
 forall A B C D,
  平行四边形 A B C D ->
  平行四边形 B A D C.
Proof.
intros.
induction H.
left.
apply plgs_comm2.
assumption.
right.
apply plgf_comm2.
assumption.
Qed.

Lemma par_preserves_conga_os :
 forall A B C D P , Par A B C D -> Bet A D P -> D <> P -> OS A D B C -> 等角 B A P C D P.
Proof.
intros.
assert(HH:= H2).
unfold OS in HH.
ex_and HH T.
unfold TS in *.
分离合取式.

prolong C D C' C D.

assert(C' <> D).
intro.
subst C'.
apply 等长的对称性 in H10.
apply 等长的同一性 in H10.
subst D.
apply H4.
Col.

assert(等角 B A D C' D A).
eapply l12_21_a.
apply (l9_8_2 _ _ C).
unfold TS.
repeat split; auto.
intro.
apply H4.
apply 中间性蕴含共线1 in H9.
ColR.

exists D.
split.
Col.
assumption.
apply one_side_symmetry.
assumption.

apply par_symmetry.
eapply (par_col_par_2 _ C).
auto.

apply 中间性蕴含共线1 in H9.
Col.
apply par_symmetry.
Par.

assert(A <> B).
intro.
subst B.
apply H3.
Col.

assert(等角 B A D B A P).
assert(A <> D).
intro.
subst D.
Col.
apply out2__conga.
apply out_trivial.
auto.
repeat split; auto.
intro.
subst P.
apply 中间性的同一律 in H0.
contradiction.
apply 等角的右交换性.

assert(等角 C D P C' D A).
eapply l11_14; auto.
intro.
subst D.
apply H4.
Col.
Between.
intro.
subst D.
Col.
eapply 角等的传递性.
apply 等角的对称性.
apply H14.
eapply 角等的传递性.
apply H12.
apply 等角的对称性.
apply 等角的左交换性.
assumption.
Qed.

Lemma cong3_par2_par :
 forall A B C A' B' C', A <> C -> 三角形全等 B A C B' A' C' -> Par B A B' A' -> Par B C B' C' ->
 Par A C A' C' \/ ~ 严格平行 B B' A A' \/ ~严格平行 B B' C C'.
Proof.
intros.

assert(HH0:=par_distinct B A B' A' H1).
assert(HH1:=par_distinct B C B' C' H2).
分离合取式.

assert(HH:=中点的存在性 B B').
ex_and HH M.

prolong A M A'' A M.
prolong C M C'' C M.

assert(中点 M A A'').
split; Cong.
assert(中点 M C C'').
split; Cong.

assert(Par B A B' A'').
apply (l12_17 _ _ _ _ M); assumption.

assert(Par B C B' C'').
apply (l12_17 _ _ _ _ M); assumption.

assert(Par  A C A'' C'').
apply (l12_17 _ _ _ _ M);assumption.

assert(Par B' A' B' A'').
eapply par_trans.
apply par_symmetry.
apply H1.
assumption.

assert(Par B' C' B' C'').
eapply par_trans.
apply par_symmetry.
apply H2.
assumption.


assert(Col B' A' A'').
unfold Par in H17.
induction H17.
apply False_ind.
apply H17.
exists B'.
split; Col.
分离合取式.
Col.

assert(Col B' C' C'').
unfold Par in H18.
induction H18.
apply False_ind.
apply H18.
exists B'.
split; Col.
分离合取式.
Col.

assert(Cong B A B' A'').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H7.
apply M是AB中点则M是BA中点.
assumption.

assert(Cong B C B' C'').
eapply l7_13_同中点组两侧等长.
apply M是AB中点则M是BA中点.
apply H7.
apply M是AB中点则M是BA中点.
assumption.

unfold 三角形全等 in H0.
分离合取式.

assert(A' = A'' \/ 中点 B' A' A'').
eapply 共线点间距相同要么重合要么中点.
Col.
apply 等长的传递性 with B A; Cong.

assert(C' = C'' \/ 中点 B' C' C'').
eapply 共线点间距相同要么重合要么中点.
Col.
apply 等长的传递性 with B C; Cong.

induction H25.

induction H26.
subst A''.
subst C''.
left.
assumption.

right; left.
intro.
apply H27.
exists M.
unfold 中点 in *.
分离合取式.
split.
apply 中间性蕴含共线1 in H7.
Col.
subst.
apply 中间性蕴含共线1 in H8.
Col.

induction H26.

subst C''.
clean_duplicated_hyps.
clean_trivial_hyps.

right; right.
intro.
apply H15.
exists M.
split.
unfold 中点 in H7.
分离合取式.
apply 中间性蕴含共线1 in  H7.
Col.
unfold 中点 in H13.
分离合取式.
apply 中间性蕴含共线1 in  H13.
Col.

assert(Par A' C' A'' C'').

apply(l12_17 A' C' A'' C'' B').

intro.
subst C'.
assert(A'' = C'').
eapply 中点组的唯一性2.
apply M是AB中点则M是BA中点.
apply H25.
apply M是AB中点则M是BA中点.
assumption.
subst C''.
apply H.
eapply 中点组的唯一性2.
apply H12.
assumption.
apply H25.
apply H26.
left.
eapply par_trans.
apply H16.
Par.
Qed.



Lemma square_perp_rectangle : forall A B C D,
 长方形 A B C D ->
 Perp A C B D ->
 正方形 A B C D.
Proof.
intros.
assert (菱形 A B C D).
apply perp_rmb.
apply H. assumption.
apply 菱形_长方形_正方形;auto.
Qed.

Lemma plgs_half_plgs :
 forall A B C D P Q,
  严格平行四边形 A B C D ->
  中点 P A B -> 中点 Q C D ->
  严格平行四边形 A P Q D /\ 严格平行四边形 B P Q C.
Proof.
intros.
split.
eapply plgs_half_plgs_aux.
apply H.
assumption.
assumption.
apply plgs_comm2 in H.
eapply plgs_half_plgs_aux.
apply H.
中点.
中点.
Qed.

Lemma parallel_2_plg :
  forall A B C D,
  ~ Col A B C ->
  Par A B C D ->
  Par A D B C ->
  严格平行四边形 A B C D.
Proof.
intros.
assert (Cong A B C D /\ Cong B C D A /\
        TS B D A C /\ TS A C B D)
  by (apply l12_19;Par).
unfold 严格平行四边形; intuition.
Qed.

Lemma par_2_plg :
  forall A B C D,
  ~ Col A B C ->
  Par A B C D ->
  Par A D B C ->
  平行四边形 A B C D.
Proof.
intros.
assert (H2 := parallel_2_plg A B C D H H0 H1).
apply 严格平行四边形_平行四边形; assumption.
Qed.

Lemma plg_cong_1 : forall A B C D, 平行四边形 A B C D -> Cong A B C D.
Proof.
intros.
apply plg_cong in H.
分离合取式.
assumption.
Qed.

Lemma plg_cong_2 : forall A B C D, 平行四边形 A B C D -> Cong A D B C.
Proof.
intros.
apply plg_cong in H.
分离合取式.
assumption.
Qed.

Lemma plgs_cong_1 : forall A B C D, 严格平行四边形 A B C D -> Cong A B C D.
Proof.
intros.
apply plgs_cong in H.
分离合取式.
assumption.
Qed.

Lemma plgs_cong_2 : forall A B C D, 严格平行四边形 A B C D -> Cong A D B C.
Proof.
intros.
apply plgs_cong in H.
分离合取式.
assumption.
Qed.

Lemma 平四_perm :
  forall A B C D,
  平行四边形 A B C D ->
  平行四边形 A B C D /\ 平行四边形 B C D A /\ 平行四边形 C D A B /\平行四边形 D A B C /\ 
  平行四边形 A D C B /\ 平行四边形 D C B A /\ 平行四边形 C B A D /\ 平行四边形 B A D C.
Proof.
intros.
split; try assumption.
split; try (apply plg_permut; assumption).
split; try (do 2 apply plg_permut; assumption).
split; try (do 3 apply plg_permut; assumption).
split; try (apply plg_comm2; do 3 apply plg_permut; assumption).
split; try (apply plg_comm2; do 2 apply plg_permut; assumption).
split; try (apply plg_comm2; apply plg_permut; assumption).
apply plg_comm2; assumption.
Qed.

Lemma plg_not_comm_1 :
  forall A B C D : Tpoint,
  A <> B ->
  平行四边形 A B C D -> ~ 平行四边形 A B D C.
Proof.
intros.
assert (HNC := plg_not_comm A B C D H H0); 分离合取式; assumption.
Qed.

Lemma plg_not_comm_2 :
  forall A B C D : Tpoint,
  A <> B ->
  平行四边形 A B C D -> ~ 平行四边形 B A C D.
Proof.
intros.
assert (HNC := plg_not_comm A B C D H H0); 分离合取式; assumption.
Qed.

End Quadrilateral_inter_dec_1.

Ltac permutation_intro_in_hyps_aux :=
 repeat
 match goal with
 | H : 平四_tagged ?A ?B ?C ?D |- _ => apply 平四_tagged_平四 in H; apply 平四_perm in H; 分离合取式
 | H : Par_tagged ?A ?B ?C ?D |- _ => apply Par_tagged_Par in H; apply Par_perm in H; 分离合取式
 | H : 严格平行_tagged ?A ?B ?C ?D |- _ => apply 严格平行_tagged_严格平行 in H; apply 严格平行_perm in H; 分离合取式
 | H : Perp_tagged ?A ?B ?C ?D |- _ => apply Perp_tagged_Perp in H; apply 垂直的等价排列 in H; 分离合取式
 | H : Perp_in_tagged ?X ?A ?B ?C ?D |- _ => apply Perp_in_tagged_Perp_in in H; apply 垂直于的等价排列 in H; 分离合取式
 | H : Per_tagged ?A ?B ?C |- _ => apply Per_tagged_Per in H; apply 直角的等价排列 in H; 分离合取式
 | H : Mid_tagged ?A ?B ?C |- _ => apply Mid_tagged_Mid in H; apply 中点的等价排列 in H; 分离合取式
 | H : NCol_tagged ?A ?B ?C |- _ => apply NCol_tagged_NCol in H; apply 共线否定的等价排列 in H; 分离合取式
 | H : Col_tagged ?A ?B ?C |- _ => apply Col_tagged_Col in H; apply 共线的等价排列 in H; 分离合取式
 | H : Bet_tagged ?A ?B ?C |- _ => apply Bet_tagged_Bet in H; apply 中间性的等价排列 in H; 分离合取式
 | H : Cong_tagged ?A ?B ?C ?D |- _ => apply Cong_tagged_Cong in H; apply 等长的等价排列 in H; 分离合取式
 | H : Diff_tagged ?A ?B |- _ => apply Diff_tagged_Diff in H; apply Diff_perm in H; 分离合取式
 end.

Ltac permutation_intro_in_hyps := clean_reap_hyps; clean_trivial_hyps; tag_hyps; permutation_intro_in_hyps_aux.

Ltac exist_hyp_perm_col4 A B C D := first [exist_hyp_perm_col A B C|exist_hyp_perm_col A B D
                                      |exist_hyp_perm_col A C D|exist_hyp_perm_col B C D].

Ltac not_exist_hyp_perm_col4 A B C D := first [not_exist_hyp_perm_col A B C|not_exist_hyp_perm_col A B D
                                           |not_exist_hyp_perm_col A C D|not_exist_hyp_perm_col B C D].

Ltac assert_cols_aux :=
repeat
 match goal with
      | H:Par ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_col4 X1 X2 X3 X4;exist_hyp_perm_col4 X1 X2 X3 X4;
     assert (Col X1 X2 X3 /\ Col X1 X2 X4 /\ Col X1 X3 X4 /\ Col X2 X3 X4)
     by (solve [apply col2_par__col4 with X1; Col|apply col2_par__col4 with X2; Col|
                apply col2_par__col4 with X1; Col|apply col2_par__col4 with X1; Col]); 分离合取式
 end.

Ltac assert_cols_perm := assert_cols; assert_cols_aux; clean_reap_hyps.

Ltac not_exist_hyp_perm_cong A B C D := not_exist_hyp (Cong A B C D); not_exist_hyp (Cong A B D C);
                                        not_exist_hyp (Cong B A C D); not_exist_hyp (Cong B A D C);
                                        not_exist_hyp (Cong C D A B); not_exist_hyp (Cong C D B A);
                                        not_exist_hyp (Cong D C A B); not_exist_hyp (Cong D C B A).

Ltac assert_congs_1 :=
repeat
 match goal with
      | H:中点 ?X1 ?X2 ?X3 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X1 X3;
      assert (h := 中点蕴含等长 X2 X1 X3 H)

      | H:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X3 X4;
      assert (h := plg_cong_1 X1 X2 X3 X4 H)

      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X2 X3 X4;
      assert (h := plgs_cong_1 X1 X2 X3 X4 H)

      | H:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X4 X2 X3;
      assert (h := plg_cong_2 X1 X2 X3 X4 H)

      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_cong X1 X4 X2 X3;
      assert (h := plgs_cong_2 X1 X2 X3 X4 H)
  end.

Ltac assert_congs_2 :=
repeat
 match goal with
      | H1:中点 ?M1 ?A1 ?B1, H2:中点 ?M2 ?A2 ?B2, H3:Cong ?A1 ?B1 ?A2 ?B2 |- _ =>
      first [ not_exist_hyp_perm_cong A1 M1 A2 M2 | not_exist_hyp_perm_cong B1 M1 B2 M2 ];
      let h1 := fresh in assert (h1 := 两中点组全段等长则前半段等长 A1 M1 B1 A2 M2 B2 H1 H2 H3);
      let h2 := fresh in assert (h2 := 两中点组全段等长则后半段等长 A1 M1 B1 A2 M2 B2 H1 H2 H3)
  end.

Ltac assert_congs_perm := assert_congs_1; permutation_intro_in_hyps; assert_congs_2; clean_reap_hyps.

Ltac not_exist_hyp_perm_para A B C D := not_exist_hyp (平行四边形 A B C D); not_exist_hyp (平行四边形 B C D A);
                                        not_exist_hyp (平行四边形 C D A B); not_exist_hyp (平行四边形 D A B C);
                                        not_exist_hyp (平行四边形 A D C B); not_exist_hyp (平行四边形 D C B A);
                                        not_exist_hyp (平行四边形 C B A D); not_exist_hyp (平行四边形 B A D C).

Ltac not_exist_hyp_perm_para_s A B C D := not_exist_hyp (严格平行四边形 A B C D);
                                          not_exist_hyp (严格平行四边形 B C D A);
                                          not_exist_hyp (严格平行四边形 C D A B);
                                          not_exist_hyp (严格平行四边形 D A B C);
                                          not_exist_hyp (严格平行四边形 A D C B);
                                          not_exist_hyp (严格平行四边形 D C B A);
                                          not_exist_hyp (严格平行四边形 C B A D);
                                          not_exist_hyp (严格平行四边形 B A D C).

Ltac assert_paras_aux :=
repeat
 match goal with
      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para X1 X2 X3 X4;
      assert (h := 严格平行四边形_平行四边形 X1 X2 X3 X4 H)

      | H:平四 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para X1 X2 X3 X4;
      assert (h := plg_to_parallelogram X1 X2 X3 X4 H)

      | H:(~ Col ?X1 ?X2 ?X3), H2:Par ?X1 ?X2 ?X3 ?X4, H3:Par ?X1 ?X4 ?X2 ?X3 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_para_s X1 X2 X3 X4;
      assert (h := parallel_2_plg X1 X2 X3 X4 H H2 H3)
  end.

Ltac assert_paras_perm := permutation_intro_in_hyps; assert_paras_aux; clean_reap_hyps.

Ltac not_exist_hyp_perm_npara A B C D := not_exist_hyp (~平行四边形 A B C D); not_exist_hyp (~平行四边形 B C D A);
                                         not_exist_hyp (~平行四边形 C D A B); not_exist_hyp (~平行四边形 D A B C);
                                         not_exist_hyp (~平行四边形 A D C B); not_exist_hyp (~平行四边形 D C B A);
                                         not_exist_hyp (~平行四边形 C B A D); not_exist_hyp (~平行四边形 B A D C).

Ltac assert_nparas :=
 repeat
 match goal with
      | H:(?X1<>?X2), H2:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      first [ not_exist_hyp_perm_npara X1 X2 X4 X3 | not_exist_hyp_perm_npara X2 X1 X3 X4 ];
      let h1 := fresh in assert (h1 := plg_not_comm_1 X1 X2 X3 X4 H H2);
      let h2 := fresh in assert (h := plg_not_comm_2 X1 X2 X3 X4 H H2)
  end.

Ltac assert_nparas_perm := permutation_intro_in_hyps; assert_nparas; clean_reap_hyps.

Ltac diag_plg_intersection M A B C D H :=
 let T := fresh in assert(T:= plg_mid A B C D H);
 ex_and T M.

Tactic Notation "Name" ident(M) "the" "intersection" "of" "the" "diagonals" "(" ident(A) ident(C) ")" "and" "(" ident(B) ident(D) ")" "of" "the" "parallelogram" ident(H) :=
 diag_plg_intersection M A B C D H.

Ltac 统计不重合点 :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := 不共线则不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps 

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := 非中间性则任两点不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_AB不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BA不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BC不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_CB不等推AC不等 A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D (不重合的对称性 B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于推出不重合 A B C D H);clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B (不重合的对称性 B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B (不重合的对称性 A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B (不重合的对称性 B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H (不重合的对称性 B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H (不重合的对称性 C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直推出不重合 A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:垂直于 ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直于推出不重合 X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 角等推AB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= 角等推CB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= 角等推DE不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= 角等推FE不重合 A B C A' B' C' H);clean_reap_hyps

      | H:(在角内 ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := 在角内推出点不重合 A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于等于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于等于推出点不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于推不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为锐角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为锐角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为钝角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为钝角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:互为补角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(垂直平面于 ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:Inter ?A ?B ?C ?D ?X |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= inter_distincts A B C D X H);decompose [and] T;clear T;clean_reap_hyps

      | H:严格平行 ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp6 A B A C A D B C B D C D);
       assert (T:= par_strict_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= par_distincts A B C D H);decompose [and] T;clear T;clean_reap_hyps
      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直推出不重合 A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:垂直于 ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直于推出不重合 X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:和角 ?A ?B ?C ?D ?E ?F ?G ?I ?J |- _ =>
      let h := fresh in
      not_exist_hyp6 A B B C D E E F G I I J;
      assert (h := 和角推出不重合 A B C D E F G I J H);decompose [and] h;clear h;clean_reap_hyps

      | H:三角形内角和 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp5 A B B C A C D E E F;
      assert (h := 三角形内角和推出不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:和角不大于平角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 和角不大于平角推出不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:严格平行四边形 ?A ?B ?C ?D |- _ =>
      let T := fresh in
      not_exist_hyp6 A B B C C D D A A C B D;
       assert (T:= plgs_diff A B C D H);decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; 统计不重合点; Col_refl tpoint col.

Ltac CongR :=
 let tpoint := constr:(Tpoint) in
 let cong := constr:(Cong) in
   treat_equalities; assert_congs_1; Cong; Cong_refl tpoint cong.

Ltac show_distinct X Y := assert (X<>Y);[intro;treat_equalities|idtac].

Ltac show_distinct'' X Y :=
 assert (X<>Y);
 [intro;treat_equalities; solve [finish]|idtac].

Ltac assert_all_diffs_by_contradiction :=
统计不重合点;repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;show_distinct'' A B
end.

Hint Resolve parallelogram_strict_not_col
             parallelogram_strict_not_col_2
             parallelogram_strict_not_col_3
             parallelogram_strict_not_col_4 : col.

Hint Resolve plg_cong_1 plg_cong_2 plgs_cong_1 plgs_cong_2 : cong.

Section Quadrilateral_inter_dec_2.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma parallelogram_strict_midpoint : forall A B C D I,
  严格平行四边形 A B C D ->
  Col I A C ->
  Col I B D ->
  中点 I A C /\ 中点 I B D.
Proof.
intros.
assert (T:=严格平行四边形_平行四边形 A B C D H).
assert (HpF := plg_mid A B C D T).
elim HpF; intros I' HI;分离合取式;clear HpF.
assert (H01 : Col A C I).
 Col.
assert (H02 : Col D B I).
 Col.
assert (H03 : ~Col A D C).
 apply parallelogram_strict_not_col_3 in H.
 Col.
unfold 严格平行四边形 in H.
decompose [and] H.
(* trouver unicité intersection *)
assert (H8 := two_sides_not_col A C B D H4).
assert (MDB:D<>B).
 assert (Col A I' C).
  assert (H9 := midpoint_bet A I' C H2).
  assert (H10 := 中间性蕴含共线1 A I' C H9).
  assumption.
 assert (H11 : ~ Col A C D).
  Col.
 assert (H12 := M是AB中点则M是BA中点 I' B D H3).
 assert (H13 : Col A C I').
  Col.
 apply (midpoint_distinct A C I' D B H11 H13 H12).
assert (H11 : Col D B I').
 assert (H14 := midpoint_bet B I' D H3).
 assert (H15 := 中间性蕴含共线1 B I' D H14).
 Col.
assert (H12 : Col A C I').
 assert (H14 := midpoint_bet A I' C H2).
 assert (H15 := 中间性蕴含共线1 A I' C H14).
 Col.
apply 共线否定排列ACB in H03.
assert (H13 := l6_21_两线交点的唯一性 A C D B I I' H03 MDB H01 H12 H02 H11).
split.
 rewrite H13;assumption.
 subst;assumption.
Qed.

Lemma rmb_perp :
 forall A B C D,
  A <> C -> B <> D ->
  菱形 A B C D ->
  Perp A C B D.
Proof.
intros.
assert(HH:= H1).
unfold 菱形 in HH.
分离合取式.
apply plg_to_parallelogram in H2.
apply plg_mid in H2.
ex_and H2 M.
assert(HH:= H1).
eapply (rmb_per _ _ _ _ M) in HH.
apply 直角转L形垂直于 in HH.

apply 垂直于转T形垂直 in HH.
induction HH.
apply 垂直推出不重合1 in H5.
tauto.
unfold 中点 in *.
分离合取式.
eapply 垂线共线点也构成垂直1.
assumption.
apply 垂直的对称性.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply 垂直的左交换性.
apply 垂直的对称性.
apply H5.
apply 中间性蕴含共线1 in H4.
Col.
apply 中间性蕴含共线1 in H2.
Col.
intro.
subst M.
apply A是AB中点则A与B重合 in H2.
contradiction.
intro.
subst M.
apply M是AB中点则M是BA中点 in H4.
apply A是AB中点则A与B重合 in H4.
subst D.
tauto.
assumption.
Qed.

Lemma rect_permut : forall A B C D, 长方形 A B C D -> 长方形 B C D A.
Proof.
intros.
unfold 长方形 in *.
分离合取式.
split.
apply plg_to_parallelogram in H.
apply plg_permut in H.
apply parallelogram_to_plg in H.
assumption.
Cong.
Qed.

Lemma rect_comm2 : forall A B C D, 长方形 A B C D -> 长方形 B A D C.
Proof.
intros.
unfold 长方形 in *.
分离合取式.
apply plg_to_parallelogram in H.

apply plg_comm2 in H.
split.
apply parallelogram_to_plg.
assumption.
Cong.
Qed.

Lemma rect_per1 : forall A B C D, 长方形 A B C D -> Per B A D.
Proof.
intros.
unfold 长方形 in H.
分离合取式.

assert(HH:= 中点的存在性 A B).
ex_and HH P.
assert(HH:= 中点的存在性 C D).
ex_and HH Q.
assert(HH:=H).
unfold 平四 in HH.
分离合取式.
ex_and H4 M.
apply plg_to_parallelogram in H.
induction H.

assert(HH:=half_plgs A B C D P Q M H H1 H2 H4).
分离合取式.
assert(Per A P Q).
eapply (直角边共线点也构成直角2 _  _ M).
intro.
subst M.
apply A是AB中点则A与B重合 in H7.
subst Q.
apply 等长的同一性 in H8.
subst D.
assert(B = C).
eapply 中点组的唯一性1.
apply M是AB中点则M是BA中点.
apply H5.
中点.
subst C.
unfold 严格平行四边形 in H.
分离合取式.
unfold TS in H.
分离合取式.
apply H9.
Col.
apply 直角的对称性.
unfold Per.
exists B.
split.
assumption.
eapply (两中点组全段等长则前半段等长 _ M _ _ M) in H0.
Cong.
assumption.
assumption.
unfold 中点 in H7.
分离合取式.
apply 中间性蕴含共线1.
assumption.

assert(A <> B).
intro.
subst B.
apply M是AA中点则M与A重合 in H1.
subst P.
unfold 严格平行四边形 in H.
分离合取式.
unfold TS in H.
分离合取式.
apply H.
Col.

assert(A <> P).
intro.
subst P.
apply A是AB中点则A与B重合 in H1.
contradiction.

apply L形垂直于转直角.
apply 垂直于的交换性.
apply L形垂直转垂直于.

apply 垂直的对称性.
apply 垂直的左交换性.
eapply cop_par_perp__perp.
apply H6.
apply 直角转L形垂直于 in H9.
apply 垂直于转T形垂直 in H9.
induction H9.
apply 垂直推出不重合1 in H9.
tauto.
apply 垂直的对称性.
eapply 垂线共线点也构成垂直1.
assumption.
apply H9.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1.
assumption.
assumption.

apply par_neq1 in H6.
assumption.
Cop.
unfold 退化平行四边形 in H.
分离合取式.

assert(A = B /\ C = D \/ A = D /\ C = B).
apply(中点蕴含等长_uniqueness A C B D M).
Col.
split; assumption.
assumption.
induction H10.
分离合取式.
subst B.
apply 直角的对称性.
apply 角ABB成直角.
分离合取式.
subst D.
apply 角ABB成直角.
Qed.

Lemma rect_per2 : forall A B C D, 长方形 A B C D -> Per A B C.
Proof.
intros.
apply rect_comm2 in H.
eapply rect_per1.
apply H.
Qed.

Lemma rect_per3 : forall A B C D, 长方形 A B C D -> Per B C D.
Proof.
intros.
apply rect_permut in H.
apply rect_comm2 in H.
eapply rect_per1.
apply H.
Qed.

Lemma rect_per4 : forall A B C D, 长方形 A B C D -> Per A D C.
Proof.
intros.
apply rect_comm2 in H.
eapply rect_per2.
apply rect_permut.
apply H.
Qed.

Lemma plg_per_rect1 : forall A B C D, 平四 A B C D -> Per D A B -> 长方形 A B C D.
Proof.
intros.

assert(HH:= 中点的存在性 A B).
ex_and HH P.
assert(HH:= 中点的存在性 C D).
ex_and HH Q.
assert(HH:=H).
unfold 平四 in HH.
分离合取式.
ex_and H4 M.
apply plg_to_parallelogram in H.
induction H.

assert(HH:=half_plgs A B C D P Q M H H1 H2 H4).
分离合取式.

assert(A <> D /\ P <> Q).
apply par_distincts in H6.
分离合取式.
split; assumption.
分离合取式.

assert(A <> B).
intro.
subst B.
unfold 严格平行四边形 in H.
分离合取式.
unfold TS in H.
分离合取式.
apply H.
Col.
assert(A <> P).
intro.
subst P.
apply A是AB中点则A与B重合 in H1.
contradiction.

assert(Perp P Q A B).
apply (cop_par_perp__perp A D P Q A B).
Par.
apply 直角转L形垂直于 in H0.
apply 垂直于的交换性 in H0.
apply 垂直于转T形垂直 in H0.
induction H0.
apply 垂直的右交换性.
assumption.
apply 垂直推出不重合1 in H0.
tauto.
auto.
assumption.
Cop.

assert(Perp P M A B).
eapply 垂线共线点也构成垂直1.
intro.
subst M.
apply A是AB中点则A与B重合 in H7.
contradiction.
apply H13.
unfold 中点 in H7.
分离合取式.
apply 中间性蕴含共线1 in H7.
Col.

assert(Perp A P P M).
eapply 垂线共线点也构成垂直1.
assumption.
apply 垂直的对称性.
apply H14.
unfold 中点 in H1.
分离合取式.
apply 中间性蕴含共线1 in H1.
Col.

assert(Per A P M).
apply 垂直的交换性 in H15.
apply L形垂直转垂直于 in H15.
apply 垂直于的交换性 in H15.
apply L形垂直于转直角 in H15.
assumption.

unfold 长方形.
split.
apply parallelogram_to_plg .
left.
assumption.

apply 直角的对称性 in H16.
unfold Per in H16.
ex_and H16 B'.
assert(B = B').
eapply 中点组的唯一性1.
apply H1.
assumption.
subst B'.

unfold 中点 in H4.
分离合取式.
unfold 中点 in H5.
分离合取式.
eapply 两组连续三点分段等则全体等.
apply H4.
apply H5.
Cong.
apply 等长的传递性 with A M; Cong.
apply 等长的传递性 with B M; Cong.

unfold 长方形.
split.
apply parallelogram_to_plg.
right.
assumption.

unfold 退化平行四边形 in H.
分离合取式.

assert(D = A \/ B = A).
apply (l8_9_直角三点共线则必有两点重合 D A B).
assumption.
Col.
induction H10.
subst D.
apply 等长的对称性 in H8.
apply 等长的同一性 in H8.
subst C.
Cong.
subst B.
apply 等长的对称性 in H7.
apply 等长的同一性 in H7.
subst D.
Cong.
Qed.

Lemma plg_per_rect2 : forall A B C D, 平四 A B C D -> Per C B A -> 长方形 A B C D.
Proof.
intros.
apply rect_comm2.
apply plg_per_rect1.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_comm2.
assumption.
assumption.
Qed.

Lemma plg_per_rect3 : forall A B C D, 平四 A B C D -> Per A D C -> 长方形 A B C D.
Proof.
intros.
apply rect_permut.
apply plg_per_rect1.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_permut.
apply plg_sym.
assumption.
apply 直角的对称性.
assumption.
Qed.

Lemma plg_per_rect4 : forall A B C D, 平四 A B C D -> Per B C D -> 长方形 A B C D.
Proof.
intros.
apply rect_comm2.
apply plg_per_rect3.
apply parallelogram_to_plg.
apply plg_to_parallelogram in H.
apply plg_comm2.
assumption.
assumption.
Qed.

Lemma plg_per_rect : forall A B C D, 平四 A B C D -> (Per D A B \/ Per C B A \/ Per A D C \/ Per B C D) -> 长方形 A B C D.
Proof.
intros.
induction H0.
apply plg_per_rect1; assumption.
induction H0.
apply plg_per_rect2; assumption.
induction H0.
apply plg_per_rect3; assumption.
apply plg_per_rect4; assumption.
Qed.

Lemma rect_per : forall A B C D, 长方形 A B C D -> Per B A D /\ Per A B C /\ Per B C D /\ Per A D C.
Proof.
intros.
repeat split.
apply (rect_per1 A B C D); assumption.
apply (rect_per2 A B C D); assumption.
apply (rect_per3 A B C D); assumption.
apply (rect_per4 A B C D); assumption.
Qed.

Lemma plgf_rect_id : forall A B C D, 退化平行四边形 A B C D -> 长方形 A B C D -> A = D /\ B = C \/ A = B /\ D = C.
Proof.
intros.
unfold 退化平行四边形 in H.
分离合取式.
assert(Per B A D /\ Per A B C /\ Per B C D /\ Per A D C).

apply rect_per.
assumption.
分离合取式.

assert(HH:=l8_9_直角三点共线则必有两点重合 A B C H6 H).
induction HH.
right.
subst B.
apply 等长的对称性 in H2.
apply 等长的同一性 in H2.
subst D.
split; reflexivity.
left.
subst B.
apply 等长的同一性 in H3.
subst D.
split; reflexivity.
Qed.

Lemma cop_perp3__perp :
 forall A B C D,
  共面 A B C D ->
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Perp D A A B.
Proof.
intros.
assert (Par A B C D)
 by (apply (l12_9 A B C D B C); Perp; Cop).
assert (Perp A B D A)
 by (apply (cop_par_perp__perp C D A B D A); Perp; Par; Cop).
auto using 垂直的对称性, 垂直的左交换性.
Qed.

Lemma cop_perp3__rect :
 forall A B C D,
  共面 A B C D ->
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  长方形 A B C D.
Proof.
intros.
assert (~ Col A B C)
 by (统计不重合点; apply 成直角三点不共线; Perp).
assert (Par A B C D)
 by (apply (l12_9 A B C D B C); Perp; Cop).
assert (Perp D A A B)
 by (eapply cop_perp3__perp;eauto).
assert (Par A D B C)
 by (apply (l12_9 A D B C A B); Perp; Cop).
assert (严格平行四边形 A B C D)
 by (apply (parallel_2_plg); auto).
apply plg_per_rect1.
apply parallelogram_to_plg.
apply 严格平行四边形_平行四边形.
assumption.
Perp.
Qed.

Lemma conga_to_par_os : forall A B C D P , Bet A D P -> OS A D B C -> 等角 B A P C D P
                                           -> Par A B C D.
Proof.
intros A B C D P HBet HOS H等角.
统计不重合点.
apply par_right_comm, l12_22_b with P; trivial.
  apply l6_6, bet_out; Between.
apply invert_one_side, col_one_side with D; Col.
Qed.

Lemma plg_par : forall A B C D, A <> B -> B <> C -> 平行四边形 A B C D -> Par A B C D /\ Par A D B C.
Proof.
intros.
assert(HH:= H1).
apply plg_mid in HH.
ex_and HH M.

assert(HH:=l12_17 A B C D M H H2 H3).
apply M是AB中点则M是BA中点 in H2.
assert(HH1:=l12_17 B C D A M H0 H3 H2).
split.
assumption.
apply par_symmetry.
Par.
Qed.

Lemma plg_par_1 : forall A B C D, A <> B -> B <> C -> 平行四边形 A B C D -> Par A B C D.
Proof.
intros.
assert (HPar := plg_par A B C D H H0 H1); 分离合取式; assumption.
Qed.

Lemma plg_par_2 : forall A B C D, A <> B -> B <> C -> 平行四边形 A B C D -> Par A D B C.
Proof.
intros.
assert (HPar := plg_par A B C D H H0 H1); 分离合取式; assumption.
Qed.

Lemma plgs_pars_1: forall A B C D : Tpoint, 严格平行四边形 A B C D -> 严格平行 A B C D.
Proof.
intros.
assert (HPar := plgs_par_strict A B C D H); 分离合取式; assumption.
Qed.

Lemma plgs_pars_2: forall A B C D : Tpoint, 严格平行四边形 A B C D -> 严格平行 A D B C.
Proof.
intros.
assert (HPar := plgs_par_strict A B C D H); 分离合取式; assumption.
Qed.

End Quadrilateral_inter_dec_2.

Ltac not_exist_hyp_perm_par A B C D := not_exist_hyp (Par A B C D); not_exist_hyp (Par A B D C);
                                       not_exist_hyp (Par B A C D); not_exist_hyp (Par B A D C);
                                       not_exist_hyp (Par C D A B); not_exist_hyp (Par C D B A);
                                       not_exist_hyp (Par D C A B); not_exist_hyp (Par D C B A).

Ltac not_exist_hyp_perm_pars A B C D := not_exist_hyp (严格平行 A B C D); not_exist_hyp (严格平行 A B D C);
                                        not_exist_hyp (严格平行 B A C D); not_exist_hyp (严格平行 B A D C);
                                        not_exist_hyp (严格平行 C D A B); not_exist_hyp (严格平行 C D B A);
                                        not_exist_hyp (严格平行 D C A B); not_exist_hyp (严格平行 D C B A).

Ltac assert_pars_1 :=
 repeat
 match goal with
      | H:严格平行 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X2 X3 X4;
      assert (h := par_strict_par X1 X2 X3 X4 H)

      | H:Par ?X1 ?X2 ?X3 ?X4, H2:Col ?X1 ?X2 ?X5, H3:(~Col ?X3 ?X4 ?X5) |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X2 X3 X4;
      assert (h := par_not_col_strict X1 X2 X3 X4 X5 H H2 H3)

      | H: ?X1 <> ?X2, H2:?X2 <> ?X3, H3:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X2 X3 X4;
      assert (h := plg_par_1 X1 X2 X3 X4 H H2 H3)

      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X2 X3 X4;
      assert (h := plgs_pars_1 X1 X2 X3 X4 H)

      | H: ?X1 <> ?X2, H2:?X2 <> ?X3, H3:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_par X1 X4 X2 X3;
      assert (h := plg_par_2 X1 X2 X3 X4 H H2 H3)

      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
      let h := fresh in
      not_exist_hyp_perm_pars X1 X4 X2 X3;
      assert (h := plgs_pars_2 X1 X2 X3 X4 H)
  end.

Ltac assert_pars_perm := permutation_intro_in_hyps; assert_pars_1; clean_reap_hyps.

Hint Resolve plg_par_1 plg_par_2 plgs_pars_1 plgs_pars_2 : par.

Section Quadrilateral_inter_dec_3.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma par_cong_cong : forall A B C D, Par A B C D -> Cong A B C D -> Cong A C B D \/ Cong A D B C.
Proof.
intros.

induction(两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H0.
apply 等长的同一性 in H0.
subst D.
left.
Cong.

induction(两点重合的决定性 A D).
subst D.

assert(B = C \/ 中点 A B C).
eapply 共线点间距相同要么重合要么中点.
unfold Par in H.
induction H.
apply False_ind.
unfold 严格平行 in H.
分离合取式.
apply H2.
exists A.
split; Col.
分离合取式.
Col.
Cong.
induction H2.
subst C.
left.
Cong.
unfold 中点 in H2.
分离合取式.
left.
Cong.

assert(HH:=par_cong_mid A B C D H H0).
ex_and HH M.
induction H3.
分离合取式.
right.

assert(HH:=mid_par_cong A B C D M H1 H2 H3 H4).
分离合取式.
Cong.

induction(两点重合的决定性 A C).
subst C.
assert(B = D \/ 中点 A B D).
eapply 共线点间距相同要么重合要么中点.
unfold Par in H.
induction H.
apply False_ind.
unfold 严格平行 in H.
分离合取式.
apply H5.
exists A.
split; Col.
分离合取式.
Col.
Cong.
induction H4.
subst D.
right.
Cong.
unfold 中点 in H4.
分离合取式.
right.
Cong.

left.
分离合取式.
assert(HH:=mid_par_cong A B D C M H1 H4 H3 H5).
分离合取式.
Cong.
Qed.

Lemma col_cong_cong : forall A B C D, Col A B C -> Col A B D -> Cong A B C D -> Cong A C B D \/ Cong A D B C.
Proof.
intros.

induction(两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H1.
apply 等长的同一性 in H1.
subst D.
left.
Cong.

induction(两点重合的决定性 C D).
subst D.
apply 等长的同一性 in H1.
subst B.
right.
Cong.

apply par_cong_cong.
right.
repeat split; ColR.
assumption.
Qed.

Lemma par_cong_cop :
  forall A B C D, Par A B C D -> Cong A B C D -> 共面 A B C D.
Proof.
intros.
destruct (par_cong_mid A B C D) as [M HM]; trivial.
exists M; right.
destruct HM as [[]|[]]; [left|right]; split; Col.
Qed.

Lemma par_cong_plg :
  forall A B C D, Par A B C D -> Cong A B C D -> 平四 A B C D \/ 平四 A B D C.
Proof.
intros A B C D HPar HCong.
destruct (par_cong_mid A B C D) as [M HM]; trivial.
elim HM; clear HM; intro HM; destruct HM as [HMid1 HMid2].

  {
  left; split; [|exists M; split; assumption].
  destruct (两点重合的决定性 A C); [|left; assumption].
  apply par_distinct in HPar.
  right; intro; treat_equalities; apply HPar; reflexivity.
  }

  {
  right; split; [|exists M; split; assumption].
  destruct (两点重合的决定性 A D); [|left; assumption].
  apply par_distinct in HPar.
  right; intro; treat_equalities; apply HPar; reflexivity.
  }
Qed.

Lemma par_cong_plg_2 :
  forall A B C D,
  Par A B C D ->
  Cong A B C D ->
  平行四边形 A B C D \/ 平行四边形 A B D C.
Proof.
intros.
assert (HElim : 平四 A B C D \/ 平四 A B D C)
  by (apply par_cong_plg; assumption).
elim HElim; intro.

  left; apply plg_to_parallelogram; assumption.

  right; apply plg_to_parallelogram; assumption.
Qed.

Lemma par_cong3_rect : forall A B C D, A <> C \/ B <> D -> Par A B C D -> Cong A B C D -> Cong A D B C -> Cong A C B D -> 长方形 A B C D \/ 长方形 A B D C.
Proof.
intros.
unfold Par in H0.
induction H0.

assert(HH:=par_strict_cong_mid1 A B C D H0 H1).

induction HH.
分离合取式.
left.
unfold 长方形.
split; auto.
unfold 平四.
split; auto.
分离合取式.
ex_and H5 M.

right.
unfold 长方形.
split; auto.
unfold 平四.
split; auto.

left.
intro.
subst D.
unfold 严格平行 in H0.
分离合取式.
apply H7.
exists A.
split; Col.
exists M.
split; auto.

分离合取式.
left.
unfold 长方形.
split; auto.

apply parallelogram_to_plg.
unfold 平行四边形.
right.
unfold 退化平行四边形.

induction(两点重合的决定性 C D).
subst D.
apply 等长的同一性 in H1.
subst B.
repeat split; Col; Cong.
repeat split; Col; Cong; ColR.
Qed.

Lemma pars_par_pars : forall A B C D, 严格平行 A B C D -> Par A D B C -> 严格平行 A D B C.
Proof.
intros.
induction H0.
assumption.
分离合取式.
repeat split; Cop.
intro.
ex_and H4 X.
unfold 严格平行 in H.
分离合取式.
apply H6.
exists C.
split; Col.
Qed.

Lemma pars_par_plg : forall A B C D, 严格平行 A B C D -> Par A D B C -> 平四 A B C D.
Proof.
intros.
assert(严格平行 A D B C).
apply pars_par_pars; auto.

assert(Par A B C D).
left.
assumption.

assert(A <> B /\ C <> D /\ A <> D /\ B <> C).
apply par_distinct in H0.
apply par_distinct in H2.
分离合取式.
auto.
分离合取式.

assert(A <> C).
intro.
subst C.
unfold 严格平行 in H.
分离合取式.
apply H7.
exists A.
split; Col.

assert(B <> D).
intro.
subst D.
unfold 严格平行 in H.
分离合取式.
apply H8.
exists B.
split; Col.

unfold 平四.
split.

left.
assumption.

assert(HH:=中点的存在性 A C).
ex_and HH M.
exists M.
split.
assumption.
prolong B M D' B M.
assert(中点 M B D').
unfold 中点.
split; auto.
Cong.
assert(平四 A B C D').
unfold 平四.
repeat split.
induction H.
left.

assumption.

exists M.
split; auto.

assert(平行四边形 A B C D').
apply plg_to_parallelogram.
assumption.
assert(HH:=plg_par A B C D' H3 H6 H14).
分离合取式.

assert(~Col C A B).
intro.
unfold 严格平行 in H.
分离合取式.
apply H18.
exists C.
split; Col.

assert(Col C C D /\ Col D' C D).

apply (parallel_uniqueness A B C D C D' C H2).
Col.
assumption.
Col.
分离合取式.

assert(A <> D').
intro.
subst D'.
unfold 严格平行 in H1.
分离合取式.
apply H20.
exists C.
split; Col.

assert(HH:=mid_par_cong A B C D' M H3 H20 H9 H12).
分离合取式.

assert(Col A A D /\ Col D' A D).
apply (parallel_uniqueness B C A D A D' A).

Par.
Col.
apply par_left_comm.
Par.
Col.
分离合取式.

assert(D = D').

eapply (l6_21_两线交点的唯一性 A D C D D D'); Col.
intro.
unfold 严格平行 in H.
分离合取式.
apply H28.
exists A.
split; Col.
subst D'.
assumption.
Qed.

Lemma not_par_pars_not_cong : forall O A B A' B', Out O A B -> Out O A' B' -> 严格平行 A A' B B' -> ~Cong A A' B B'.
Proof.
intros.
intro.

assert(A <> B).
intro.
subst B.
unfold 严格平行 in H1.
分离合取式.
apply H3.
exists A.
split; Col.

assert(A' <> B').
intro.
subst B'.
unfold 严格平行 in H1.
分离合取式.
apply H4.
exists A'.
split; Col.

assert(O <> A).
unfold Out in H.
分离合取式.
auto.

assert(O <> A').
unfold Out in H0.
分离合取式.
auto.

assert(~Col O A A').
intro.
apply out_col in H.
apply out_col in H0.
assert(Col O B A').
ColR.
unfold 严格平行 in H1.
分离合取式.
apply H9.
exists O.
split.
assumption.
ColR.

assert(OS A B A' B').

apply(out_one_side_1 _ _  _ _ O).
intro.
apply H7.
apply out_col in H.
apply out_col in H0.
ColR.
apply out_col in H.
Col.
assumption.

assert(Par A A' B B').
left.
assumption.

assert(HH:=os_cong_par_cong_par A A' B B' H8 H2 H9).
分离合取式.
unfold Par in H11.
induction H11.
unfold 严格平行 in H11.
分离合取式.
apply H12.
exists O.
split.
apply out_col in H.
assumption.
apply out_col in H0.
assumption.
分离合取式.
apply H7.
apply out_col in H.
apply out_col in H0.
ColR.
Qed.

Lemma plg_uniqueness : forall A B C D D', 平行四边形 A B C D -> 平行四边形 A B C D' -> D = D'.
Proof.
intros.
apply plg_mid in H.
apply plg_mid in H0.
ex_and H M.
ex_and H0 M'.
assert(M = M').
eapply 中点的唯一性1.
apply H.
assumption.
subst M'.
eapply 中点组的唯一性1.
apply H1.
assumption.
Qed.

Lemma plgs_trans_trivial : forall A B C D B', 严格平行四边形 A B C D -> 严格平行四边形 C D A B' 
                                             -> 平行四边形 A B B' A.
Proof.
intros.
apply plgs_permut in H.
apply plgs_permut in H.
assert (B = B').
eapply plg_uniqueness.
left.
apply H.
left.
assumption.
subst B'.
apply plg_trivial.
apply plgs_diff in H.
分离合取式.
assumption.
Qed.

Lemma par_strict_trans : forall A B C D E F, 严格平行 A B C D -> 严格平行 C D E F -> Par A B E F.
Proof.
intros.
eapply par_trans.
left.
apply H.
left.
assumption.
Qed.

Lemma plgs_pseudo_trans : forall A B C D E F, 严格平行四边形 A B C D -> 严格平行四边形 C D E F -> 平行四边形 A B F E.
Proof.
intros.

induction(两点重合的决定性 A E).
subst E.
eapply (plgs_trans_trivial A B C D); assumption.

apply plgs_diff in H.
apply plgs_diff in H0.
分离合取式.

clean_duplicated_hyps.

prolong D C D' D C.

assert(C <> D').
intro.
subst D'.
apply 等长的对称性 in H14.
apply 等长的同一性 in H14.
subst D.
tauto.

assert(HH1:=plgs_par_strict A B C D H).
assert(HH2:=plgs_par_strict C D E F H0).
分离合取式.

apply par_strict_symmetry in H18.

assert(HH1:= l12_6 C D A B H18).
assert(HH2:= l12_6 C D E F H16).


assert(等角 A D D' B C D').
apply par_preserves_conga_os.
left.
Par.
assumption.
assumption.
apply invert_one_side.
assumption.

assert(等角 E D D' F C D').
apply par_preserves_conga_os.
left.
Par.
assumption.
assumption.
apply invert_one_side.
assumption.

assert(~ Col A C D).
apply (par_strict_not_col_2 B).
Par.

assert(~ Col E C D).
apply (par_strict_not_col_2 F).
Par.

induction (cop_dec C D A E).

assert(HH:=cop__one_or_two_sides C D A E H24 H22 H23).

assert(等角 A D E B C F).

induction HH.

assert(TS C D A F).
apply l9_2.
eapply l9_8_2.
apply l9_2.
apply H25.
assumption.

assert(TS C D B F).
eapply l9_8_2.
apply H26.
assumption.

apply(l11_22a A D E D' B C F D').
split.
eapply col_two_sides.
apply 中间性蕴含共线1.
apply H2.
intro.
subst D'.
apply 中间性的同一律 in H2.
subst D.
tauto.
apply invert_two_sides.
assumption.
split.
eapply (col_two_sides _ D).
apply 中间性蕴含共线1 in H2.
Col.
assumption.
assumption.
split.
assumption.
apply 等角的交换性.
assumption.

apply(l11_22b A D E D' B C F D').
split.
eapply col_one_side.
apply 中间性蕴含共线1.
apply H2.
intro.
subst D'.
apply 中间性的同一律 in H2.
subst D.
tauto.
apply invert_one_side.
assumption.
split.
eapply (col_one_side _ D).
apply 中间性蕴含共线1 in H2.
Col.
assumption.
eapply one_side_transitivity.
apply one_side_symmetry.
apply HH1.
apply one_side_symmetry.
eapply one_side_transitivity.
apply one_side_symmetry.
apply HH2.
apply one_side_symmetry.
assumption.
split.
assumption.
apply 等角的交换性.
assumption.

assert(HP0:=plgs_cong A B C D H).
assert(HP1:=plgs_cong C D E F H0).
分离合取式.
apply 等长的对称性 in H27.

assert(HP:=等角两边等长则端点间距相等 A D E B C F H25 H29 H27).
(**************)

assert(Par A B E F).
eapply par_trans.
apply par_symmetry.
left.
apply H18.
left.
assumption.

induction(共线的决定性 A E F).
induction H30.
apply False_ind.
apply H30.
exists A.
split; Col.
分离合取式.

right.
unfold 退化平行四边形.
repeat split; Cong.
ColR.
ColR.
apply 等长的传递性 with C D; Cong.

induction(两点重合的决定性 A F).
right.
subst F.
intro.
subst E.

apply 等长的对称性 in H27.

assert(HQ:=par_strict_cong_mid C A D B H17 H27).
ex_and HQ M.
induction H35.
unfold 中点 in *.
分离合取式.

apply H16.
exists M.
split; Col.
unfold 中点 in *.
分离合取式.
apply H19.
exists M.
split.
ColR.
ColR.
left.
assumption.

assert(Par A E B F \/ ~ 严格平行 D C A B \/ ~ 严格平行 D C E F).

eapply(cong3_par2_par ); auto.
repeat split; Cong.
apply par_comm.
left.
assumption.
apply par_symmetry.
left.
assumption.

induction H32.
apply plg_to_parallelogram.
apply pars_par_plg.

assert(Par A B F E).
eapply par_trans.
apply par_symmetry.
left.
apply H18.
apply par_right_comm.
left.
assumption.
induction H33.
assumption.
分离合取式.
apply False_ind.
apply H31.
Col.
assumption.
induction H32.
apply False_ind.
apply H32.
apply par_strict_left_comm.
assumption.
apply False_ind.
apply H32.
apply par_strict_left_comm.
assumption.

destruct (par_cong_plg_2 A B E F); auto.
apply par_trans with C D; Par.
apply 等长的传递性 with C D; apply plgs_cong_1; assumption.
exfalso.

assert (OS A E B F).
apply (cop3_osp__os A D E); Cop.
assert (~ Col D A B) by (apply (par_strict_not_col_2 C), H18).
apply osp_transitivity with C.
  apply cop2_os__osp with A D; [|Cop..|Side].
  intro; apply H24, 等价共面CABD, coplanar_trans_1 with B; Col; Cop.
apply cop2_os__osp with D E; [|Cop..|Side].
intro; apply H24, 等价共面CABD, coplanar_trans_1 with C; Col; Cop.

apply (l9_9 A E B F); [|assumption].
repeat split.
  apply one_side_not_col123 in H26; Col.
  apply one_side_not_col124 in H26; Col.
apply plg_mid in H25.
destruct H25 as [M []].
exists M; split; [Col|Between].
Qed.



Lemma plgf_plgs_trans : forall A B C D E F, A <> B -> 退化平行四边形 A B C D -> 严格平行四边形 C D E F -> 严格平行四边形 A B F E.
Proof.
intros.

induction(两点重合的决定性 A D).
subst D.
induction H0.
分离合取式.
apply 等长的对称性 in H4.
apply 等长的同一性 in H4.
分离合取式.
subst C.
apply plgs_comm2.
assumption.

induction(两点重合的决定性 B C).
subst C.
induction H0.
分离合取式.
apply 等长的同一性 in H5.
分离合取式.
subst D.
apply plgs_comm2.
assumption.

assert(HH:=plgs_par_strict C D E F H1).
分离合取式.

assert(HH:=plgs_cong C D E F H1).
分离合取式.

assert(HH2:= l12_6 C D E F H4).

assert(HOS := HH2).
induction HH2.
分离合取式.

unfold TS in H9.
assert(~ Col F C D).
分离合取式.
assumption.
分离合取式.
unfold TS in H8.
assert(~ Col E C D).
分离合取式.
assumption.
分离合取式.

assert(D <> E).
intro.
subst E.
apply H13.
Col.
assert(HH0:=H0).

induction HH0.
分离合取式.

prolong D C D' D C.

assert(D <> D').
intro.
subst D'.
apply 中间性的同一律 in H22.
subst D.
Col.

assert(C <> D').
intro.
subst D'.
apply 等长的对称性 in H23.
apply 等长的同一性 in H23.
contradiction.


assert(等角 E D D' F C D').

apply(par_preserves_conga_os D E F C D').
apply par_symmetry.
apply par_left_comm.
left.
assumption.
assumption.
intro.
subst D'.
apply 等长的对称性 in H23.
apply 等长的同一性 in H23.
subst D.
tauto.
apply invert_one_side.
assumption.

induction(两点重合的决定性 A C).
subst C.
assert(B=D \/ 中点 A B D).
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.
(*induction H21.
tauto.*)
induction H27.
induction H21.
tauto.
contradiction.

unfold 严格平行四边形.
分离合取式.
split.

apply l9_2.

eapply (l9_8_2  _ _ D).
unfold TS.
repeat split.
intro.
apply H10.
Col.
intro.
apply H10.
ColR.

exists A.
split.
Col.
apply midpoint_bet.
apply M是AB中点则M是BA中点.
assumption.
eapply l12_6.
assumption.
split.
eapply (par_col_par_2 _ D).
auto.
unfold 中点 in H27.
分离合取式.
apply 中间性蕴含共线1 in H27.
Col.
apply par_right_comm.
left.
assumption.
apply 等长的传递性 with A D; Cong.

induction(两点重合的决定性 B D).
subst D.

assert(A=C \/ 中点 B A C).
eapply 共线点间距相同要么重合要么中点.
Col.
Cong.

induction H28.
tauto.

apply plgs_comm2.
unfold 严格平行四边形.
split.
apply l9_2.

eapply (l9_8_2 _ _ C).
unfold TS.
repeat split.
auto.
intro.
apply H13.
Col.
intro.
apply H13.
ColR.
exists B.
split.
Col.
apply midpoint_bet.
apply M是AB中点则M是BA中点.
assumption.
eapply l12_6.
apply par_strict_symmetry.
assumption.
split.
eapply (par_col_par_2 _ C).
auto.
unfold 中点 in H28.
分离合取式.
apply 中间性蕴含共线1 in H28.
Col.
apply par_left_comm.
left.
assumption.
apply 等长的传递性 with C B; Cong.

assert(HH:=plgf_bet A B D C H0).

assert(等角 A D E B C F).

induction HH.
分离合取式.
eapply l11_10.
apply 等角的交换性.
apply H26.
repeat split.
auto.
auto.
eapply (l5_1 _ C).
intro.
subst D.
Col.
Between.
Between.
apply out_trivial.
intro.
subst E.
apply H13.
Col.
repeat split.
auto.
auto.

assert(Bet D C B).
eapply 中间性的外传递性2.
apply H29.
assumption.
auto.

eapply (l5_2 D);
auto.
intro.
subst D.
Col.

apply out_trivial.
intro.
subst F.
apply H10.
Col.

induction H29.

分离合取式.

apply (l11_10 D' D E D' C F).
apply 等角的交换性.
apply H26.
repeat split;auto.
left.
eBetween.
apply out_trivial.
intro.
subst E.
apply H13.
Col.
repeat split; auto.
left.

eapply (bet3_cong3_bet A B C D D');
auto;
Cong.
apply out_trivial.
intro.
subst F.
apply H10.
Col.

induction H29.
分离合取式.

eapply l11_13.

apply 等角的交换性.
apply H26.

统计不重合点.
apply 中间性的对称性.
apply 中间性的外传递性2 with C.
apply 中间性的外传递性2 with B.
assumption.
assumption.
auto.
assumption.
auto.
auto.
apply 中间性的内传递性1 with D.
Between.
Between.
auto.

分离合取式.

eapply l11_13.

apply 等角的交换性.

apply H26.
统计不重合点.
apply 中间性的外传递性2 with B.
apply 中间性的对称性.
apply 中间性的外传递性2 with C.
assumption.
assumption.
auto.
Between.
auto.
auto.
统计不重合点.
apply 中间性的外传递性2 with D.
Between.
Between.
auto.
auto.


assert(Cong A E B F).

eapply(等角两边等长则端点间距相等 A D E B C F H29);Cong.
assert(三角形全等 E A D F B C).
repeat split; Cong.

assert(Par A B E F).
eapply (par_trans A B C D E F).
right.
repeat split; auto.
intro.
subst.
Col.
ColR.
ColR.
left.
assumption.

assert(等角 E A D F B C).
apply 三角形全等推角等1.
intro.
subst E.
apply H13.
ColR.
auto.
assumption.

assert(OS A B E F).
eapply l12_6.
induction H32.
assumption.
分离合取式.
assert(Col A B E).
ColR.
apply False_ind.
apply H13.
eapply (共线的传递性4 A B); Col.

assert(Par A E F B).

induction HH.

prolong A B A' A B.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply 等角的交换性.
eapply l11_13.
apply 等角的交换性.
apply H33.
apply 中间性的外传递性2 with B.
apply 中间性的对称性.
apply 中间性的外传递性2 with C.
Between.
Between.
auto.
assumption.
auto.
intro.
subst A'.
apply 中间性的同一律 in H36.
contradiction.
apply 中间性的对称性.
apply 中间性的外传递性2 with A.
Between.
Between.
auto.
intro.
subst A'.
apply 等长的对称性 in H37.
apply 等长的同一性 in H37.
contradiction.

induction H35.
分离合取式.

prolong A B A' A B.
apply (conga_to_par_os _ _ _ _ A');
auto.
apply 等角的交换性.
eapply l11_13.
apply 等角的交换性.
apply H33.
apply 中间性的外传递性2 with B.
apply 中间性的外传递性2 with C.
assumption.
assumption.
auto.
assumption.
auto.
intro.
subst A'.
apply 中间性的同一律 in H37.
contradiction.
apply 中间性的交换传递性1 with A.
assumption.
assumption.
intro.
subst A'.
apply 等长的对称性 in H38.
apply 等长的同一性 in H38.
contradiction.

induction H35.
分离合取式.
prolong A B A' A B.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply 等角的交换性.

eapply l11_10.
apply 等角的交换性.
apply H33.
repeat split; auto.
intro.
subst A'.
apply 中间性的同一律 in H37.
contradiction.
right.
apply 中间性的交换传递性2 with B.
assumption.
assumption.
apply out_trivial.
intro.
subst E.
apply H13.
ColR.
repeat split; auto.
intro.
subst A'.
apply 等长的对称性 in H38.
apply 等长的同一性 in H38.
contradiction.
right.
eapply (bet3_cong3_bet D _ _ A); Cong.
intro.
subst D.
Col.
apply out_trivial.
intro.
subst F.
apply H10.
ColR.

分离合取式.
prolong A B A' A C.

apply (conga_to_par_os _ _ _ _ A');
auto.
apply 等角的交换性.

eapply l11_10.
apply 等角的交换性.
apply H33.
repeat split; auto.
intro.
subst A'.
apply 中间性的同一律 in H37.
contradiction.
right.

assert(Bet B C A').
eapply (bet_cong_bet A); auto.
apply 中间性的外传递性2 with D.
assumption.
assumption.
auto.
Cong.
apply 中间性的内传递性2 with B.
assumption.
apply 中间性的交换传递性2 with C.
assumption.
assumption.
apply out_trivial.
intro.
subst E.
apply H13.
ColR.
repeat split.
intro.
subst A'.
apply 等长的对称性 in H38.
apply 等长的同一性 in H38.
contradiction.
auto.
right.

apply (bet_cong_bet A); auto.
apply 中间性的外传递性2 with D.
assumption.
assumption.
auto.
Cong.
apply out_trivial.
intro.
subst F.
apply H10.
ColR.

assert(平四 A B F E).
apply pars_par_plg.
induction H32.
apply par_strict_right_comm.
assumption.
分离合取式.
apply False_ind.
assert(Col A B E).
ColR.
apply H13.
eapply (共线的传递性4 A B); Col.
Par.
apply plg_to_parallelogram in H36.
induction H36.
assumption.
unfold 退化平行四边形 in H36.
分离合取式.

assert(Col A B E).
ColR.
apply False_ind.
apply H13.
eapply (共线的传递性4 A B); Col.
Qed.

Lemma plgf_plgf_plgf: forall A B C D E F, A <> B -> 退化平行四边形 A B C D -> 退化平行四边形 C D E F
                                          -> 退化平行四边形 A B F E.
Proof.
intros.
assert(C <> D).
unfold 退化平行四边形 in H0.
分离合取式.
intro.
subst D.
apply 等长的同一性 in H3.
contradiction.
assert(E <> F).
unfold 退化平行四边形 in H1.
分离合取式.
intro.
subst F.
apply 等长的同一性 in H4.
contradiction.

assert(HH:=plgs_existence C D H2).
ex_and HH D'.
ex_and H4 C'.

assert(严格平行四边形 A B C' D').
eapply (plgf_plgs_trans A B C D); auto.
assert(严格平行四边形 E F C' D').
eapply (plgf_plgs_trans E F C D); auto.

apply plgf_sym.
assumption.
assert(平行四边形 A B F E).
eapply plgs_pseudo_trans.
apply H4.
apply plgs_sym.
assumption.
induction H7.
induction H7.
unfold TS in H7.
分离合取式.
unfold 退化平行四边形 in *.
分离合取式.
apply False_ind.
apply H10.

assert(Col C D A).
ColR.
assert(Col C D B).
ColR.
apply (共线的传递性4 C D); Col.
assumption.
Qed.

Lemma plg_pseudo_trans : forall A B C D E F, 平行四边形 A B C D -> 平行四边形 C D E F -> 平行四边形 A B F E \/ (A = B /\ C = D /\ E = F /\ A = E).
Proof.
intros.
induction(两点重合的决定性 A B).
subst B.
induction H.
unfold 严格平行四边形 in H.
分离合取式.
unfold TS in H.
分离合取式.
apply False_ind.
apply H.
Col.
assert(C = D).
assert(HH:=plgf_trivial_neq A C D H).
分离合取式.
assumption.
subst D.
induction H0.
unfold 严格平行四边形 in H0.
分离合取式.
unfold TS in H0.
分离合取式.
apply False_ind.
apply H0.
Col.
assert(E=F).
assert(HH:=plgf_trivial_neq C E F H0).
分离合取式.
assumption.
subst F.
induction (两点重合的决定性 A E).
right.
repeat split; auto.
left.
apply plg_trivial1.
assumption.


assert(C <> D).
intro.
subst D.
induction H.
unfold 严格平行四边形 in H.
分离合取式.
unfold TS in H.
分离合取式.
apply H4.
Col.
apply plgf_sym in H.
apply plgf_trivial_neq in H.
分离合取式.
contradiction.

assert(E <> F).
intro.
subst F.
induction H0.
unfold 严格平行四边形 in H0.
分离合取式.
unfold TS in H0.
分离合取式.
apply H5.
Col.
apply plgf_sym in H0.
apply plgf_trivial_neq in H0.
分离合取式.
contradiction.

left.
induction H; induction H0.
eapply plgs_pseudo_trans.
apply H.
assumption.
left.
apply plgs_sym.
apply (plgf_plgs_trans F E D C);auto.
apply plgf_comm2.
apply plgf_sym.
assumption.
apply plgs_comm2.
apply plgs_sym.
assumption.
left.
apply (plgf_plgs_trans A B C D E F); auto.
right.
apply  (plgf_plgf_plgf A B C D E F); auto.
Qed.

Lemma 正方形_菱形 : forall A B C D,
 正方形 A B C D -> 菱形 A B C D.
Proof.
intros.
unfold 菱形.
split.
apply 正方形_平行四边形 in H.
apply parallelogram_to_plg in H.
assumption.
unfold 正方形 in H.
tauto.
Qed.

Lemma plgs_in_angle : forall A B C D, 严格平行四边形 A B C D -> 在角内 D A B C.
Proof.
intros.
assert(平四 A B C D).
apply parallelogram_to_plg.
left.
assumption.

unfold 严格平行四边形 in H.
unfold 平四 in H0.
分离合取式.
ex_and H1 M.

assert(A <> B /\ C <> B).
unfold TS in H.
分离合取式.

split;
intro;
subst B;
apply H;
Col.
分离合取式.

assert(HH:=H).
unfold TS in HH.
分离合取式.
ex_and H9 T.

unfold 在角内.
repeat split; auto.
intro.
subst D.
apply M是AA中点则M与A重合 in H4.
subst M.
apply midpoint_bet in H1.
apply H7.
apply 中间性蕴含共线1 in H1.
Col.

exists M.
split.
apply midpoint_bet.
auto.
right.

unfold Out.
repeat split.
intro.
subst M.
unfold 中点 in H4.
分离合取式.
apply 等长的对称性 in H11.
apply 等长的同一性 in H11.
subst D.
apply 中间性的同一律 in H10.
subst T.
contradiction.
intro.
subst D.
apply 中间性的同一律 in H10.
subst T.
contradiction.
left.
apply midpoint_bet.
auto.
Qed.

Lemma par_par_cong_cong_parallelogram :
 forall A B C D,
 B<>D ->
 Cong A B C D ->
 Cong B C D A ->
 Par B C A D ->
 Par A B C D ->
 平行四边形 A B C D.
Proof.
intros.
assert (平行四边形 A B C D \/ 平行四边形 A B D C)
 by (apply par_cong_plg_2; assumption).
assert (平行四边形 B C A D \/ 平行四边形 B C D A)
 by (apply par_cong_plg_2; Cong).
induction H4.
assumption.
induction H5.
apply 平四_perm in H4.
apply 平四_perm in H5.
统计不重合点.
分离合取式.
apply plg_not_comm in H8.
intuition.
auto.
apply 平四_perm in H5.
分离合取式.
assumption.
Qed.

Lemma degenerated_rect_eq : forall A B C, 长方形 A B B C -> A = C.
Proof.
intros A B C HRect.
apply 长方形_平行四边形 in HRect; apply plg_mid in HRect.
destruct HRect as [M [HMid1 HMid2]]; treat_equalities; auto.
Qed.

Lemma rect_2_rect : forall A B C1 C2 D1 D2,
  A <> B ->
  长方形 A B C1 D1 ->
  长方形 A B C2 D2 ->
  长方形 C1 D1 D2 C2.
Proof.
intros A B C1 C2 D1 D2 HDiff HRect1 HRect2.
elim (两点重合的决定性 C1 C2); intro HC1C2; treat_equalities.

  {
  apply 长方形_平行四边形 in HRect1; apply plg_mid in HRect1.
  apply 长方形_平行四边形 in HRect2; apply plg_mid in HRect2.
  destruct HRect1 as [M [HMid1 HMid2]]; destruct HRect2 as [M' [HMid3 HMid4]].
  treat_equalities; split; Cong; apply parallelogram_to_plg.
  apply plg_trivial; intro; treat_equalities; auto.
  }

  {
  elim (两点重合的决定性 B C1); intro HBC1; elim (两点重合的决定性 B C2); intro HBC2;
  treat_equalities; [intuition|apply degenerated_rect_eq in HRect1; treat_equalities|
                     apply degenerated_rect_eq in HRect2; treat_equalities|];
  apply rect_comm2; auto; apply rect_comm2; do 2 (apply rect_permut); auto.
  assert (HPara1 := HRect1); apply 长方形_平行四边形 in HPara1.
  assert (HPara2 := HRect2); apply 长方形_平行四边形 in HPara2.

  assert (HNC1 : ~ Col A B C1) by (apply rect_per2 in HRect1; apply 成直角三点不共线; auto).
  assert (HNC2 : ~ Col A B C2) by (apply rect_per2 in HRect2; apply 成直角三点不共线; auto).
  apply plg_per_rect2.

    {
    elim HPara1; clear HPara1; intro HPara1;
    [|unfold 退化平行四边形 in HPara1; 分离合取式; intuition].
    elim HPara2; clear HPara2; intro HPara2;
    [|unfold 退化平行四边形 in HPara2; 分离合取式; intuition].
    apply parallelogram_to_plg; apply plgs_pseudo_trans with B A;
    apply plgs_comm2; auto; do 2 (apply plgs_permut); auto.
    }

  elim (cop_dec A B C1 C2); intro HCop.

    {
    apply L形垂直转直角1, 垂直的对称性, cop_par_perp__perp with A B; Cop;
    apply plg_par_1 in HPara2; Par; clear HPara1; clear HPara2.
    apply rect_per2 in HRect1; apply rect_per2 in HRect2.
    assert (HCol : Col C1 C2 B) by (apply cop_per2__col with A; Perp; Cop).
    apply 与垂线共线之线也为垂线1 with B C1; Col; apply 直角转L形垂直 in HRect1; Perp.
    }

    {
    apply rect_per in HRect1; apply rect_per in HRect2; 分离合取式.
    destruct (两点重合的决定性 C2 D2); [subst; Perp|].
    assert (HOrth : 垂直平面于 C2 B C1 C2 C2 D2);
      [|destruct HOrth as [_ [_ [_ [_ HOrth]]]]; apply HOrth; Col; Cop].
    apply l11_61_bis with B A; Perp; Cop.
    apply l11_60_bis; Perp; Cop.
    apply 四点不共面则前三点不共线 with A; Cop.
    }
  }
Qed.

Lemma ncol123_plg__plgs : forall A B C D,
  ~ Col A B C -> 平行四边形 A B C D -> 严格平行四边形 A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold 退化平行四边形 in *; 分离合取式; Col.
Qed.

Lemma ncol124_plg__plgs : forall A B C D,
  ~ Col A B D -> 平行四边形 A B C D -> 严格平行四边形 A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold 退化平行四边形 in *; 分离合取式; Col.
Qed.

Lemma ncol134_plg__plgs : forall A B C D,
  ~ Col A C D -> 平行四边形 A B C D -> 严格平行四边形 A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold 退化平行四边形 in *; 分离合取式; ColR.
Qed.

Lemma ncol234_plg__plgs : forall A B C D,
  ~ Col B C D -> 平行四边形 A B C D -> 严格平行四边形 A B C D.
Proof.
intros A B C D HNC H; induction H; auto.
exfalso; apply HNC; unfold 退化平行四边形 in *; 分离合取式; ColR.
Qed.

Lemma ncol123_plg__pars1234 : forall A B C D,
  ~ Col A B C -> 平行四边形 A B C D -> 严格平行 A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol123_plg__plgs; auto.
Qed.

Lemma ncol124_plg__pars1234 : forall A B C D,
  ~ Col A B D -> 平行四边形 A B C D -> 严格平行 A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol124_plg__plgs; auto.
Qed.

Lemma ncol134_plg__pars1234 : forall A B C D,
  ~ Col A C D -> 平行四边形 A B C D -> 严格平行 A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol134_plg__plgs; auto.
Qed.

Lemma ncol234_plg__pars1234 : forall A B C D,
  ~ Col B C D -> 平行四边形 A B C D -> 严格平行 A B C D.
Proof.
intros; apply plgs_pars_1; apply ncol234_plg__plgs; auto.
Qed.

Lemma ncol123_plg__pars1423 : forall A B C D,
  ~ Col A B C -> 平行四边形 A B C D -> 严格平行 A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol123_plg__plgs; auto.
Qed.

Lemma ncol124_plg__pars1423 : forall A B C D,
  ~ Col A B D -> 平行四边形 A B C D -> 严格平行 A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol124_plg__plgs; auto.
Qed.

Lemma ncol134_plg__pars1423 : forall A B C D,
  ~ Col A C D -> 平行四边形 A B C D -> 严格平行 A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol134_plg__plgs; auto.
Qed.

Lemma ncol234_plg__pars1423 : forall A B C D,
  ~ Col B C D -> 平行四边形 A B C D -> 严格平行 A D B C.
Proof.
intros; apply plgs_pars_2; apply ncol234_plg__plgs; auto.
Qed.

Lemma sac_plg : forall A B C D, 萨凯里四边形 A B C D -> 平行四边形 A B C D.
Proof.
intros A B C D H.
assert (T:=sac__pars1234 A B C D H).
assert (U:=sac__par1423 A B C D H).
assert (V:=sac__par1234 A B C D H).
apply par_2_plg;eauto using par_strict_not_col_1.
Qed.

Lemma sac_rectangle : forall A B C D, 萨凯里四边形 A B C D -> 长方形 A B C D.
Proof.
intros A B C D H.
assert (平行四边形 A B C D) by (apply sac_plg;auto).
apply parallelogram_to_plg in H0.
apply plg_per_rect1.
assumption.
unfold 萨凯里四边形 in H.
分离合取式; Perp.
Qed.

Lemma exists_square : forall A B, A<>B -> exists C D,  正方形 A B C D.
Proof.
intros.
destruct (exists_cong_per A B A B) as [C [HC1 HC2]].
统计不重合点.
destruct (per__ex_saccheri B C A) as [D HSac]; Perp.
exists C.
exists D.
assert (长方形 B C D A) by (apply sac_rectangle;auto).
unfold 正方形;split.
eauto using rect_permut.
Cong.
Qed.

End Quadrilateral_inter_dec_3.

Section Quadrilateral_inter_dec_2D.

Context `{T2D:Tarski_2D}.
Context `{TE:@塔斯基公理系统_欧几里得几何 Tn TnEQD}.

Lemma perp3__perp :
 forall A B C D,
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  Perp D A A B.
Proof.
intros A B C D.
apply cop_perp3__perp, all_coplanar.
Qed.

Lemma perp3__rect :
 forall A B C D,
  Perp A B B C ->
  Perp B C C D ->
  Perp C D D A ->
  长方形 A B C D.
Proof.
intros A B C D.
apply cop_perp3__rect, all_coplanar.
Qed.

End Quadrilateral_inter_dec_2D.