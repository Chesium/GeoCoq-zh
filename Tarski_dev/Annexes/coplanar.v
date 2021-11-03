Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

Section 共面.

Context `{Tn:无维度中性塔斯基公理系统}.

Lemma coplanar_perm_1 : forall A B C D,
  共面 A B C D -> 共面 A B D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_2 : forall A B C D,
  共面 A B C D -> 共面 A C B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_3 : forall A B C D,
  共面 A B C D -> 共面 A C D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_4 : forall A B C D,
  共面 A B C D -> 共面 A D B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_5 : forall A B C D,
  共面 A B C D -> 共面 A D C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_6 : forall A B C D,
  共面 A B C D -> 共面 B A C D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_7 : forall A B C D,
  共面 A B C D -> 共面 B A D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_8 : forall A B C D,
  共面 A B C D -> 共面 B C A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_9 : forall A B C D,
  共面 A B C D -> 共面 B C D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_10 : forall A B C D,
  共面 A B C D -> 共面 B D A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_11 : forall A B C D,
  共面 A B C D -> 共面 B D C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_12 : forall A B C D,
  共面 A B C D -> 共面 C A B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_13 : forall A B C D,
  共面 A B C D -> 共面 C A D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_14 : forall A B C D,
  共面 A B C D -> 共面 C B A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_15 : forall A B C D,
  共面 A B C D -> 共面 C B D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_16 : forall A B C D,
  共面 A B C D -> 共面 C D A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_17 : forall A B C D,
  共面 A B C D -> 共面 C D B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_18 : forall A B C D,
  共面 A B C D -> 共面 D A B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_19 : forall A B C D,
  共面 A B C D -> 共面 D A C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_20 : forall A B C D,
  共面 A B C D -> 共面 D B A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_21 : forall A B C D,
  共面 A B C D -> 共面 D B C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_22 : forall A B C D,
  共面 A B C D -> 共面 D C A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_23 : forall A B C D,
  共面 A B C D -> 共面 D C B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma ncoplanar_perm_1 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A B D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_1, HCop.
Qed.

Lemma ncoplanar_perm_2 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A C B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_2, HCop.
Qed.

Lemma ncoplanar_perm_3 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A C D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_4, HCop.
Qed.

Lemma ncoplanar_perm_4 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A D B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_3, HCop.
Qed.

Lemma ncoplanar_perm_5 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A D C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_5, HCop.
Qed.

Lemma ncoplanar_perm_6 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B A C D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_6, HCop.
Qed.

Lemma ncoplanar_perm_7 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B A D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_7, HCop.
Qed.

Lemma ncoplanar_perm_8 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B C A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_12, HCop.
Qed.

Lemma ncoplanar_perm_9 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B C D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_18, HCop.
Qed.

Lemma ncoplanar_perm_10 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B D A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_13, HCop.
Qed.

Lemma ncoplanar_perm_11 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B D C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_19, HCop.
Qed.

Lemma ncoplanar_perm_12 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C A B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_8, HCop.
Qed.

Lemma ncoplanar_perm_13 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C A D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_10, HCop.
Qed.

Lemma ncoplanar_perm_14 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C B A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_14, HCop.
Qed.

Lemma ncoplanar_perm_15 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C B D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_20, HCop.
Qed.

Lemma ncoplanar_perm_16 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C D A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_16, HCop.
Qed.

Lemma ncoplanar_perm_17 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C D B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_22, HCop.
Qed.

Lemma ncoplanar_perm_18 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D A B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_9, HCop.
Qed.

Lemma ncoplanar_perm_19 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D A C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_11, HCop.
Qed.

Lemma ncoplanar_perm_20 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D B A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_15, HCop.
Qed.

Lemma ncoplanar_perm_21 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D B C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_21, HCop.
Qed.

Lemma ncoplanar_perm_22 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D C A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_17, HCop.
Qed.

Lemma ncoplanar_perm_23 : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D C B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply coplanar_perm_23, HCop.
Qed.

Lemma coplanar_trivial : forall A B C, 共面 A A B C.
Proof.
intros.
exists B; Col5.
Qed.

Lemma col__coplanar : forall A B C D,
  Col A B C -> 共面 A B C D.
Proof.
intros.
exists C; Col5.
Qed.

Lemma ncop__ncol : forall A B C D,
  ~ 共面 A B C D -> ~ Col A B C.
Proof.
intros.
intro.
apply H, col__coplanar, H0.
Qed.

Lemma ncop__ncols : forall A B C D,
  ~ 共面 A B C D -> ~ Col A B C /\ ~ Col A B D /\ ~ Col A C D /\ ~ Col B C D.
Proof.
intros; repeat split.
apply ncop__ncol with D, H.
apply ncop__ncol with C, ncoplanar_perm_1, H.
apply ncop__ncol with B, ncoplanar_perm_3, H.
apply ncop__ncol with A, ncoplanar_perm_9, H.
Qed.

Lemma bet__coplanar : forall A B C D,
  Bet A B C -> 共面 A B C D.
Proof.
intros.
apply col__coplanar; Col.
Qed.

Lemma out__coplanar : forall A B C D,
  Out A B C -> 共面 A B C D.
Proof.
intros.
apply col__coplanar; Col.
Qed.

Lemma midpoint__coplanar : forall A B C D,
  中点 A B C -> 共面 A B C D.
Proof.
intros A B C D [].
apply col__coplanar; Col.
Qed.

Lemma perp__coplanar : forall A B C D,
  Perp A B C D -> 共面 A B C D.
Proof.
intros A B C D [P HP].
unfold 垂直于 in HP; spliter.
exists P; left; Col.
Qed.

Lemma ts__coplanar : forall A B C D,
  TS A B C D -> 共面 A B C D.
Proof.
intros A B C D [_ [_ [X []]]].
exists X; left; split; Col.
Qed.

Lemma reflectl__coplanar : forall A B C D,
  严格对称 A B C D -> 共面 A B C D.
Proof.
intros A B C D [[X [[] HCol]] _].
exists X.
left; split; Col.
Qed.

Lemma reflect__coplanar : forall A B C D,
  对称 A B C D -> 共面 A B C D.
Proof.
intros A B C D [[_ HR]|[Heq]].
  apply reflectl__coplanar, HR.
subst; apply coplanar_perm_16, coplanar_trivial.
Qed.

Lemma inangle__coplanar : forall A B C D,
  在角内 A B C D -> 共面 A B C D.
Proof.
intros A B C D H.
unfold 在角内 in H; spliter.
destruct H2 as [X [HBet Dij]].
exists X; right; left.
split; Col.
induction Dij; [subst|]; Col.
Qed.

Lemma pars__coplanar : forall A B C D,
  严格平行 A B C D -> 共面 A B C D.
Proof.
  unfold 严格平行; intros; spliter; assumption.
Qed.

Lemma par__coplanar : forall A B C D,
  Par A B C D -> 共面 A B C D.
Proof.
  intros A B C D H.
  destruct H.
    apply pars__coplanar; assumption.
  spliter; exists A; left; Col.
Qed.

Lemma plg__coplanar : forall A B C D,
  Plg A B C D -> 共面 A B C D.
Proof.
  intros A B C D [H [M [[H1 _] [H2 _]]]].
  exists M; right; left; split; Col.
Qed.

Lemma plgs__coplanar : forall A B C D,
  严格平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [_ [HPar _]].
  apply par__coplanar, HPar.
Qed.

Lemma plgf__coplanar : forall A B C D,
  退化平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [HCol _].
  apply col__coplanar, HCol.
Qed.

Lemma parallelogram__coplanar : forall A B C D,
  平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [Hs|Hf].
    apply plgs__coplanar, Hs.
    apply plgf__coplanar, Hf.
Qed.

Lemma rhombus__coplanar : forall A B C D,
  菱形 A B C D -> 共面 A B C D.
Proof.
  unfold 菱形.
  intros; spliter; apply plg__coplanar; assumption.
Qed.

Lemma rectangle__coplanar : forall A B C D,
  长方形 A B C D -> 共面 A B C D.
Proof.
  unfold 长方形.
  intros; spliter; apply plg__coplanar; assumption.
Qed.

Lemma square__coplanar : forall A B C D,
  正方形 A B C D -> 共面 A B C D.
Proof.
  unfold 正方形.
  intros; spliter; apply rectangle__coplanar; assumption.
Qed.

Lemma lambert__coplanar : forall A B C D,
  Lambert四边形 A B C D -> 共面 A B C D.
Proof.
  unfold Lambert四边形.
  intros; spliter; assumption.
Qed.

End 共面.

Hint Resolve coplanar_perm_1 coplanar_perm_2 coplanar_perm_3 coplanar_perm_4 coplanar_perm_5
coplanar_perm_6 coplanar_perm_7 coplanar_perm_8 coplanar_perm_9 coplanar_perm_10 coplanar_perm_11
coplanar_perm_12 coplanar_perm_13 coplanar_perm_14 coplanar_perm_15 coplanar_perm_16 coplanar_perm_17
coplanar_perm_18 coplanar_perm_19 coplanar_perm_20 coplanar_perm_21 coplanar_perm_22 coplanar_perm_23
ncoplanar_perm_1 ncoplanar_perm_2 ncoplanar_perm_3 ncoplanar_perm_4 ncoplanar_perm_5 ncoplanar_perm_6
ncoplanar_perm_7 ncoplanar_perm_8 ncoplanar_perm_9 ncoplanar_perm_10 ncoplanar_perm_11
ncoplanar_perm_12 ncoplanar_perm_13 ncoplanar_perm_14 ncoplanar_perm_15 ncoplanar_perm_16
ncoplanar_perm_17 ncoplanar_perm_18 ncoplanar_perm_19 ncoplanar_perm_20 ncoplanar_perm_21
ncoplanar_perm_22 ncoplanar_perm_23 : cop_perm.

Hint Resolve coplanar_trivial col__coplanar bet__coplanar out__coplanar midpoint__coplanar
perp__coplanar ts__coplanar reflectl__coplanar reflect__coplanar inangle__coplanar pars__coplanar
par__coplanar plg__coplanar plgs__coplanar plgf__coplanar parallelogram__coplanar rhombus__coplanar
rectangle__coplanar square__coplanar lambert__coplanar : cop.

Ltac not_exist_hyp_perm_cop_aux A B C D :=
  not_exist_hyp (共面 A B C D); not_exist_hyp (共面 A B D C); not_exist_hyp (共面 A C B D);
  not_exist_hyp (共面 A C D B); not_exist_hyp (共面 A D B C); not_exist_hyp (共面 A D C B).

Ltac not_exist_hyp_perm_cop A B C D := not_exist_hyp_perm_cop_aux A B C D;
                                       not_exist_hyp_perm_cop_aux B A C D;
                                       not_exist_hyp_perm_cop_aux C A B D;
                                       not_exist_hyp_perm_cop_aux D A B C.

Ltac assert_cops :=
 repeat match goal with
      | H:Perp ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply perp__coplanar, H)
      | H:TS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply ts__coplanar, H)
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
      | H:Lambert四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply lambert__coplanar, H)
 end.

Ltac exist_hyp_perm_cop_aux A B C D := first
  [exist_hyp (共面 A B C D)|exist_hyp (共面 A B D C)|exist_hyp (共面 A C B D)
  |exist_hyp (共面 A C D B)|exist_hyp (共面 A D B C)|exist_hyp (共面 A D C B)].

Ltac exist_hyp_perm_cop A B C D := first
  [exist_hyp_perm_cop_aux A B C D|exist_hyp_perm_cop_aux B A C D
  |exist_hyp_perm_cop_aux C A B D|exist_hyp_perm_cop_aux D A B C].

Ltac exist_hyp_perm_ncop_aux A B C D := first
  [exist_hyp (~ 共面 A B C D)|exist_hyp (~ 共面 A B D C)|exist_hyp (~ 共面 A C B D)
  |exist_hyp (~ 共面 A C D B)|exist_hyp (~ 共面 A D B C)|exist_hyp (~ 共面 A D C B)].

Ltac exist_hyp_perm_ncop A B C D := first
  [exist_hyp_perm_ncop_aux A B C D|exist_hyp_perm_ncop_aux B A C D
  |exist_hyp_perm_ncop_aux C A B D|exist_hyp_perm_ncop_aux D A B C].

Ltac Cop := auto; try (intros; solve [apply col__coplanar; Col
     |apply coplanar_perm_1, col__coplanar; Col|apply coplanar_perm_4, col__coplanar; Col
     |apply coplanar_perm_18, col__coplanar; Col
     |assert_cops; auto 2 with cop_perm]).