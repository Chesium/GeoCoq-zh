Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

Section 共面.

Context `{Tn:无维度中性塔斯基公理系统}.

Lemma 等价共面ABDC : forall A B C D,
  共面 A B C D -> 共面 A B D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面ACBD : forall A B C D,
  共面 A B C D -> 共面 A C B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面ACDB : forall A B C D,
  共面 A B C D -> 共面 A C D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面ADBC : forall A B C D,
  共面 A B C D -> 共面 A D B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面ADCB : forall A B C D,
  共面 A B C D -> 共面 A D C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BACD : forall A B C D,
  共面 A B C D -> 共面 B A C D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BADC : forall A B C D,
  共面 A B C D -> 共面 B A D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BCAD : forall A B C D,
  共面 A B C D -> 共面 B C A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BCDA : forall A B C D,
  共面 A B C D -> 共面 B C D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BDAC : forall A B C D,
  共面 A B C D -> 共面 B D A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面BDCA : forall A B C D,
  共面 A B C D -> 共面 B D C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CABD : forall A B C D,
  共面 A B C D -> 共面 C A B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CADB : forall A B C D,
  共面 A B C D -> 共面 C A D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CBAD : forall A B C D,
  共面 A B C D -> 共面 C B A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CBDA : forall A B C D,
  共面 A B C D -> 共面 C B D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CDAB : forall A B C D,
  共面 A B C D -> 共面 C D A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面CDBA : forall A B C D,
  共面 A B C D -> 共面 C D B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DABC : forall A B C D,
  共面 A B C D -> 共面 D A B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DACB : forall A B C D,
  共面 A B C D -> 共面 D A C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DBAC : forall A B C D,
  共面 A B C D -> 共面 D B A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DBCA : forall A B C D,
  共面 A B C D -> 共面 D B C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DCAB : forall A B C D,
  共面 A B C D -> 共面 D C A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面DCBA : forall A B C D,
  共面 A B C D -> 共面 D C B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); 分离合取式; Col5.
Qed.

Lemma 等价共面否定ABDC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A B D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面ABDC, HCop.
Qed.

Lemma 等价共面否定ACBD : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A C B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面ACBD, HCop.
Qed.

Lemma 等价共面否定ACDB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A C D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面ADBC, HCop.
Qed.

Lemma 等价共面否定ADBC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A D B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面ACDB, HCop.
Qed.

Lemma 等价共面否定ADCB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 A D C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面ADCB, HCop.
Qed.

Lemma 等价共面否定BACD : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B A C D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BACD, HCop.
Qed.

Lemma 等价共面否定BADC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B A D C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BADC, HCop.
Qed.

Lemma 等价共面否定BCAD : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B C A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CABD, HCop.
Qed.

Lemma 等价共面否定BCDA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B C D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DABC, HCop.
Qed.

Lemma 等价共面否定BDAC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B D A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CADB, HCop.
Qed.

Lemma 等价共面否定BDCA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 B D C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DACB, HCop.
Qed.

Lemma 等价共面否定CABD : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C A B D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BCAD, HCop.
Qed.

Lemma 等价共面否定CADB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C A D B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BDAC, HCop.
Qed.

Lemma 等价共面否定CBAD : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C B A D.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CBAD, HCop.
Qed.

Lemma 等价共面否定CBDA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C B D A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DBAC, HCop.
Qed.

Lemma 等价共面否定CDAB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C D A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CDAB, HCop.
Qed.

Lemma 等价共面否定CDBA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 C D B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DCAB, HCop.
Qed.

Lemma 等价共面否定DABC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D A B C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BCDA, HCop.
Qed.

Lemma 等价共面否定DACB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D A C B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面BDCA, HCop.
Qed.

Lemma 等价共面否定DBAC : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D B A C.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CBDA, HCop.
Qed.

Lemma 等价共面否定DBCA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D B C A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DBCA, HCop.
Qed.

Lemma 等价共面否定DCAB : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D C A B.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面CDBA, HCop.
Qed.

Lemma 等价共面否定DCBA : forall A B C D,
  ~ 共面 A B C D -> ~ 共面 D C B A.
Proof.
intros A B C D HNCop HCop; apply HNCop.
apply 等价共面DCBA, HCop.
Qed.

Lemma AABC共面 : forall A B C, 共面 A A B C.
Proof.
intros.
exists B; Col5.
Qed.

Lemma 共线三点和任一点共面 : forall A B C D,
  Col A B C -> 共面 A B C D.
Proof.
intros.
exists C; Col5.
Qed.

Lemma 四点不共面则前三点不共线 : forall A B C D,
  ~ 共面 A B C D -> ~ Col A B C.
Proof.
intros.
intro.
apply H, 共线三点和任一点共面, H0.
Qed.

Lemma 四点不共面则任三点不共线 : forall A B C D,
  ~ 共面 A B C D -> ~ Col A B C /\ ~ Col A B D /\ ~ Col A C D /\ ~ Col B C D.
Proof.
intros; repeat split.
apply 四点不共面则前三点不共线 with D, H.
apply 四点不共面则前三点不共线 with C, 等价共面否定ABDC, H.
apply 四点不共面则前三点不共线 with B, 等价共面否定ACDB, H.
apply 四点不共面则前三点不共线 with A, 等价共面否定BCDA, H.
Qed.

Lemma 成中间性三点和任一点共面 : forall A B C D,
  Bet A B C -> 共面 A B C D.
Proof.
intros.
apply 共线三点和任一点共面; Col.
Qed.

Lemma 外共线三点和任一点共面 : forall A B C D,
  Out A B C -> 共面 A B C D.
Proof.
intros.
apply 共线三点和任一点共面; Col.
Qed.

Lemma 中点组三点和任一点共面 : forall A B C D,
  中点 A B C -> 共面 A B C D.
Proof.
intros A B C D [].
apply 共线三点和任一点共面; Col.
Qed.

Lemma 垂直蕴含共面 : forall A B C D,
  Perp A B C D -> 共面 A B C D.
Proof.
intros A B C D [P HP].
unfold 垂直于 in HP; 分离合取式.
exists P; left; Col.
Qed.

Lemma 异侧蕴含共面 : forall A B C D,
  TS A B C D -> 共面 A B C D.
Proof.
intros A B C D [_ [_ [X []]]].
exists X; left; split; Col.
Qed.

Lemma 严格对称蕴含共面 : forall A B C D,
  严格对称 A B C D -> 共面 A B C D.
Proof.
intros A B C D [[X [[] HCol]] _].
exists X.
left; split; Col.
Qed.

Lemma 对称蕴含共面 : forall A B C D,
  对称 A B C D -> 共面 A B C D.
Proof.
intros A B C D [[_ HR]|[Heq]].
  apply 严格对称蕴含共面, HR.
subst; apply 等价共面CDAB, AABC共面.
Qed.

Lemma 在角内蕴含共面 : forall A B C D,
  在角内 A B C D -> 共面 A B C D.
Proof.
intros A B C D H.
unfold 在角内 in H; 分离合取式.
destruct H2 as [X [HBet Dij]].
exists X; right; left.
split; Col.
induction Dij; [subst|]; Col.
Qed.

Lemma 严格平行蕴含共面 : forall A B C D,
  严格平行 A B C D -> 共面 A B C D.
Proof.
  unfold 严格平行; intros; 分离合取式; assumption.
Qed.

Lemma 平行蕴含共面 : forall A B C D,
  Par A B C D -> 共面 A B C D.
Proof.
  intros A B C D H.
  destruct H.
    apply 严格平行蕴含共面; assumption.
  分离合取式; exists A; left; Col.
Qed.

Lemma 平四蕴含共面 : forall A B C D,
  平四 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [H [M [[H1 _] [H2 _]]]].
  exists M; right; left; split; Col.
Qed.

Lemma 严格平行四边形蕴含共面 : forall A B C D,
  严格平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [_ [HPar _]].
  apply 平行蕴含共面, HPar.
Qed.

Lemma 退化平行四边形蕴含共面 : forall A B C D,
  退化平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [HCol _].
  apply 共线三点和任一点共面, HCol.
Qed.

Lemma 平行四边形蕴含共面 : forall A B C D,
  平行四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [Hs|Hf].
    apply 严格平行四边形蕴含共面, Hs.
    apply 退化平行四边形蕴含共面, Hf.
Qed.

Lemma 菱形蕴含共面 : forall A B C D,
  菱形 A B C D -> 共面 A B C D.
Proof.
  unfold 菱形.
  intros; 分离合取式; apply 平四蕴含共面; assumption.
Qed.

Lemma 长方形蕴含共面 : forall A B C D,
  长方形 A B C D -> 共面 A B C D.
Proof.
  unfold 长方形.
  intros; 分离合取式; apply 平四蕴含共面; assumption.
Qed.

Lemma 正方形蕴含共面 : forall A B C D,
  正方形 A B C D -> 共面 A B C D.
Proof.
  unfold 正方形.
  intros; 分离合取式; apply 长方形蕴含共面; assumption.
Qed.

Lemma Lambert四边形蕴含共面 : forall A B C D,
  Lambert四边形 A B C D -> 共面 A B C D.
Proof.
  unfold Lambert四边形.
  intros; 分离合取式; assumption.
Qed.

End 共面.

Hint Resolve 等价共面ABDC 等价共面ACBD 等价共面ACDB 等价共面ADBC 等价共面ADCB
等价共面BACD 等价共面BADC 等价共面BCAD 等价共面BCDA 等价共面BDAC 等价共面BDCA
等价共面CABD 等价共面CADB 等价共面CBAD 等价共面CBDA 等价共面CDAB 等价共面CDBA
等价共面DABC 等价共面DACB 等价共面DBAC 等价共面DBCA 等价共面DCAB 等价共面DCBA
等价共面否定ABDC 等价共面否定ACBD 等价共面否定ACDB 等价共面否定ADBC 等价共面否定ADCB 等价共面否定BACD
等价共面否定BADC 等价共面否定BCAD 等价共面否定BCDA 等价共面否定BDAC 等价共面否定BDCA
等价共面否定CABD 等价共面否定CADB 等价共面否定CBAD 等价共面否定CBDA 等价共面否定CDAB
等价共面否定CDBA 等价共面否定DABC 等价共面否定DACB 等价共面否定DBAC 等价共面否定DBCA
等价共面否定DCAB 等价共面否定DCBA : 共面的排列.

Hint Resolve AABC共面 共线三点和任一点共面 成中间性三点和任一点共面 外共线三点和任一点共面 中点组三点和任一点共面
垂直蕴含共面 异侧蕴含共面 严格对称蕴含共面 对称蕴含共面 在角内蕴含共面 严格平行蕴含共面
平行蕴含共面 平四蕴含共面 严格平行四边形蕴含共面 退化平行四边形蕴含共面 平行四边形蕴含共面 菱形蕴含共面
长方形蕴含共面 正方形蕴含共面 Lambert四边形蕴含共面 : cop.

Ltac not_exist_hyp_perm_cop_aux A B C D :=
  not_exist_hyp (共面 A B C D); not_exist_hyp (共面 A B D C); not_exist_hyp (共面 A C B D);
  not_exist_hyp (共面 A C D B); not_exist_hyp (共面 A D B C); not_exist_hyp (共面 A D C B).

Ltac not_exist_hyp_perm_cop A B C D := not_exist_hyp_perm_cop_aux A B C D;
                                       not_exist_hyp_perm_cop_aux B A C D;
                                       not_exist_hyp_perm_cop_aux C A B D;
                                       not_exist_hyp_perm_cop_aux D A B C.

Ltac 推导四点共面 :=
 repeat match goal with
      | H:Perp ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 垂直蕴含共面, H)
      | H:TS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 异侧蕴含共面, H)
      | H:严格对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 严格对称蕴含共面, H)
      | H:对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 对称蕴含共面, H)
      | H:在角内 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 在角内蕴含共面, H)
      | H:严格平行 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 严格平行蕴含共面, H)
      | H:Par ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 平行蕴含共面, H)
      | H:平四 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 平四蕴含共面, H)
      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 严格平行四边形蕴含共面, H)
      | H:退化平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 退化平行四边形蕴含共面, H)
      | H:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 平行四边形蕴含共面, H)
      | H:菱形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 菱形蕴含共面, H)
      | H:长方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 长方形蕴含共面, H)
      | H:正方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply 正方形蕴含共面, H)
      | H:Lambert四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply Lambert四边形蕴含共面, H)
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

Ltac Cop := auto; try (intros; solve [apply 共线三点和任一点共面; Col
     |apply 等价共面ABDC, 共线三点和任一点共面; Col|apply 等价共面ADBC, 共线三点和任一点共面; Col
     |apply 等价共面DABC, 共线三点和任一点共面; Col
     |推导四点共面; auto 2 with 共面的排列]).
