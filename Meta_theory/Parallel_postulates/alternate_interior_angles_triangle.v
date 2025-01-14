Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section alternate_interior_angles_postulate_triangle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma alternate_interior__triangle :
  alternate_interior_angles_postulate ->
  triangle_postulate.
Proof.
intros AIA A B C D E F HTrisuma.
elim (共线的决定性 A B C); [intro; apply (退化三角形的内角和为平角 A B C); auto|intro HNCol].
destruct(给定角一边可作出与给定点异侧一点构成等角_非平角 B C A C B A) as [B1 [HConga HTS]]; Col.
assert (HPar : Par A C B B1)
  by (apply par_left_comm, par_symmetry, l12_21_b; Side; 等角).
apply (par_not_col_strict _ _ _ _ B) in HPar; Col.
assert (HNCol1 : ~ Col C B B1) by (apply (par_not_col A C); Col).
assert (HNCol2 : ~ Col A B B1) by (apply (par_not_col A C); Col).
destruct (构造对称点 B1 B) as [B2 [HBet HCong]]; 统计不重合点.
assert (HTS1 : TS B A B1 B2)
  by (repeat split; Col; [intro; apply HNCol2; ColR|exists B; Col]).
assert (HTS2 : TS B A C B2)
  by (apply (l9_8_2 _ _ B1); auto; apply os_ts1324__os; Side).
apply (零角的等角是零角 B1 B B2); auto.
destruct HTrisuma as [D1 [E1 [F1 []]]].
apply (和角的唯一性 D1 E1 F1 C A B); auto.
assert (等角 A B B2 C A B).
  {
  apply 等角的左交换性, AIA; Side.
  apply par_symmetry, (par_col_par _ _ _ B1); Col; Par.
  }
apply (等角保持和角性质 B1 B A A B B2 B1 B B2); try (apply 同角相等); auto;
[exists B2; repeat (split; 等角); Cop; apply l9_9; auto|].
apply (和角的唯一性 A B C B C A); auto.
apply (等角保持和角性质 A B C C B B1 A B B1); 等角.
exists B1; repeat (split; 等角); Cop; apply l9_9; Side.
Qed.

End alternate_interior_angles_postulate_triangle.