# GeoCoq-zh
Coq 中的几何形式化
翻译自 [GeoCoq](https://github.com/GeoCoq/GeoCoq)

翻译完成度用这四个图标表示：![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png) ![25%](https://upload.wikimedia.org/wikipedia/commons/thumb/c/ce/25_percent.svg/14px-25_percent.svg.png) ![50%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/50_percents.svg/14px-50_percents.svg.png) ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png) ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)，这与 <img src="https://en.wikibooks.org/favicon.ico" height=20/>[Wikiboook](https://en.wikibooks.org/wiki/Help:Development_stages) 相同

标星号的为尚未获得良好翻译的词条
## 任务：
### 公理：`/Axioms`
- **`Michael\ Beeson` 的公理系统** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/beeson\_s\_axioms.v`
- **连续性公理** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/continuity\_axioms.v`
- **欧几里得公理** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/euclidean\_axioms.v`
- **塔斯基公理系统 `Gupta` 变种** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/gupta\_inspired\_variant\_axioms.v`
- **希尔伯特公理系统** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/hilbert\_axioms.v`
- **塔斯基公理系统 `Makarios` 变种** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/makarios\_variant\_axioms.v`
- **平行公设** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Axioms/parallel\_postulates.v`
- **塔斯基公理系统** ![100](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Axioms/tarski\_axioms.v`
  
### 《几何原本》：`/Elements` ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)
暂时不翻译

### 中学几何：`/Highschool` ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)
- **角平分线** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Highschool/bisector.v`

  引理数：7

- **三角形外心** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/circumcenter.v`

  引理数：16

- **共圆** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/concyclic.v`

  引理数：26

- **欧拉线（三角形重心垂心外心三点共线）** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Highschool/Euler_line.v`

  引理数：5

- **一些练习** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/exercises.v`

  引理数：2

- **三角形重心** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/gravityCenter.v`

  引理数：18

- **三角形内心** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/incenter.v`

  引理数：7

- **泰勒斯定理（直径所对圆周角为直角）** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/midpoint_thales.v`

  引理数：2

- **`Orientation`*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Highschool/orientation.v`

  引理数：61

- **三角形垂心** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Highschool/orthocenter.v`

  引理数：16

- **`Sesamath` 中学几何练习示例** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Highschool/sesamath\_exercises.v`

  引理数：12

- **三角形** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/triangles.v`

  引理数：25

- **瓦里尼翁平行四边形** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Highschool/varignon.v`

  引理数：4


### 元理论：`/Meta\_theory` ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)
暂时不翻译

### 附加策略：`/Tactics` ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)
暂时不翻译

### 塔斯基几何：`/Tarski\_dev`
- **定义** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Tarski\_dev/Definitions.v`

  引理数：

- **第二章：等长** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Tarski\_dev/Ch02\_cong.v`

  引理数：34

- **第三章：中间线** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Tarski\_dev/Ch03\_bet.v`

  引理数：29

- **第四章：共线** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Tarski\_dev/Ch04\_col.v`

  引理数：25

- **第四章：等长与中间性** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch04\_cong\_bet.v`

  引理数：6

- **第五章：中间性和偏序*** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Tarski\_dev/Ch05\_bet\_le.v`

  引理数：66

- **第六章：`out` 谓词*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch06\_out\_lines.v`

  引理数：54

- **第七章：中点** ![75%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/62/75_percent.svg/14px-75_percent.svg.png)

  `/Tarski\_dev/Ch07\_midpoint.v`

  引理数：55

- **第八章：垂直** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Tarski\_dev/Ch08\_orthogonality.v`

  引理数：94

- **第九章：平面** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch09\_plane.v`

  引理数：111

- **第十章：线的自反性1*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch10\_line\_reflexivity.v`

  引理数：41

- **第十章：线的自反性2*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch10\_line\_reflexivity\_2.v`

  引理数：31

- **第十一章：角** ![25%](https://upload.wikimedia.org/wikipedia/commons/thumb/c/ce/25_percent.svg/14px-25_percent.svg.png)

  `/Tarski\_dev/Ch11\_angles.v`

  引理数：278

- **第十二章：平行** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch12\_parallel.v`

  引理数：84

- **第十二章：平行的内部决定性*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch12\_parallel\_inter\_dec.v`

  引理数：30

- **第十三章：1.概述** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_1.v`

  引理数：38

- **第十三章：2.长度** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_2\_length.v`

  引理数：22

- **第十三章：3.角度** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_3\_angles.v`

  引理数：66

- **第十三章：4.余弦** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_4\_cos.v`

  引理数：61

- **第十三章：5.帕普斯-帕斯卡定理** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_5\_Pappus_Pascal.v`

  引理数：16

- **第十三章：6.笛卡尔-海森堡定理** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch13\_6\_Desargues_Hessenberg.v`

  引理数：12

- **第十四章：1.序*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch14\_order.v`

  引理数：36

- **第十四章：2.`Prod` 谓词*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch14\_prod.v`

  引理数：37

- **第十四章：3.`Sum` 谓词*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch14\_sum.v`

  引理数：95

- **第十五章：1.长度*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch15\_lengths.v`

  引理数：79

- **第十五章：2.`PythRel` 谓词*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch15\_pyth_rel.v`

  引理数：5

- **第十六章：1.坐标** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch16\_coordinates.v`

  引理数：27

- **第十六章：2.坐标与函数*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Ch16\_coordinates\_with\_functions.v`

  引理数：96



#### 附加部分：`/Tarski\_dev/Annexes`
- **圆** ![25%](https://upload.wikimedia.org/wikipedia/commons/thumb/c/ce/25_percent.svg/14px-25_percent.svg.png)

  `/Tarski\_dev/Annexes/circles.v`

  引理数：104

- **共面** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/coplanar.v`

  引理数：68

- **三角形内角和与平角之差（`defect`）** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/defect.v`

  引理数：18

- **半角** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/half\_angles.v`

  引理数：50

- **圆周角*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/inscribed\_angle.v`

  引理数：33

- **中点定理*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/midpoint\_theorems.v`

  引理数：22

- **中垂线** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/perp\_bisect.v`

  引理数：17

- **投影*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/project.v`

  引理数：42

- **四边形内部决定性*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/quadrilaterals\_inter\_dec.v`

  引理数：105

- **四边形** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/quadrilaterals.v`

  引理数：79

- **菱形** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/rhombus.v`

  引理数：11

- **萨凯里四边形** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/saccheri.v`

  引理数：95

- **角度之和** ![100%](https://upload.wikimedia.org/wikipedia/commons/thumb/2/24/100_percent.svg/14px-100_percent.svg.png)

  `/Tarski\_dev/Annexes/suma.v`

  引理数：108

- **长度之和** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/sums.v`

  引理数：39

- **标记谓词*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/Tagged\_predicates.v`

  引理数：25

- **相切*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/tangency.v`

  引理数：15

- **向量*** ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)

  `/Tarski\_dev/Annexes/vectors.v`

  引理数：52


#### 附加策略：`/Tarski\_dev/Tactics` ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)
暂时不翻译

### `Utils` 文件夹：`/Utils` ![0%](https://upload.wikimedia.org/wikipedia/commons/thumb/6/60/00_percent.svg/14px-00_percent.svg.png)
暂时不翻译