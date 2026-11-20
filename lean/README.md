# Andrews 分拆不等式的 Lean 核验

本工程对应上传稿《A complete proof of a conjecture of Andrews》。原稿 SHA-256 为 `fc0ae09e569459886c2a567c1e656ce6b6abffdbd173f2f8dfd7807a51c7934a`。环境为 Lean 4.19.0 和 mathlib v4.19.0。

## 主定理

`LeanAndrews.Unconditional.andrews_from_four` 的输入只有自然数 `d,n` 及两条范围条件 `4 ≤ d` 和 `1 ≤ n`。它同时给出

$$
Q_d^*(n)\le q_d^*(n),\qquad
q_d^*(n)=Q_d^*(n)\quad\Longleftrightarrow\quad
n\le d+3\ \text{或}\ (d,n)=(4,12).
$$

`LeanAndrews.Unconditional.strengthened` 给出同一范围中 $n\ne d+2$ 时的 $Q_d^*(n)\le h_{d+1}(n)$，并证明例外权重处的三个计数依次为 $h=1,q=2,Q=2$。

`LeanAndrews.Unconditional.andrews` 从 $d\ge2$ 开始。唯一的文献前提 `LeanAndrews.ClassicalIdentities` 表示 $d=2,3$ 时的 Göllnitz–Gordon 和 Schur 等式。两个经典情形的剩余类已在 `CountBasics.lean` 中分别化为模 8 的 1、4、7 和模 6 的 1、5。上述三个最终定理均没有欧拉五边形数递推前提。

## 原稿到证明文件的对照

| 原稿中的推论或计算 | 对应的 Lean 结果 |
|---|---|
| 分拆计数的定义 | `Small.mem_partitions`、`Small.partitions_nodup` 证明降序正整数列表完整、无重复。`CountBasics.originalGapOK_iff` 将相邻部件的检验转换成对所有部件对的差分条件。这里的 `Small` 全名为 `Andrews.Small`。 |
| 引言里与 Inagaki–Tamura 比较的推导 | `Historical.ordered_parts_comparison` 证明替换部件并用 1 补足总重量的单射。`prior_large_range` 和 `prior_bounded_range` 分别显式假设引用的那条文献结论。主定理未调用这两条历史推论。 |
| 引理 2.1，剩余类计数的统一上界 | `UpperBridge.upper_count` 给出 $Q_d^*(dm+r)\le P(m)$，其中 $P(m)=\sum_{i=0}^m p(i)$。 |
| 阶梯展开、分拆共轭、引理 2.2 | `Lower.staircaseBijection`、`Lower.conjugation`、`CoinBridge.gapCount_eq_sum_cutoff`、`GapBridge.scaling`。最后一条给出原稿所需的跨参数计数不等式。 |
| 命题 3.1 的组合下界 | `Sorting.stars_hCount` 用排序置换和实际间距分拆编码有序弱组合，并控制重数。`Analytic.power_bound_of_stars` 导出幂次下界。 |
| 命题 3.1 的解析估计 | `FiniteEuler.cumulative_log` 给出普通分拆累计数的对数上界。`EulerIntegral.logKernel_integral`、`EulerIntegral.logKernel_riemann_le`、`Analytic.factorial_from_unit_trapezoids` 核验原稿的积分与梯形估计。`NumericalSteps.lean` 核验文中的截断级数、常数和导数。`LeanAndrews.largeComparison` 对所有 $m\ge65536$ 得到严格不等式。 |
| 表 1 的八行、最小值、首次取到的位置及全部零点 | `Unconditional.entries` 将整张表陈述为关于实际分拆数的命题。`VerifiedTable`、`GapTable`、`ResidueTable`、`CoinBridge` 将数组项接到分拆定义。 |
| 小权重与六个特殊权重 | `Small.small_counts` 覆盖所有 $4\le d,1\le n<2d$。`CountBasics.sixWeights` 与 `Witnesses.lean` 同时核验六个权重、五个具体见证和 $d=4,n=12$ 的两份完整分拆清单。 |
| 定理 1.1、1.2 的整参数合并 | `Reduction.lean` 完成商与余数的分区。`Unconditional.lean` 将各个分区的证明代入，并导出文首三个定理。 |

除 `Andrews.Small` 外，表中省略的根命名空间为 `LeanAndrews`。

## 有限计算与信任范围

工程有两条有限验证路线。`LinkedFinite.lean` 按原稿以经典欧拉五边形数递推为显式输入，逐项核实八行。`Unconditional.lean` 对同一张表给出第二份证明。它在 $m<7000$ 用受限分拆的递推计算 $P(m)$，在 $7000\le m<65536$ 已有
$$
P(m)\le 2^{\lfloor\sqrt{14m}\rfloor+1}< h_5(4m)-22\,332\,733.
$$
因此大区间后段不可能出现更小或并列的最小值。两个区间接上后，第一行的最小值为 22,332,733，首个达到点为 100。

大规模有限比较使用 Lean 的 `native_decide`，公理报告中相应出现 `Lean.ofReduceBool`。这些比较信任 Lean 的原生编译与执行。组合单射、全部参数范围的推导和解析估计均以 Lean 证明项给出。`verify/axioms.txt` 保留了最终定理的类型及实际公理输出，六个特殊权重和具体分拆清单可以直接由内核归约。

我们还直接运行了上传稿附录中的 Python 代码，八行输出见 `verify/appendix-output.txt`。Lean 对表中数学命题作了独立验证。Python 程序与 Lean 程序之间的逐行等价性不属于此项核验。部分步骤采用等价证明，例如引理 2.2 直接构造分拆之间的单射。

## 复现

在安装 elan 并解压后，从含有 `lakefile.toml` 的目录执行

```sh
lake update
lake exe cache get
lake build
lake env lean verify/Check.lean
```

首次获取依赖需要联网。最后两条命令分别构建证明工程、列出定理和所用公理。另可用 `lake env lean --run FiniteMain.lean` 单独打印原稿表 1 的八行数据。随包的 `verify/table.txt` 为 Lean 程序的八行输出，`verify/build.txt` 为项目构建记录。本次构建使用本地缓存的同版本 mathlib。发布配置按标签从 Git 获取依赖。
