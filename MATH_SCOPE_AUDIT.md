# JSP-001006 / Erdős 1201：最终数学范围验收

状态：**FINAL SCOPE PASSED / LEAN KERNEL-CHECKED**。2026-10-01 已只读核对最终源码、完整目标构建的退出状态、两个独立展开入口及其四份公理依赖输出。完整目标构建、独立入口编译和官方 leanchecker 最终模块重放均自然退出 0。本文没有修改 proof 源，也没有额外运行 Lean。

验收版本为 Lean **4.33.0** 与固定 Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。原包指定 Lean 4.33.1；构建过程中明确调整为与固定依赖一致的 4.33.0，不能将本次成功称为原 4.33.1 工程已通过。兼容性、版本调整、全部失败和成功日志由构建报告保留。

最终 `build/reference_4_33_0/Erdos1201.lean` SHA256：

`B282388C18069BC400D527158CDD68CEEF9BDE9E1DB932EAAC02FC85A3EAD803`

独立 `verification/VerifyOriginalStatement.lean` SHA256：

`E8ECD9E09E4F347A6EE4137180BCCDE6ED13763BFB8AE6CC77A9BEBD1C741AE9`

本文行号按上述实际验收源码重新核对。原源码文件头的 `UNCOMPILED DRAFT` 是打包时的历史标记；当前验收状态以本文对应的真实日志和源码哈希为准。

## 完整目标及官方额外范围

对任意实数 \(\epsilon>0\)、\(\eta>0\)，存在一个固定自然数 \(k\)，使

\[
\liminf_{N\to\infty}\frac1N
\#\left\{0\le n<N:
P^+\!\left(\prod_{i=0}^{k}(n+i)\right)>n^{1-\epsilon}\right\}
\ge1-\eta.
\]

此处素因子最大值的 Lean 定义与固定 FormalConjectures 目标完全一样，是自然数集合 `sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k+1), (n+i)}`；liminf 的值域为 `EReal`。正乘积的非空素因子集合有上界，因而此定义给出最大素因子；零乘积的边界另见下文。

官方最终声明的 eta 未注类型，而在 `(1-eta:EReal)` 中推为 **EReal**。验收保持这个额外范围，包括 `eta = ⊤`，同时单独验证所有正实数 eta 的数学范围。没有仅将最终 eta 改为 ℝ 后冒称官方同型。

两个独立入口实际通过：

- `VerifyOriginalStatement.lean:8–18`：`audit_erdos1201_formalconjectures_statement`，显式 epsilon : ℝ、eta : EReal，将完整集合、全部连续乘积、`Nat.count`、自然数 `atTop` 和 `EReal` liminf 直接展开，证明为 `exact Erdos1201.erdos_1201`。
- 同文件 :20–32：`audit_erdos1201_original_statement`，显式 epsilon : ℝ、eta : ℝ，保留相同完整展开目标；:31–32 用 `(eta : EReal)` 与 `EReal.coe_pos.mpr heta` 从官方型定理获得全部实数范围。

这些展开入口没有加入未证明的数学假设，也没有把完整乘积改为正偏移子乘积。

## 量词、阈值与固定 k

| 要求 | 最终源码证据 | 验收结果 |
|---|---|---|
| epsilon 取遍正实数，数学 eta 取遍正实数，官方 eta 取遍正 EReal | `VerifyOriginalStatement.lean:9,21`；`Erdos1201.lean:95–117` | 两个独立全量词入口均实际通过。|
| k 先于环境 N 选择 | `Erdos1201.lean:65–68,79,95–99`；`DyadicDensity.lean:100–103,112` | 同一个 k 的 eventual 比例转成全部 N 的 liminf；k 没有随 N 或 n 变化。|
| 同一个 H 覆盖所有大 dyadic 尺度 | `DyadicBadWindows.lean:37–41,53–59` | H、J₀ 先选，随后对每个 j≥J₀ 证明；没有稀疏尺度量词替换。|
| 完整乘积含 n 本身及每个 n+i | `Erdos1201.lean:19–21`；独立入口 :14–16、:26–28 | `range(k+1)` 恰为 0,…,k。|
| 阈值依赖每个 n，指数为原 1−epsilon | 同一集合定义和两份独立展开入口 | 中间平滑 cutoff 仅服务证明；最终陈述没有用固定 cutoff 替代。|
| 自然数全前缀及其下密度 | `DyadicDensity.lean:73–97,100–133`；`Erdos1201.lean:65–92,114–117` | dyadic 结果转成任意前缀 eventual 下界，再转全部自然数 atTop 的 liminf。|

## 下密度与有限前缀误差

固定 Mathlib `Mathlib/Data/Nat/Count.lean:36–38,52–54` 的 `Nat.count P N` 计数 \([0,N)\) 中满足 P 的自然数。对 N>0，比值位于 [0,1]；目标是该比值嵌入 EReal 后的下极限。这里要求自然下密度下界，没有要求普通密度极限存在。

`DyadicDensity.lean:41–69` 累加各 dyadic annulus 的坏数上界，再由 :73–97 覆盖任意前缀，得到

\[
\#\{0\le n<N:\mathrm{bad}(n)\}
\le1+2^{J_0}+2\alpha N.
\]

其中因子 2 来自相邻 dyadic 前缀覆盖；额外 1 明确支付 n=0。:105–133 取 \(\alpha=\eta/4\)，并用 \((1+2^{J_0})/N\to0\) 得到同一个 H 的所有充分大 N 的好起点比例至少 \(1-\eta\)。不存在只给某个无穷子序列的比例。

最终 `Erdos1201.lean:71–92` 调用误差 \(\eta/2\) 的好起点比例，再支付目标集合转移中的 \(1/N<\eta/2\)，得到完整目标的实数 eventual 下界。:114–117 通过 `Filter.le_liminf_of_le (α := EReal)` 转成目标 liminf。固定 API 在 `Mathlib/Order/LiminfLimsup.lean:145–148`，命名参数 `h` 确为 eventual 下界；此应用已真实类型检查成功。

## n=0、N=0 与完整乘积桥接

中间 `goodStart` 在 `OriginalThreshold.lean:14–15` 要求 \(1\le j\le H\) 的见证素数 p 整除 n+j，并严格超过 n 的阈值。`Erdos1201.lean:27–46` 对 n>0 将这个见证转入完整乘积：:32–36 证明完整乘积 Q>0；:37–40 将见证位置放入 `range(H+1)` 并证明 p∣Q；:41–43 用素因子不超过 Q 得到 p≤sSup。完整乘积含 zeroth factor，不会丢掉正偏移因子的素数见证。

当 n=0 时，完整乘积为 0，所有素数都整除它，候选集合无上界。固定 Mathlib `Mathlib/Order/Lattice/Nat.lean:45–51` 的自然数 sSup 对这种集合取 0。证明没有在这里套用正乘积的有界性：`Erdos1201.lean:48–61` 明确给出

\[
\operatorname{count}(\mathrm{goodStart},N)
\le\operatorname{count}(\mathrm{target},N)+1.
\]

:53–60 将零点单独加入计数容许集合；:80–92 用 1/N→0 支付该单点误差。最终目标保留官方定义，没有人为删除 n=0。N=0 的除法值只影响一个有限前缀；eventual 证明 :80–83 同时要求 N≥1，atTop 的 liminf 不受这一点影响。

## 所有 epsilon>0 与 eta>0

中间整数 cutoff 的几何引理 `OriginalThreshold.lean:38–65` 直接处理 \(0<\epsilon\le1\)。最终 `Erdos1201.lean:71–76` 对任意原 epsilon>0 取

\[
\epsilon'=\min(\epsilon,1/2),\qquad
0<\epsilon'\le1/2,\quad\epsilon'\le\epsilon.
\]

对每个 n≥1，底数至少为 1，指数单调性给出

\[
n^{1-\epsilon}\le n^{1-\epsilon'}.
\]

`Erdos1201.lean:44–46` 正是这个转移：对较大阈值的严格素因子见证也严格超过原阈值。固定 `Real.rpow_le_rpow_of_exponent_le` 在 `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:615` 要求底数≥1；局部 `hn : 0<n` 是自然数命题，`exact_mod_cast hn` 在最终实际编译中成功提供该条件。epsilon>1 时原指数为负仍被同一比较覆盖；底数 n=0 已由单点误差处理。因此最终没有将 epsilon 缩为 (0,1] 或 (0,1/2]。

实数 eta 也没有上界限制。所有误差分配仅要求 eta>0，eta/2、eta/4 均为正，所以 eta≥1 同样被覆盖。

官方 EReal eta 的桥接在 `Erdos1201.lean:102–117` 实际通过：eta=top 时 :103–105 取 k=0，`EReal.sub_top` 将下界变为 bottom，直接由 `bot_le` 成立；eta≠top 时 :106–109 由 eta>0 排除 bottom，:110–111 用 `EReal.toReal_pos`、`EReal.coe_toReal` 恢复正实数 eta.toReal，:112 调用完整 Real eventual 定理，:114–117 把该实数不等式嵌入 EReal 并得到最终 liminf。没有新增有限性假设；top 分支也未被删除。

## 实际构建、公理输出与重放范围

| 实际检查 | 完整证据 | 结果 |
|---|---|---|
| `lake build JSP1006Proof` | `verification/repairs/build/021-full-final-ereal-order-explicit.log` 及同名 `-meta.json` | 自然退出 0，`Build completed successfully (9509 jobs)`；目标完整依赖闭包成功。构建过程使用记录的官方依赖缓存与已构建模块。|
| 双独立展开入口和四份 axioms 输出 | `verification/repairs/build/022-independent-expanded-statements-four-axioms.log` 及同名 `-meta.json` | 自然退出 0，官方 EReal eta 和数学 Real eta 两个完整目标均实际类型检查成功。|
| `lake env leanchecker --verbose Erdos1201` | `verification/repairs/build/023-official-leanchecker-final-module.log` 及同名 `-meta.json` | 自然退出 0；对最终 Erdos1201 模块声明进行官方 kernel 重放。|

022 日志实际输出四个定理的公理依赖，全部相同：

```text
'audit_erdos1201_formalconjectures_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_erdos1201_original_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1201.erdos_1201' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1201.erdos_1201_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
```

这四份输出没有 `sorryAx`、新增工程公理或未证明的数学假设接口。前面失败轮次中 elaborator 错误恢复显示的 sorry/sorryAx 不能算证明产物；本次结论只依据成功版本的实际输出。

023 的 replay 复用导入模块环境，没有启用 `--fresh`。官方 checker 会跳过 unsafe/partial 声明并允许 axiom 声明，因此应准确称为**最终模块重放成功**，而非所有 Mathlib 依赖均从零重新核查；它与完整目标构建及四份公理输出共同构成本次证据。

人工审读没有发现必须削弱原题才能弥补的数学缺口。此次实际修复保持证明链和完整范围，修复了命名空间、类型推断、强制转换、正规化、战术及最后的 EReal eta 桥接；详细 diff 和所有完整日志随工程保存。有限 13750 检查和静态无 sorry 扫描不是上述无穷目标成立的依据。公开优先权及奖项认定另由查新报告处理，不由本数学范围验收判定。
