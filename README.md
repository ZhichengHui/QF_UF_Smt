# QF_UF 求解器及其 AutoCorrode 验证

一个用 Rust 写的 QF_UF SMT 求解器（能生成模型），以及它的 Isabelle/HOL 正确性证明。证明经由 AutoCorrode：Rust 代码先翻译成 uRust，再在 Isabelle 中证明翻译后的程序满足顶层规约。

## 目录

| 目录 | 内容 | Isabelle 会话 |
|---|---|---|
| `solver/` | Rust 求解器 `src/lib.rs` 和测试 `tests/solve.rs` | |
| `urust/` | AutoCorrode 前端从 `solver/src/lib.rs` 生成的 uRust theory | `QFUF`（父会话 `AutoCorrode`） |
| `spec/` | 顶层规约 `QFUF_Spec.thy` | `QFUF_Spec` |
| `pure/` | 同余闭包、模型构造和搜索的纯数学证明 | `QFUF_Pure` |
| `proof/` | 各函数的 uRust 契约证明，以及定理 `solve_correct` | `QFUF_Proof` |

## 求解器

输入是 CNF 形式的 QF_UF 问题：只有一个未解释类型；项按下标组成 DAG，参数的下标小于项本身；原子是两个项的等式。`solve` 枚举所有原子的真值；对满足全部子句的赋值，用同余闭包检查对应的等式与不等式是否一致，一致时从等价类读出模型。

运行测试（在 `solver/` 下）：

```
cargo test --release
```

测试用独立的求值器检查每个 `Sat` 回答的模型；`z3` 在 `PATH` 上时，还与 z3 比较 sat/unsat。

## 规约与证明

规约是 `spec/QFUF_Spec.thy` 中的定义 `solve_correct`：在前置条件 `wf_problem`、`sizes_ok`、原子数小于 `urust_fuel` 下，`solve` 回答 `Sat m` 时 `m` 使问题成立，回答 `Unsat` 时不存在论域为 `nat` 的模型，并且不 panic。各定义的含义和写法理由见该文件中的注释。

`proof/QFUF_Proof.thy` 中的定理 `solve_correct` 证明了这一定义。

检查证明需要 Isabelle2026 和 AutoCorrode（`ZhichengHui/AutoCorrode` 的提交 `d15effd`）：

```
isabelle build -d <AutoCorrode 目录> -d urust -d spec -d pure -d proof QFUF_Proof
```

## 重新生成翻译

`solver/src/lib.rs` 改动后，在仓库根运行 AutoCorrode 前端：

```
urust-frontend.sh --out urust --name QFUF solver/src/lib.rs
```
