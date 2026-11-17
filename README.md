# QFUF

一个支持 QF_UF 的 SMT 求解器，能给出模型。求解器用 Rust 写成，经 AutoCorrode 翻译到 Isabelle/HOL，并证明它满足
`spec/` 中以 SMT-LIB 语义写成的规约：回答 `sat` 时给出模型，回答 `unsat` 时问题确实不可满足，在规约的输入范围内
不回答 `unknown`。主定理是 `QFUF_heap.check_sat_correct`（`proof/top/QFUF_Top.thy`）。

    git clone --recursive https://github.com/ZhichengHui/QF_UF_Smt.git
    cargo build --release
    target/release/qfuf FILE.smt2

- 规约：`spec/`
- 规则：`PLAN.md`
- 开发方式：`CLAUDE.md`
- 证明的 HTML：<https://zhichenghui.github.io/QF_UF_Smt/>
