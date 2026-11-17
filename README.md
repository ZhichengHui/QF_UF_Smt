# QFUF

一个支持 QF_UF（无量词未解释函数）的 SMT 求解器，能给出模型。求解器用 Rust 写成，经 AutoCorrode 前端翻译到
Isabelle/HOL，并证明它满足以 SMT-LIB 语义写成的顶层规约。另一个项目 QF_BV_Smt（QF_BV 求解器）与本项目共用前端、
通用问题结构和语义，目录结构和命名一一对应。

## 目录结构

| 路径 | 内容 |
|---|---|
| `core/src/lib.rs` | 被验证的部分：求解器核心 `solve`（单一论域、项的 DAG、原子为等式的子句集；枚举原子真值，用同余闭包检查），以及通用问题结构上的入口 `check_sat`（片段检查、规模检查、翻译、模型翻译） |
| `frontend/` | SMT-LIB 2.6 前端（未验证，两个项目共用；git submodule，仓库 SMTLIB-frontend）：解析脚本，构造通用问题结构，在 `check-sat` 时调用求解器，输出回答和 `get-model` |
| `cli/src/main.rs` | 可执行程序 `qfuf`：前端加 `check_sat` |
| `urust/` | AutoCorrode 前端从 `core/src/lib.rs` 生成的 Isabelle 翻译，session `QFUF` |
| `spec/` | 顶层规约，session `QFUF_Spec`。主定理的含义只取决于这个目录：`SMT_Types.thy`（生成的通用数据类型的形状）、`SMT_Semantics.thy`（通用问题的语义），这两个文件在两个项目中相同；`QFUF_Spec.thy`（片段、契约、heap locale 与主定理的陈述）；`smtlib-2.6/`（所依据的 SMT-LIB 原文） |
| `proof/core_spec/` | 核心 `solve` 的规约（核心问题的语义、`solve_contract`、`solve_correct`），session `QFUF_CoreSpec`；不属于顶层规约 |
| `proof/` | 核心 `solve` 的证明，session `QFUF_Proof` |
| `proof/smt/` | 翻译的函数式模型及其语义正确性，session `QFUF_Smt` |
| `proof/top/` | Rust 翻译函数的精化、规模检查、规模界与顶层定理，session `QFUF_Top` |
| `tools/` | 检查、测试与评测脚本 |

## 求解器

`check_sat(p: &SmtProblem) -> SmtAnswer` 依次：

1. 检查 `p` 是否在本求解器的片段内（不含位向量的类型、常量和运算），不在则回答 `Unknown`；
2. 计算 `p` 的规模 `smt_size p`（符号、定义、断言的个数加项的节点数，带参数的定义在每个调用处展开），超过 `2^28` 则回答 `Unknown`；
3. 把 `p` 翻译成核心问题（Tseitin 编码；所有未解释类型合并为一个论域；Bool 用常量 TRUE、FALSE 与原子
   `TRUE ≠ FALSE` 表示；带参数的定义在应用处展开）；
4. 调用 `solve`；`Sat` 时把核心模型翻译回通用模型（每个未解释类型取同一个论域）。

核心覆盖 SMT-LIB 2.6 Core 理论的全部运算（`not`、`and`、`or`、`xor`、`=>`、`=`、`distinct`、`ite`）和任意
未解释类型与函数。

## 构建与运行

需要 Rust 工具链。前端是 submodule，克隆时加 `--recursive`，或在克隆后运行
`git submodule update --init`：

    cargo build --release

产物为 `target/release/qfuf`。用法：`qfuf FILE.smt2`，或从标准输入读入脚本。支持 `get-model`，输出满足
SMT-COMP 模型验证的格式；标准错误上不输出任何内容。

## 规约与定理

顶层规约就是 `spec/` 目录：主定理的含义只取决于其中的定义，改动求解器或证明不需要改动它，改动它就是改动规约。
`spec/SMT_Types.thy` 写出从 Rust 代码生成的通用数据类型（`SmtProblem`、`SmtModel`、`SmtAnswer` 等）的每个构造子、
字段及其类型，并由生成的类型证明，Rust 中这些类型一旦改变，构建就失败。`spec/SMT_Semantics.thy` 定义通用问题的语义：良类型 `smt_wf`、表示条件 `smt_repr_ok`（每个 `Vec` 少于 `2^63`
个元素，任何 Rust 值都满足）、求值 `smt_eval`、模型 `smt_is_model`、可满足性 `smt_satisfiable`，以及描述问题写法的
规模度量（`smt_size`、`smt_max_width`、`smt_max_mul_width`）。`spec/QFUF_Spec.thy` 中：

- `smt_in_range p`：本求解器的输入范围，`smt_size p ≤ 2^28`。范围是规约的一部分，固定不变；它覆盖 SMT-LIB 2025 的全部
  QF_UF 基准（最大约 `1.5 · 10^6`）。改动求解器必须继续对范围内的每个问题给出 `Sat` 或 `Unsat`；

- `check_sat_contract p`：前置条件 `smt_wf p ∧ smt_repr_ok p`；回答 `Sat m` 时 `smt_is_model p m`，回答 `Unsat`
  时 `p` 不可满足，回答 `Unknown` 时 `p` 不在片段内或不在输入范围内；不 panic；
- `check_sat_correct Γ`：对每个满足前置条件的 `p`，存在 `N`，使翻译取任意不小于 `N` 的 fuel 时 `check_sat p`
  满足 `check_sat_contract p`。fuel 是翻译给每个循环和递归设的次数上限，对它取存在量词。

顶层定理是 `QFUF_heap.check_sat_correct`（`proof/top/QFUF_Top.thy`），`N` 取 `fuel_top p`。核心的契约
`solve_contract` 和陈述 `solve_correct` 在 `proof/core_spec/` 中，主定理不依赖它们；`proof/QFUF_Proof.thy` 另证明更强的 `solve_contract_vals`
（模型中的值都小于项数，模型翻译需要它）。

例外：`spec/QFUF_Spec.thy` 中的 locale `QFUF_heap` 是生成的 `QFUF_ctx`（`urust/QFUF_Locale.thy`）去掉 fuel 后的副本。
求解器新增一种可变局部变量的类型时，生成的 locale 会多一个参数，`QFUF_heap` 要照样更新；这是 `spec/` 中唯一随求解器
实现改变的部分。

信任基础（不在本仓库中证明）：AutoCorrode 翻译的正确性（fuel 足够时翻译出的函数与 Rust 函数行为一致）；
locale `QFUF_heap` 的假设（AutoCorrode 引用模型的假设）；未验证的前端（把 SMT-LIB 文本转成通用问题结构，
把模型打印成文本）。程序逻辑不模拟内存和栈的耗尽，契约对它们不作断言。

## 证明的组成

| 文件 | 内容 |
|---|---|
| `proof/core_spec/QFUF_CoreSpec.thy` | 核心 `solve` 的规约：核心问题的语义、`solve_contract`、`solve_correct` |
| `proof/QFUF_Pure.thy`、`proof/QFUF_Proof.thy` | 核心 `solve`：同余闭包、模型构造和搜索的纯数学证明与精化，`solve_spec`、`solve_correct`、`solve_vals_spec` |
| `proof/smt/QFUF_SmtModel.thy` | 翻译的函数式模型 `tr_problem_m`、`tr_model_m`；翻译保持语义（`tr_wf_problem`、`tr_model_correct`、`tr_complete`） |
| `proof/top/QFUF_SmtSize.thy` | 规模计算 `input_size` 的契约（饱和算术），其值等于规约的 `smt_size`（`isize_smt_size`），前置条件由良类型推出 |
| `proof/top/QFUF_SmtBound.thy` | 翻译规模的上界 `usize_m` 小于 `2^63` 时翻译满足核心的前置条件（`usize_tr_ok`）；输入范围内该上界小于 `2^63`（`in_range_usize`，上界不超过规模平方的 32 倍） |
| `proof/top/QFUF_SmtRefine.thy` | Rust 翻译函数的行为等于函数式模型：`tr_problem_spec`、`tr_model_spec`、`in_fragment_spec` |
| `proof/top/QFUF_Top.thy` | `check_sat_spec` 与顶层定理 `check_sat_correct` |

## 检查证明

    tools/check.sh [MINUTES]

检查全部证明：把 `urust/`、`spec/`、`proof/` 复制到检查机器上的任务目录
`$CHECK_WORK/qfuf-check-<检出目录名>/`（并行的 worktree 互不冲突），在那里写 `ROOTS` 和一个以任务命名的 session `QFUFCheck_Task`（导入顶层定理
`QFUF_Top.QFUF_Top`），用 `isabelle build -d`（不加 `-b`，不留 heap）在共享的 AutoCorrode heap 上构建，作为
限时 MINUTES 分钟（默认 120）、内存 16 GB 的 systemd 单元运行，结束后输出构建的 session、错误和退出码。
不改动共享的 `ROOTS`。需要 Isabelle2026 和已构建的 AutoCorrode heap。检查机器、任务目录和 Isabelle 的位置是机器相关的配置，不在仓库里，见 `tools/check.sh` 开头的说明。

## 测试

- `cargo test --release`：`core/tests/solve.rs` 直接测试核心；`cli/tests/check_sat.rs` 把 SMT-LIB 脚本经前端交给
  `check_sat`，并用前端的参考求值器检查每个模型。
- `tools/fuzz.py BIN Z3 N [SEED]`：随机 QF_UF 问题，与 z3 比较 sat/unsat，并用 z3 检查模型；
  `tools/remote_fuzz.sh N SEED...` 在检查机器上并行运行它。
- `tools/eval.py`：在 SMT-LIB 基准上评测（回答与 `:status` 比较，模型用 z3 检查）。

## 用 pod 派任务

仓库按 lean-zip 的做法配置了 pod（<https://github.com/kim-em/pod>，多代理管理器），与 Sat 仓库相同：在一台机器上运行
一组 Claude Code agent，每个 agent 在自己的 git worktree 和分支上工作，通过 GitHub issue 接任务、通过 PR 交付，PR 的
CI（spec 校验、cargo test、全部证明）通过后自动 squash 合并。

- 下达任务：开一个 issue。带标签 `agent-plan` 的 issue 由 worker 直接认领去做；带标签 `directive` 的较大任务由 planner
  拆成若干 `agent-plan` issue。只有仓库所有者和协作者写的 issue 与评论会被 agent 读到。
- 规则：`PLAN.md` 写项目规则和方向（只有所有者能改），`CLAUDE.md` 写 agent 的工作方式；agent 的每个任务在
  `progress/` 留一份工作记录。pod 拒绝为改动 `tools/spec.sha256`、`tools/check-spec.sh`、`frontend`、`PLAN.md`、
  `CLAUDE.md`、`.github/`、`.pod/` 的分支开 PR（`.pod/config.toml` 的 `protected_files`）；`spec/` 由 CI 的
  `tools/check-spec.sh` 把关：去掉 heap locale 后与清单一致，heap locale 与生成的 locale 去掉 fuel 后一致，agent
  只能按规则更新这个 locale。
- 启动：在运行 pod 的机器上进入 pod 的工作副本，用所有者环境中的启动脚本运行 pod（`add N` 启动 N 个 agent，`list`、
  `status`、`finish all` 等见 pod 的说明）。启动脚本设置 agent 的环境（Claude Code 配置、令牌、PATH、`tools/check.sh`
  的配置），属于机器相关的配置，不在仓库里。
- agent 开发证明时，用 `tools/devcopy.sh` 生成 `dev/`（导入去掉 session 限定的扁平副本），在 Pool Server 上检查其中的理论；
  提交前 `tools/check.sh` 必须通过。

## 重新生成翻译

`core/src/lib.rs` 改动后，或前端更新后（CI 的 `translation up to date` 失败），用前端 master 分支的最新版本重新生成：

    urust-frontend.sh --out urust --name QFUF core/src/lib.rs
