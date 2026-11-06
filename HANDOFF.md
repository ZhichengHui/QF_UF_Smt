# 交接：QF_UF 求解器的 AutoCorrode 验证

任务：用 Rust 实现一个支持 QF_UF、能生成模型的 vanilla SMT 求解器，用 AutoCorrode 前端翻译到 Isabelle，写顶层规约并证明。

## 位置

仓库 `~/Work/AutoCorrode-QFUF`（本地仓库，没有远端），工作区 `.claude/worktrees/qfuf-solver`，分支 `worktree-qfuf-solver`。main 上只有空的初始提交；按用户规则，用户确认后再把分支合并进 main，并删除分支和工作区。

| 目录 | 内容 |
|---|---|
| `solver/` | Rust crate（`src/lib.rs`）和测试（`tests/solve.rs`） |
| `urust/` | 前端翻译出的 uRust theory（会话 `QFUF`） |
| `spec/` | 顶层规约 `QFUF_Spec.thy`（会话 `QFUF_Spec`），审阅注释写在文件开头 |
| `pure/` | 纯数学证明 `QFUF_Pure.thy`（会话 `QFUF_Pure`） |
| `proof/` | uRust 契约证明 `QFUF_Proof.thy`（会话 `QFUF_Proof`） |
| `tools/check.sh` | 在计算主机上检查 theory 的脚本 |
| `scratch/` | 辅助脚本和输出，被 git 忽略 |

## 求解器

输入是 CNF 形式的 QF_UF 问题：只有一个未解释类型；项按下标组成 DAG，参数的下标都小于项本身；原子是两个项的等式。算法是朴素回溯，枚举所有原子的真值。叶子上先检查命题部分（`prop_holds`），再做理论检查（`theory_check`）：`init_rep` 建立单元素划分，`assert_eqs` 合并真原子的两边，`close` 反复调用 `scan`/`scan_row` 直到同余闭合，`finish` 检查假原子的两边不在同一类，然后由 `build_model`/`rep_args` 构造模型。

`solver/` 下运行 `~/Work/AutoCorrodeRustFrontEnd/scripts/cargo.sh test --release`，4 个测试全部通过。随机 400 例的 sat/unsat 与 z3 一致，每个模型都由独立求值器验证。

为了方便证明，做过两类语义不变的改写：
- 把嵌套或连续的循环拆成单循环的小函数。
- 新增 `finish(p, a, rep: &mut Vec<usize>)`，它的 `rep` 是 `&mut` 但只读。原因是 `close` 的后置条件带存在量词，紧接着解引用 `rep` 时 crush 会卡住；改成只把 `rep` 传给下一个调用后，证明可以继续。

翻译命令（在仓库根运行）：`~/Work/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name QFUF solver/src/lib.rs`，占位符为 0。

## 证明状态

- `spec/QFUF_Spec.thy`：可以构建。契约 `solve_contract` 的内容：
  - 回答 `Sat m` 时，`model_interp m` 满足问题；
  - 回答 `Unsat` 时，问题不可满足（`¬ satisfiable p`）；
  - 不 panic。
  - 前置条件：`wf_problem`、`sizes_ok`（各个 Vec 的长度小于 2^63）、`length atoms < urust_fuel`。
- `pure/QFUF_Pure.thy`：完整通过，没有 sorry。
- `proof/QFUF_Proof.thy` 中已逐个检查通过的契约（检查时其余引理换成 sorry）：`clause_holds`、`prop_holds`、`merge`、`congruent`、`scan_row`、`scan`、`close`、`rep_args`、`build_model`、`init_rep`、`diseqs_ok`，以及 `search_rec_spec`、`solve_unsat_any_domain` 和所有辅助引理。
- 证明已写好但还没检查：`assert_eqs_spec`、`finish_spec`、`theory_check_spec`、`search_rec_step_spec`、`solve_spec`（在提交 `9dccbe3` 中）。写好时计算主机失联，所以这几个能否通过还未知，可能还需要再调一两轮。
- 文件中没有 `sorry`、`oops` 或 `apply fail`。整个会话还没有不带 quick_and_dirty 完整构建过。

## 下一步

1. 在仓库根运行：
   - `python3 scratch/focus.py proof/QFUF_Proof.thy assert_eqs_spec finish_spec theory_check_spec search_rec_step_spec solve_spec`
   - `TIMEOUT=1800 tools/check.sh proof proof/v | scratch/errs.sh`
   - urust 改过，第一次运行会先重建 `QFUF`、`QFUF_Spec`、`QFUF_Pure` 三层 heap。
2. 有失败时，`errs.sh` 的输出会给出剩余子目标，在对应位置补收尾的 `apply`。
3. 全部通过后运行 `tools/check.sh session`，不带 quick_and_dirty 构建 `QFUF_Proof`，这是最终验证。
4. 用户确认后：合并进 main，删除分支和工作区，并删除远端的 `/disk/scratch/s2982359/qfuf/` 和 `~/.isabelle/Isabelle2026/heaps/polyml-*/` 下的 `QFUF*` heap 及其日志。

## 检查环境与经验

- 证明都在计算主机上检查：`ssh -J s2982359@ssh.inf.ed.ac.uk s2982359@s2982359.pgr.inf.ed.ac.uk`，Isabelle2026，AutoCorrode 在 `~/builds/AutoCorrode`（提交 `d15effd`，与本地 `~/Work/AutoCorrode` main 一致）。本机内存不足，不在本机跑 Isabelle。本地的 isabelle-pool-server MCP 连不上，未使用。
- `tools/check.sh` 的模式：
  - `build`：构建三层 heap；
  - `proof [FILE|DIR...]`：在 `QFUF_Pure` heap 上并行运行 `process_theories` 并打印消息，目录参数代表其下的 `*/*.thy`；
  - `session`：最终构建。
- heap 记录了会话目录的路径，所以 `urust/`、`spec/`、`pure/` 固定同步到远端的 `/disk/scratch/s2982359/qfuf/base/`，证明文件在每次运行各自的目录里。proof 模式会先串行确保 heap 是最新的，再并行检查。
- 每个检查放在独立的进程组里，超时时结束整个组（包括 `poly`）。不要用 `timeout` 直接包 `process_theories`：它只结束外层进程，`poly` 会成为遗留进程。
- `scratch/focus.py FILE LEMMA...`：生成 `proof/v/<LEMMA>/`，每个变体只保留一个引理的证明，其余换成 sorry。它调用 `~/Work/AutoCorrode-CreuSAT/tools/variants.py`，后者只识别以 `lemma` 开头的条目。
- `scratch/errs.sh`：只保留 `===` 标题行、`EXIT` 行和每个错误的第一份消息。
- crush 的经验：
  - 要化简 `unat (word64_of_nat …)`，长度界必须是显式假设。做法是在第一次 `crush_base` 时展开 `cc_inv_def`、`sizes_ok_def`，并在 simp 集里加 `unat_of_nat_lt63`。
  - 目标中出现的是数字 `18446744073709551616`，不是 `2^64`，辅助引理要写成数字形式。
  - 不变式里不要用变量名 `o`，它是复合运算符。
  - HOL 的 `map`/`find` 被 AutoCorrode 遮蔽，要写成 `List.map`、`List.find`。
  - simp 会循环展开 `term_val_wf` 和 `word_unat_eq_iff`，应该用方向固定的 `unat_eq_iff_eq` 或显式等式链。
  - 证明很慢时，用"每次只保留一个 `by`"的变体定位慢的那一步。

## 计算主机上的遗留进程

早期检查脚本超时时只结束了外层进程，留下了 19 个 QFUF 的 `poly` 进程。它们的工作目录是 `/tmp/isabelle-s2982359/private*/Draft`，目录中的文件含 "QFUF"。识别方法：`readlink /proc/<pid>/cwd` 在该路径下，并且 `grep -rqs QFUF <cwd>` 能匹配。用户已授权结束这些进程。同一主机上 `explore-postcond-proof`、`frontend-corpus` 等任务的进程不属于本任务，不能动。
