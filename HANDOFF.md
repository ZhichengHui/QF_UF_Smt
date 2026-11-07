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
- `proof/QFUF_Proof.thy`：全部完成，没有 `sorry`、`oops` 或 `apply fail`。`tools/check.sh session`（不带 quick_and_dirty）构建 `QFUF_Proof` 通过（2026-11-07）。
- 最后一轮的改动：
  - `finish_contract` 去掉了参数 `g rs`，`rep` 的状态改为在前置、后置条件里存在量化。否则 `theory_check` 调用 `finish` 时，参数的 schematic 会先于 `close` 后置条件的存在量词生成，无法实例化。
  - `assert_eqs_spec`：循环体以 `merge` 调用结束，crush 会先实例化不变式的存在量词，再打开 `merge` 后置条件的存在量词。证明改为在 `crush_allow_schematics = false` 下运行 crush，两个分支分别处理：else 分支用 `aexists_entailsR` 显式代入，then 分支用 `merge_spec[where g=g' and rs=rs']`。
  - 新增的辅助引理放在 `close_spec` 之后。`scan_row_spec` 等较早的 crush 证明对上下文里的事实敏感（crush 按相关性挑选事实）。

## 下一步

用户确认后：合并进 main，删除分支和工作区，并清理远端：
- `/disk/scratch/s2982359/qfuf/`（check.sh 的工作目录）；
- `~/.isabelle/Isabelle2026/heaps/polyml-*/` 下的 `QFUF*` heap 及其日志；
- `/disk/scratch/s2982359/qfuf-pool/`（自己的 pool server 实例，tmux 会话 `qfuf-pool`，需先结束）；
- 共享 pool server 中加的东西：`/disk/scratch/s2982359/bvsmt-pool/qfuf-pure/`，以及 `/disk/scratch/s2982359/isabelle-pool-server-home/.isabelle/Isabelle2026/ROOTS` 里追加的两行 `qfuf/base/urust`、`qfuf/base/spec`。

## 检查环境与经验

- 证明都在计算主机上检查：`ssh -o ProxyCommand='ssh -q s2982359@ssh.inf.ed.ac.uk nc -4 s2982359.pgr.inf.ed.ac.uk 22' s2982359@s2982359.pgr.inf.ed.ac.uk`（`-J` 方式会走不通的 IPv6），Isabelle2026，AutoCorrode 在 `~/builds/AutoCorrode`（提交 `d15effd`，与本地 `~/Work/AutoCorrode` main 一致）。本机内存不足，不在本机跑 Isabelle。
- `tools/check.sh` 的模式：
  - `build`：构建三层 heap；
  - `proof [FILE|DIR...]`：在 `QFUF_Pure` heap 上并行运行 `process_theories` 并打印消息，目录参数代表其下的 `*/*.thy`；
  - `session`：最终构建。
- heap 记录了会话目录的路径，所以 `urust/`、`spec/`、`pure/` 固定同步到远端的 `/disk/scratch/s2982359/qfuf/base/`，证明文件在每次运行各自的目录里。proof 模式会先串行确保 heap 是最新的，再并行检查。
- 每个检查用 `setsid` 放在独立的会话里。`poly` 在另一个进程组里，只结束进程组会留下它，所以超时时先递归结束整棵子进程树，再用 `pkill -s` 兜底；检查结束时也再清一次。默认超时 600 秒。不要用 `timeout` 直接包 `process_theories`：它只结束外层进程，`poly` 会成为遗留进程。
- 出错的命令之后，`process_theories` 有时不退出，一直挂到超时。所以超时要设得接近正常耗时（单引理变体 2 到 5 分钟，完整文件约 5 分钟）。
- 一个不终止的 `metis`（比如带大数字的传递推理）会让整个文件挂住。能用 `rule`/`erule` 写出的步骤不要交给 `metis`。
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

早期检查遗留的 19 个 QFUF `poly` 进程已经结束（用户授权，结束后剩余 0 个）。

## isabelle-pool-server（交互式检查）

- 本机 MCP 连 `http://localhost:8000`，需要一条到计算主机上服务器的 SSH 隧道。本机所有 Claude 会话共用这个端口，隧道指向哪个实例，大家就都连到哪个实例。
- 共享实例（远端 `~/README.md` 第 68 行起）在 `systemd-run --user --scope` 下运行，读不到权限为 600 的 AFS 文件（`~/builds/AutoCorrode`）。自己的实例 `/disk/scratch/s2982359/qfuf-pool/`：家目录是共享家目录的副本，AutoCorrode 和 Word_Lib 复制到了 `src/`，监听 8001，heap 登记在 task group `qfuf2`。
- MCP 每次加载文件的预算是 `ISABELLE_MCP_LSP_LOAD_TIMEOUT`（默认 30 秒）。超时后服务器会把整个文件从 PIDE 文档中删掉，所有还在运行的命令随之取消。此后 MCP 显示的 `still_running` 是旧报告，按行查询都返回"no command at line"。所以超过 30 秒的 crush 步骤在 MCP 里永远跑不完，这类证明要用 `check.sh` 检查，或者先调大这个预算。
