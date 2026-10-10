# AGENTS.md

## 测试运行时间上限

`tests/` 下每个算法的测试文件在 **debug 配置、不定义 `TCS_NO_TEMP_IMPL`、不开 sanitizer** 时必须 **1s 以内**。

```sh
xmake f -m debug && xmake
./build/tests/test                             # 全部用例
./build/tests/test --filter readonly_sort      # 例：只跑一个 suite
./build/tests/test --list --filter readonly    # 列出匹配的用例及其注册位置
./build/tests/test --time                      # 按文件列出 cases / fail / total / max
```

`--time` 会校验上面的 1s 预算：超预算的文件在表格里标记 `<-- over budget`，并以退出码 `4` 结束。
该预算只在 **debug、未定义 `TCS_NO_TEMP_IMPL` 且未开 sanitizer** 的构建里强制；其它构建（release、true in-place、ASan/UBSan）仍会打印表格，但只提示、不判失败。
`scripts/asan.sh --time` 因此不会误报：sanitizer 构建比基准慢 4-7 倍，它只打印表格。
带上 `--filter` / `--params` 时，表格里的 total 只统计被选中的用例，并不等于该文件的完整耗时。

退出码：`0` 通过，`1` 有用例失败，`2` 命令行错误，`3` 没有选中任何用例，`4` 有文件超预算。
同时有用例失败和文件超预算时退出码取 `1`，但超预算提示仍会打印。

超时就缩小用例规模（n、repeat、参数扫描范围），不要为此删掉断言。

## 禁止运行 clang-tidy

**不要自己跑 `clang-tidy`**（单文件、整目录、脚本里、CI 复现都算），也不要运行包含它的 `scripts/code-quality.sh`。

静态检查的告警由用户提供：拿到告警后只做两件事——按告警改代码，或按用户要求调整 `.clang-tidy` 的 `Checks`。改完用 `clang-format --dry-run --Werror`、构建和 `./build/tests/test` 自证，不要靠重跑 clang-tidy 验证。

## 命令超时上限 20 秒

**每条命令都必须显式设置超时，且最长 20 秒**（bash 工具传 `timeoutMs: 20000`），不允许不设超时，也不允许为了等结果把上限调大。

预计会超过 20 秒的工作（全量构建、全量测试、sanitizer 构建、`scripts/*.sh` 的整轮检查等）必须拆成能在 20 秒内跑完的小步（例如按 `--filter` 分批跑测试、只构建改动到的目标）；拆不开就停下来问用户。

**禁止使用后台任务**：不要用 `run_in_background`，也不要读、杀或等待任何 `job_*`。长任务同样靠拆步解决，不许拿后台或放宽超时绕过上限。
