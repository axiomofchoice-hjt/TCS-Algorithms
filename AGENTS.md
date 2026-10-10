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
