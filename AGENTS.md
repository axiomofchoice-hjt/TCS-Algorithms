# AGENTS.md

## 测试运行时间上限

`tests/` 下每个算法的测试文件（对应一个 suite）在 **debug 配置、不定义 `TCS_NO_TEMP_IMPL`** 时必须 **0.5s 以内**。

```sh
xmake f -m debug && xmake
./build/tests/test --filter <suite>   # 例：--filter readonly_sort
```

超时就缩小用例规模（n、repeat、参数扫描范围），不要为此删掉断言。
