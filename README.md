# TCS-Algorithms

理论计算机科学算法实现（Theoretical Computer Science Algorithms）。

使用 **C++23** 标准，**xmake** 构建系统，**Catch2** 测试框架。

## 目录结构

```text
TCS-Algorithms/
├── include/tcs/      # Header-only 算法模板库
├── tests/            # 单元测试（Catch2）
├── xmake.lua         # 构建配置
└── README.md
```

## 依赖

- **编译器**：GCC 14+ / Clang 18+（需支持 C++23）
- **构建工具**：[xmake](https://xmake.io/)
- **测试框架**：[Catch2](https://github.com/catchorg/Catch2)（xmake 自动拉取）

## 构建与运行

```bash
# 安装 xmake（如未安装）
curl -fsSL https://xmake.io/shget.text | bash

# 构建并运行所有测试
xmake run test
```

## 使用

Header-only，拷贝 `include/` 到你的项目或通过 xmake 集成：

```cpp
#include <tcs/bfprt.hpp>

std::vector<int> arr = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5};
int k = 5;
bfprt(arr.data(), arr.data() + k, arr.data() + arr.size());
// arr[k] 即为第 k 小的元素，且已三路划分
```

## 已实现的算法

- **BFPRT** — 最坏情况 O(n) 的第 k 小选择算法（Median of Medians）
