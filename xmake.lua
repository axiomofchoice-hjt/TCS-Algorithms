-- TCS-Algorithms xmake 构建配置
-- C++23 / Catch2 / Header-only

set_project("TCS-Algorithms")
set_version("0.1.0")

-- C++23 标准
set_languages("c++23")

-- 添加 Catch2 依赖
add_requires("catch2")

-- Header-only 库目标
target("tcs")
    set_kind("headeronly")
    add_includedirs("include", {public = true})
    add_packages("catch2")

-- 测试目标
target("test")
    set_kind("binary")
    add_files("tests/*.cpp")
    add_deps("tcs")
    add_packages("catch2")
    set_targetdir("$(builddir)/tests")

-- 示例目标（每个文件独立编译为可执行文件）
for _, file in ipairs(os.files("examples/*.cpp")) do
    local basename = path.basename(file)
    target(basename)
        set_kind("binary")
        add_files(file)
        add_deps("tcs")
        set_targetdir("$(builddir)/examples")
end
