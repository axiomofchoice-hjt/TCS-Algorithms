-- TCS-Algorithms xmake build configuration
-- C++23 / Header-only

set_project("TCS-Algorithms")
set_version("0.1.0")

-- C++23 standard
set_languages("c++23")

-- Warning flags
add_cxflags("-Wall", "-Wextra")

-- Option: use the true in-place (O(1) extra space) primitives from
-- stable_partition.hpp / stable_select.hpp instead of the std-based stubs,
-- by defining TCS_NO_TEMP_IMPL for every target that consumes the headers.
-- Enable with: xmake f --tcs_no_temp_impl=y
option("tcs_no_temp_impl")
    set_default(false)
    set_showmenu(true)
    set_description(
        "Use true in-place O(1) partition/select primitives instead of std-based stubs (defines TCS_NO_TEMP_IMPL)")
option_end()

local no_temp_impl = has_config("tcs_no_temp_impl")

-- Header-only library target
target("tcs")
    set_kind("headeronly")
    add_includedirs("include", {public = true})
    if no_temp_impl then
        add_defines("TCS_NO_TEMP_IMPL", {public = true})
    end

-- Test target
target("test")
    set_kind("binary")
    add_files("tests/**.cpp")
    add_includedirs("tests")
    add_deps("tcs")
    if no_temp_impl then
        add_defines("TCS_NO_TEMP_IMPL")
    end
    set_targetdir("$(builddir)/tests")

-- Example targets (each file compiled as a standalone executable)
for _, file in ipairs(os.files("examples/**.cpp")) do
    local basename = path.basename(file)
    target(basename)
        set_kind("binary")
        add_files(file)
        add_deps("tcs")
        if no_temp_impl then
            add_defines("TCS_NO_TEMP_IMPL")
        end
        set_targetdir("$(builddir)/examples")
end
