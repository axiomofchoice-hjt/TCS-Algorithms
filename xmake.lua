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

-- Option: build the local test/example binaries with AddressSanitizer and
-- UndefinedBehaviorSanitizer. This is for on-demand (manual) hardening, not CI.
-- Enable with: xmake f --tcs_sanitize=y
option("tcs_sanitize")
    set_default(false)
    set_showmenu(true)
    set_description(
        "Build test/example binaries with ASan+UBSan (-fsanitize=address,undefined)")
option_end()

local no_temp_impl = has_config("tcs_no_temp_impl")
local sanitize = has_config("tcs_sanitize")

-- Apply ASan+UBSan flags to the *current* target (call inside a target block).
local function apply_sanitize()
    if not sanitize then
        return
    end
    add_cxxflags("-fsanitize=address,undefined", "-fno-omit-frame-pointer")
    -- `{force = true}`: xmake's linker-flag auto-check otherwise drops
    -- -fsanitize here, which would leave ASan symbols unresolved at link time.
    add_ldflags("-fsanitize=address,undefined", {force = true})
end

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
    apply_sanitize()
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
        apply_sanitize()
        set_targetdir("$(builddir)/examples")
end
