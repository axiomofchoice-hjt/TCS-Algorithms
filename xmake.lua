-- TCS-Algorithms xmake build configuration
-- C++23 / Header-only

set_project("TCS-Algorithms")
set_version("0.1.0")

-- C++23 standard
set_languages("c++23")

-- Warning flags
add_cxflags("-Wall", "-Wextra")

-- Option: build the local test/example binaries with AddressSanitizer and
-- UndefinedBehaviorSanitizer. This is for on-demand (manual) hardening, not CI.
-- Enable with: xmake f --tcs_sanitize=y
option("tcs_sanitize")
    set_default(false)
    set_showmenu(true)
    set_description(
        "Build test/example binaries with ASan+UBSan (-fsanitize=address,undefined)")
option_end()

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
    -- Mark the build so the test harness can exclude it from the per-file time
    -- budget: instrumentation slows the suite by 4-7x, so enforcing the budget
    -- here would report files as over budget that are not. This also covers
    -- compilers that do not predefine __SANITIZE_ADDRESS__ (Clang).
    add_defines("TCS_SANITIZE")
end

-- Header-only library target
target("tcs")
    set_kind("headeronly")
    add_includedirs("include", {public = true})

-- Test target
target("test")
    set_kind("binary")
    add_files("tests/**.cpp")
    add_includedirs("tests")
    add_deps("tcs")
    apply_sanitize()
    set_targetdir("$(builddir)/tests")

-- Example targets (each file compiled as a standalone executable)
for _, file in ipairs(os.files("examples/**.cpp")) do
    local basename = path.basename(file)
    target(basename)
        set_kind("binary")
        add_files(file)
        add_deps("tcs")
        apply_sanitize()
        set_targetdir("$(builddir)/examples")
end
