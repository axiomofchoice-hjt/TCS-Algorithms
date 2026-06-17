-- TCS-Algorithms xmake build configuration
-- C++23 / Header-only

set_project("TCS-Algorithms")
set_version("0.1.0")

-- C++23 standard
set_languages("c++23")

-- Warning flags
add_cxflags("-Wall", "-Wextra")

-- Header-only library target
target("tcs")
    set_kind("headeronly")
    add_includedirs("include", {public = true})

-- Test target
target("test")
    set_kind("binary")
    add_files("tests/*.cpp")
    add_includedirs("tests")
    add_deps("tcs")
    set_targetdir("$(builddir)/tests")

-- Example targets (each file compiled as a standalone executable)
for _, file in ipairs(os.files("examples/*.cpp")) do
    local basename = path.basename(file)
    target(basename)
        set_kind("binary")
        add_files(file)
        add_deps("tcs")
        set_targetdir("$(builddir)/examples")
end
