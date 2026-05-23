-- TCS-Algorithms xmake build configuration
-- C++23 / Catch2 / Header-only

set_project("TCS-Algorithms")
set_version("0.1.0")

-- C++23 standard
set_languages("c++23")

-- Add Catch2 dependency
add_requires("catch2")

-- Header-only library target
target("tcs")
    set_kind("headeronly")
    add_includedirs("include", {public = true})
    add_packages("catch2")

-- Test target
target("test")
    set_kind("binary")
    add_files("tests/*.cpp")
    add_deps("tcs")
    add_packages("catch2")
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
