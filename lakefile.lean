import Lake
open Lake DSL

package imperia

@[default_target]
lean_lib Imperia

@[test_driver]
lean_lib ImperiaTests where
  globs := `ImperiaTests.+
