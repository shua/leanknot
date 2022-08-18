import Lake
open Lake DSL

package knot {
  -- add package configuration options here
}

lean_lib Knot {}

lean_lib Basic {}

lean_lib Tangle {}

lean_lib Link {}

--@[defaultTarget]
--lean_exe knot {
--  root := `Main
--}
