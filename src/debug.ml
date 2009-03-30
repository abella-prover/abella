let debug_level = ref 0

let debug msg = if !debug_level > 0 then
  print_endline msg
