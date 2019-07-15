try
  while true do
    let line = read_line () in
    Printf.printf "Got: <%s>\n" line
  done
with End_of_file ->
  Printf.printf "Got EOF"
