let may_read_line () =
  try Some (read_line ())
  with End_of_file -> None

let rec loop acc =
  match may_read_line () with
  | Some line -> line :: acc |> loop
  | None -> List.rev acc

let _ =
  if Array.length Sys.argv < 2 then raise (Failure "Not enough arguments");
  let party = Sys.argv.(1) in
  let lines = loop [] in
  print_endline "-1";
  print_endline ("I am " ^ party);
  List.iter (fun s -> print_string (party ^ " got: "); print_endline s) lines
