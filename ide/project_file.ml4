type target =
  | ML of string (* ML file : foo.ml -> (ML "foo.ml") *)
  | MLI of string (* MLI file : foo.mli -> (MLI "foo.mli") *)
  | ML4 of string (* ML4 file : foo.ml4 -> (ML4 "foo.ml4") *)
  | MLLIB of string (* MLLIB file : foo.mllib -> (MLLIB "foo.mllib") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Arg of string
  | Special of string * string * string (* file, dependencies, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | Include of string
  | RInclude of string * string (* -R physicalpath logicalpath *)


exception Parsing_error
let rec parse_string = parser
  | [< '' ' | '\n' | '\t' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string s)
  | [< >] -> ""
and parse_string2 = parser
  | [< ''"' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string2 s)
and parse_skip_comment = parser
  | [< ''\n'; s >] -> s
  | [< 'c; s >] -> parse_skip_comment s
  | [< >] -> [< >]
and parse_args = parser
  | [< '' ' | '\n' | '\t'; s >] -> parse_args s
  | [< ''#'; s >] -> parse_args (parse_skip_comment s)
  | [< ''"'; str = parse_string2; s >] -> ("" ^ str) :: parse_args s
  | [< 'c; str = parse_string; s >] -> ((String.make 1 c) ^ str) :: (parse_args s)
  | [< >] -> []


let parse f =
  let c = open_in f in
  let res = parse_args (Stream.of_channel c) in
    close_in c;
    res

let rec process_cmd_line ((project_file,makefile,install,opt) as opts) l = function
  | [] -> opts,List.rev l
  | ("-h"|"--help") :: _ ->
    raise Parsing_error
  | ("-no-opt"|"-byte") :: r ->
    process_cmd_line (project_file,makefile,install,false) l r
  | ("-full"|"-opt") :: r ->
    process_cmd_line (project_file,makefile,install,true) l r
  | "-impredicative-set" :: r ->
    Minilib.safe_prerr_endline "Please now use \"-arg -impredicative-set\" instead of \"-impredicative-set\" alone to be more uniform.";
    process_cmd_line opts (Arg "-impredicative_set" :: l) r
  | "-no-install" :: r ->
    if not install then Minilib.safe_prerr_endline "Warning: -no-install sets more than once.";
    process_cmd_line (project_file,makefile,false,opt) l r
  | "-custom" :: com :: dependencies :: file :: r ->
    process_cmd_line opts (Special (file,dependencies,com) :: l) r
  | "-I" :: d :: r ->
    process_cmd_line opts (Include d :: l) r
  | "-R" :: p :: lp :: r ->
    process_cmd_line opts (RInclude (p,lp) :: l) r
  | ("-I"|"-custom") :: _ ->
    raise Parsing_error
  | "-f" :: file :: r ->
    let () = match project_file with
      | None -> ()
      | Some _ -> Minilib.safe_prerr_endline
	"Warning: Several features will not work with multiple project files."
    in process_cmd_line (Some file,makefile,install,opt) l ((parse file)@r)
  | ["-f"] ->
    raise Parsing_error
  | "-o" :: file :: r ->
    let () = match makefile with
      |None -> ()
      |Some f ->
	Minilib.safe_prerr_endline ("Warning: Only one output file in genererated. "^f^" will not.")
    in process_cmd_line (project_file,Some file,install,opt) l r
  | v :: "=" :: def :: r ->
    process_cmd_line opts (Def (v,def) :: l) r
  | "-arg" :: a :: r ->
    process_cmd_line opts (Arg a :: l) r
  | f :: r ->
    process_cmd_line opts ((
      if Filename.check_suffix f ".v" then V f
      else if (Filename.check_suffix f ".ml") then ML f
      else if (Filename.check_suffix f ".ml4") then ML4 f
      else if (Filename.check_suffix f ".mli") then MLI f
      else if (Filename.check_suffix f ".mllib") then MLLIB f
      else Subdir f) :: l) r

let rec post_canonize f =
  if Filename.basename f = Filename.current_dir_name
  then let dir = Filename.dirname f in
    if dir = Filename.current_dir_name then f else post_canonize dir
  else f

(* Return: ((v,(mli,ml4,ml,mllib),special,subdir),(i_inc,r_inc),(args,defs)) *)
let rec split_arguments = function
  | V n :: r ->
      let (v,m,o,s),i,d = split_arguments r in ((Minilib.strip_path n::v,m,o,s),i,d)
  | ML n :: r ->
      let (v,(mli,ml4,ml,mllib),o,s),i,d = split_arguments r in ((v,(mli,ml4,Minilib.strip_path n::ml,mllib),o,s),i,d)
  | MLI n :: r ->
      let (v,(mli,ml4,ml,mllib),o,s),i,d = split_arguments r in ((v,(Minilib.strip_path n::mli,ml4,ml,mllib),o,s),i,d)
  | ML4 n :: r ->
      let (v,(mli,ml4,ml,mllib),o,s),i,d = split_arguments r in ((v,(mli,Minilib.strip_path n::ml4,ml,mllib),o,s),i,d)
  | MLLIB n :: r ->
      let (v,(mli,ml4,ml,mllib),o,s),i,d = split_arguments r in ((v,(mli,ml4,ml,Minilib.strip_path n::mllib),o,s),i,d)
  | Special (n,dep,c) :: r ->
      let (v,m,o,s),i,d = split_arguments r in ((v,m,(n,dep,c)::o,s),i,d)
  | Subdir n :: r ->
      let (v,m,o,s),i,d = split_arguments r in ((v,m,o,n::s),i,d)
  | Include p :: r ->
      let t,(i,r),d = split_arguments r in (t,((post_canonize p,Minilib.canonical_path_name p)::i,r),d)
  | RInclude (p,l) :: r ->
      let t,(i,r),d = split_arguments r in (t,(i,(post_canonize p,l,Minilib.canonical_path_name p)::r),d)
  | Def (v,def) :: r ->
      let t,i,(args,defs) = split_arguments r in (t,i,(args,(v,def)::defs))
  | Arg a :: r ->
      let t,i,(args,defs) = split_arguments r in (t,i,(a::args,defs))
  | [] -> ([],([],[],[],[]),[],[]),([],[]),([],[])

let read_project_file f = split_arguments (snd (process_cmd_line (Some f, None, false, true) [] (parse f)))

let args_from_project file project_files =
  let contains_file f dir =
    let is_f = Minilib.same_file f in
      List.exists (fun x -> let tmp = (if Filename.is_relative x then Filename.concat dir x else x)
		   in Minilib.safe_prerr_endline tmp; is_f tmp)
  in try
      let (_,(_,(i_inc,r_inc),(args,_))) = List.find (fun (dir,((v_files,_,_,_),_,_)) ->
							contains_file file dir v_files) project_files in
	List.fold_right (fun (_,i) o -> "-I" :: i :: o) i_inc
	  (List.fold_right (fun (_,l,p) o -> "-R" :: p :: l :: o) r_inc
	     (List.fold_right (fun a o -> parse_args (Stream.of_string a) @ o) args []))
    with Not_found -> []
