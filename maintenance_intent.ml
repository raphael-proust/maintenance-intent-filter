
let ocaml_versions = [
  "4.08.99"; "4.09.99"; "4.10.99"; "4.11.99"; "4.12.99"; "4.13.99"; "4.14.99";
  "5.0.99"; "5.1.99"; "5.2.99"; "5.3.99"
]

module S = Set.Make(String)
module M = Map.Make(String)


let find_ocaml_dep v opam =
  let ocaml_dep = OpamPackage.Name.of_string "ocaml" in
  let deps = OpamFile.OPAM.depends opam in
  let dep_matches op filter =
    match filter with
    | OpamTypes.FString ver ->
      begin
        let r = match op with
          | `Lt -> OpamVersionCompare.compare v ver <= 0
          | `Leq | `Eq -> OpamVersionCompare.compare v ver < 0
          | `Geq -> OpamVersionCompare.compare v ver >= 0
          | `Gt -> OpamVersionCompare.compare v ver >= 0
          | `Neq -> false
        in
        (*Logs.app (fun m -> m "ocaml version %s op %s ver %s == %B" v
                     (OpamPrinter.FullPos.relop_kind op)
                     ver r); *)
        r
      end
    | _ -> false
  in
  let rec walk_formula p = function
    | OpamTypes.Empty -> false
    | Atom f -> p f
    | Block formula -> walk_formula p formula
    | And (a, b) -> walk_formula p a && walk_formula p b
    | Or (a, b) -> walk_formula p a || walk_formula p b
  in
  let p = function
    | OpamTypes.Filter _ -> false
    | Constraint (op, filter) -> dep_matches op filter
  in
  let rec find_dep = function
    | OpamFormula.Empty -> false
    | Atom (name, cond) ->
      if OpamPackage.Name.equal ocaml_dep name then
        walk_formula p cond
      else
        false
    | Block x -> find_dep x
    | And (a, b) ->
      let a' = find_dep a in
      let b' = find_dep b in
      a' || b'
    | Or (a, b) ->
      let a' = find_dep a in
      let b' = find_dep b in
      a' && b'
  in
  find_dep deps

let find_latest opams =
  List.fold_left (fun acc ocaml_version ->
      (* Logs.app (fun m -> m "for ocaml version %s" ocaml_version); *)
      match List.find_opt (fun (_, opam) -> find_ocaml_dep ocaml_version opam) opams with
      | None -> acc
      | Some (version, opam) ->
        (* Logs.app (fun m -> m "keeping %s" version); *)
        M.add version opam acc
    ) M.empty ocaml_versions

let pkg_name_and_version path =
  match List.rev (Fpath.segs path) with
  | _opam :: pkg_ver :: pkg :: _rest -> pkg, pkg_ver
  | _ -> assert false

let not_maintained (_, opam) =
  match OpamFile.OPAM.extended opam "x-maintained" Fun.id with
  | None -> true
  | Some { pelem = Bool b ; _ } -> b
  | _ -> invalid_arg "maintained: expected a bool"

let jump () opam_repository pkgs =
  let ( let* ) = Result.bind in
  let pkg_dir = Fpath.(v opam_repository / "packages") in
  let* _ = Bos.OS.Dir.must_exist pkg_dir in
  let should_consider path =
    if Fpath.filename path = "opam" then
      let _name, version = pkg_name_and_version path in
      let opam =
        let opam_file =
          OpamFile.make (OpamFilename.raw (Fpath.to_string path))
        in
        OpamFile.OPAM.read opam_file
      in
      Some (version, opam)
    else
      None
  in
  let foreach path acc =
    let* opams = acc in
    match should_consider path with
    | None -> Ok opams
    | Some p -> Ok (p :: opams)
  in
  List.fold_left (fun acc pkg ->
      (* for each pkg, we collect all opam files *)
      let* () = acc in
      let* opams =
        Bos.OS.Dir.fold_contents foreach (Ok []) Fpath.(pkg_dir / pkg)
      in
      let* opams = opams in
      let sorted =
        List.sort (fun (v, _) (v', _) -> OpamVersionCompare.compare v' v)
          opams
      in
      (* we parse the x-maintenance-intent of the last version *)
      let* intent =
        let open OpamParserTypes.FullPos in
        match OpamFile.OPAM.extended (snd (List.hd sorted)) "x-maintenance-intent" Fun.id with
        | None -> Ok "(any)"
        | Some { pelem = List { pelem = [ one ] ; _ } ; _ } ->
          let extract_string = function
            | { pelem = String s ; _ } -> Ok s
            | _ -> Error (`Msg "expected a string")
          in
          extract_string one
        | Some _ -> Error (`Msg "expected a list of a single string")
      in
      let intent = Mintent.M.intent_of_string intent in
      (* if none, we output none *)
      (match intent with
       | Mintent.M.Last x :: [] when x = max_int ->
         (* if any, we output all *)
         let opams = List.filter not_maintained sorted in
         let keeping = List.map fst opams in
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping)) in
         Logs.app (fun m -> m "intent is any@.keeping %a@.removing %a"
                      Fmt.(list ~sep:(any ", ") string) keeping
                      Fmt.(list ~sep:(any ", ") string) remove)
       | Mintent.M.Last 1 :: [] ->
         let opams = find_latest sorted in
         let opams = List.filter not_maintained (M.bindings opams) in
         let keeping = List.map fst opams in
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping)) in
         Logs.app (fun m -> m "intent is latest,@.keeping %a@.removing %a"
                      Fmt.(list ~sep:(any ", ") string) keeping
                      Fmt.(list ~sep:(any ", ") string) remove)
       | Mintent.M.Last 0 :: [] ->
         Logs.app (fun m -> m "intent is none, keeping nothing")
       | _ ->
         let opams = List.filter not_maintained sorted in
         let keeping = List.map fst opams in
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping)) in
         Logs.app (fun m -> m "intent is %s (not handled), keeping %a removing %a"
                      (Mintent.M.string_of_intent intent)
                      Fmt.(list ~sep:(any ", ") string) keeping
                      Fmt.(list ~sep:(any ", ") string) remove)
           (* if latest, we go through all ocaml versions and find the latest package *)
      );
      Ok ())
    (Ok ()) pkgs

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ~dst:Format.std_formatter ())

open Cmdliner

let setup_log =
  Term.(const setup_log
        $ Fmt_cli.style_renderer ()
        $ Logs_cli.level ())

let pkg =
  let doc = "Archive this package (may be package name or package.version)" in
  Arg.(value & opt_all string [] & info ~doc ["pkg"])

let opam_repository =
  let doc = "Opam repository directory to work on (must be a git checkout)" in
  Arg.(value & opt dir "." & info ~doc ["opam-repository"])

let cmd =
  let info = Cmd.info "maintenance-intent" ~version:"%%VERSION_NUM%%"
  and term =
    Term.(term_result (const jump $ setup_log $ opam_repository $ pkg))
  in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
