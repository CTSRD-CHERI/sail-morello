let opt_verbose = ref false
let opt_cycle_limit = ref (-1)
let opt_files : string list ref = ref []

let options = Arg.align [
  ("-v", Arg.Set opt_verbose, " verbose");
  ("--cycle-limit", Arg.Set_int opt_cycle_limit, "<int> exit after given number of instructions")
]
;;
Arg.parse options (fun s -> opt_files := s :: !opt_files) "run";;

Stdlib.List.iter Elf_loader.load_elf !opt_files;;

Elf_loader.state := { !Elf_loader.state with ss_regstate = { !Elf_loader.state.ss_regstate with coq_CFG_RVBAR = ExtrUtils.word_of_int 64 0x10300000 } };;

let runS exp =
  let r,s = ExtrUtils.runS exp !Elf_loader.state in
  Elf_loader.state := s;
  r
;;
let run exp = runS (State_lifting.liftState Morello_types.register_accessors exp)
;;

run (Morello.initialize_registers ());;
run (Morello.__InitSystem ());;

let step () = begin
    Elf_loader.state := { !Elf_loader.state with ss_regstate = { !Elf_loader.state.ss_regstate with coq_SEE = ExtrOcamlIntConv.z_of_int (-1) } };
    run (Morello.__TopLevel ())
  end
;;

print_endline "Running...";;

let loop () =
  while true do
    if !opt_verbose then
      Printf.printf "PC = %x\n" (ExtrUtils.int_of_word !Elf_loader.state.ss_regstate._PC);
    step();
    if !opt_cycle_limit > 0 then opt_cycle_limit := !opt_cycle_limit - 1;
    if !opt_cycle_limit = 0 then failwith "Cycle limit reached"
  done
;;

loop();;
