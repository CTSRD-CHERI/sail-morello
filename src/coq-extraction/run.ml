Elf_loader.load_elf Sys.argv.(1);;
;;

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
(*    Printf.printf "PC = %x\n" (ExtrUtils.int_of_word !Elf_loader.state.ss_regstate._PC);*)
    step()
  done
;;

loop();;
