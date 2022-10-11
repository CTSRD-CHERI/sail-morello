let implode l =
  let res = Bytes.create (Stdlib.List.length l) in
  let rec imp i = function
    | [] -> Bytes.to_string res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;;
let nat_word_length w =
  match w with
  | Word.WS (_, i, _) -> Datatypes.S i
  | Word.WO -> Datatypes.O
;;
let string_of_word w = implode (String0.string_of_word (nat_word_length w) w);;
let word_of_int length i = Word.coq_NToWord (ExtrOcamlIntConv.nat_of_int length) (ExtrOcamlIntConv.n_of_int i);; 

let run exp s =
  match State_lifting.liftState Morello_types.register_accessors exp s State_monad.default_choice with
  | [] -> failwith "dead!"
  | [((Value v, s'), _)] -> v,s'
  | [((r, _), _)] -> failwith (implode (State_monad.show_result r))
  | _ -> failwith "non-deterministic!"
;;
let s0 = State_monad.init_state Morello.initial_regstate;;
let _,s1 = run (Morello.initialize_registers ()) s0;;
let _,s2 = run (Morello.__InitSystem ()) s1;;

(*
let add1 = word_of_int 32 0x91000400;;
let r,s3 = run (Morello.__DecodeA64 (ExtrOcamlIntConv.z_of_int 32) add1) s2;;
string_of_word s3.ss_regstate._R00;;
*)

(*
let str = word_of_int 32 0xf9000020;;
let s3 = { s2 with ss_regstate = { s2.ss_regstate with _R01 = word_of_int 129 0x01000000 } };;
let r,s4 = run (Morello.__DecodeA64 (ExtrOcamlIntConv.z_of_int 32) str) s3;;
*)
