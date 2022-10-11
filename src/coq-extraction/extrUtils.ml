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
let mword_of_int length i = Values.mword_of_int (ExtrOcamlIntConv.z_of_int length) (ExtrOcamlIntConv.z_of_int i);;
let int_of_word w = ExtrOcamlIntConv.int_of_n (Word.wordToN (nat_word_length w) w);;

let runS (exp : _ State_monad.monadS) s =
  match exp s State_monad.default_choice with
  | [] -> failwith "dead!"
  | [((Value v, s'), _)] -> v,s'
  | [((r, _), _)] -> failwith (implode (State_monad.show_result r))
  | _ -> failwith "non-deterministic!"
;;

let run exp s = runS (State_lifting.liftState Morello_types.register_accessors exp) s
;;

let print_endline cs =
  let () = Stdlib.print_endline (implode cs) in
  Prompt_monad.Done ()

