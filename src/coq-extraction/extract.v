From Coq Require Extraction.
From Coq.extraction Require ExtrOcamlBasic ExtrOcamlString ExtrOcamlIntConv.
From Sail Require String State_lifting.
Require arm_extras morello_types morello.

(* Used by Coq's Real library *)
Extract Constant ClassicalDedekindReals.sig_forall_dec => "fun _ -> assert false".
Extract Constant ClassicalDedekindReals.sig_not_dec => false.  (* Ugh *)

Extract Inlined Constant arm_extras.print_endline_monadic => "ExtrUtils.print_endline".
Extract Inlined Constant State_monad.write_mem_bytesS => "Writeshim.write_mem_bytesS".

Extraction Blacklist Nat.

Separate Extraction
  ExtrOcamlIntConv
  State_lifting
  State_monad
  Sail.String
  arm_extras
  morello_types
  morello.
