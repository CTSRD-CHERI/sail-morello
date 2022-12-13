let int_of_mword sz w = ExtrOcamlIntConv.int_of_z (Operators_mwords.uint (ExtrOcamlIntConv.z_of_int sz) w);;

let write_mem_bytesS wk addr sz v =
  let addr_int = ExtrOcamlIntConv.int_of_n addr in
  (*Printf.printf "Write to %x\n" addr_int;*)
  if addr_int == 0x13000000 then begin
      let byte = int_of_mword 8 (Option.get (Values.of_bits (ExtrOcamlIntConv.z_of_int 8) (Stdlib.List.hd v))) in
      if byte == 4 then exit 0;
      print_char (char_of_int byte);
      flush stdout
    end;
  State_monad.write_memt_bytesS wk addr sz v B0
