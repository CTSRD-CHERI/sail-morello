Require Import SailStdpp.Base.
Require Import Lia.
Local Open Scope Z.
Require Import morello_types.

Definition write_ram addrsize size (hexRAM : mword addrsize) (address : mword addrsize) (value : mword (8 * size)) : M unit :=
  write_mem_ea Write_plain addrsize address size >>
  write_mem Write_plain addrsize address size value >>= fun _ =>
  returnm tt.

Definition read_ram addrsize size (hexRAM : mword addrsize) (address : mword addrsize) : M (mword (8 * size)) :=
  read_mem Read_plain addrsize address size.

(* A version of print_endline in the monad so that it doesn't disappear during
   extraction to OCaml.  A change in the Sail library declaration has to be
   spliced in to use it. *)
Definition print_endline_monadic (_:string) : M unit := returnm tt.
