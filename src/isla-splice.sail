val __ReadTaggedMem
  = { lem: "read_memt", coq: "read_memt", c: "platform_read_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit) effect {rmemt}

val __WriteTaggedMem
  = { lem: "write_memt", coq: "write_memt", c: "platform_write_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool effect {wmvt}

val __WriteMem
  = { lem: "write_mem", coq: "write_mem", c: "platform_write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}
