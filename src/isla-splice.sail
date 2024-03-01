val __ReadTaggedMem
  = { lem: "read_memt", coq: "read_memt", c: "platform_read_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit) effect {rmemt}

val __WriteTaggedMem
  = { lem: "write_memt", coq: "write_memt", c: "platform_write_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool effect {wmvt}

val __WriteMem
  = { lem: "write_mem", coq: "write_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}

function __WriteMem(wk, addrsize, addr, size, data) = {
  // Address is aligned to access size at this point
  assert(addr == Align(addr, size));
  // Clear capability tag (this access can't straddle multiple capabilities due
  // to the alignment)
  let tag_addr = Align(addr, CAPABILITY_DBYTES);
  let _ = __write_tag(wk, ZeroExtend(tag_addr, 64), bitzero);
  match('addrsize) {
    32 => __write_mem(wk, 32, addr, size, data),
    64 => __write_mem(wk, 64, addr, size, data)
  }
}
