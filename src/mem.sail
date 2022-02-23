/******************************************************************************/
/*  BSD 3-clause Clear License                                                */
/*                                                                            */
/*  Copyright (c) 2022                                                        */
/*    Arm Limited (or its affiliates),                                        */
/*    Thomas Bauereiss,                                                       */
/*    Brian Campbell,                                                         */
/*    Alasdair Armstrong,                                                     */
/*    Alastair Reid,                                                          */
/*    Peter Sewell                                                            */
/*                                                                            */
/*  All rights reserved.                                                      */
/*                                                                            */
/*  Redistribution and use in source and binary forms, with or without        */
/*  modification, are permitted (subject to the limitations in the            */
/*  disclaimer below) provided that the following conditions are met:         */
/*                                                                            */
/*    * Redistributions of source code must retain the above copyright        */
/*      notice, this list of conditions and the following disclaimer.         */
/*    * Redistributions in binary form must reproduce the above copyright     */
/*      notice, this list of conditions and the following disclaimer in the   */
/*      documentation and/or other materials provided with the distribution.  */
/*    * Neither the name of ARM Limited nor the names of its contributors     */
/*      may be used to endorse or promote products derived from this          */
/*      software without specific prior written permission.                   */
/*                                                                            */
/*  NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED   */
/*  BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND   */
/*  CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,    */
/*  BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND         */
/*  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE   */
/*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT  */
/*  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON    */
/*  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT   */
/*  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF  */
/*  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.         */
/******************************************************************************/

// Redirect memory primitives to Sail builtins

val __write_tag_bool = { c: "write_tag_bool", ocaml: "write_tag_bool" } : (bits(64), bool) -> unit effect {wmvt}
val __read_tag_bool = { c: "read_tag_bool", ocaml: "read_tag_bool" } : bits(64) -> bool effect {rmemt}

val __ReadMem
  = { ocaml: "Platform.read_mem", c: "platform_read_mem", _: "read_mem" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n) effect {rmem}

val __ReadTaggedMem
  = { lem: "read_memt", coq: "read_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit) effect {rmemt}

function __ReadTaggedMem(rk, addr, size) = {
  // Address is aligned to capability size at this point
  assert(addr == Align(addr, CAPABILITY_DBYTES));
  let tag = (if __read_tag_bool(ZeroExtend(addr)) then bitone else bitzero);
  let data : bits(8 * 'n) = match('addrsize) {
    32 => __ReadMem(rk, 32, addr, size),
    64 => __ReadMem(rk, 64, addr, size)
  };
  return (data, tag)
}

val __WriteTaggedMem
  = { lem: "write_memt", coq: "write_memt" }
  : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool effect {wmvt}

function __WriteTaggedMem(wk, addr, size, data, tag) = {
  // Address is aligned to capability size at this point
  assert(addr == Align(addr, CAPABILITY_DBYTES));
  __write_tag_bool(ZeroExtend(addr), (tag == bitone));
  match('addrsize) {
    32 => __write_mem(wk, 32, addr, size, data),
    64 => __write_mem(wk, 64, addr, size, data)
  }
}

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
  __write_tag_bool(ZeroExtend(tag_addr), false);
  match('addrsize) {
    32 => __write_mem(wk, 32, addr, size, data),
    64 => __write_mem(wk, 64, addr, size, data)
  }
}

val acctype_to_read_kind : AccType -> read_kind

function acctype_to_read_kind(acctype) = {
    match acctype {
        AccType_NORMAL => Read_plain,
        AccType_IFETCH => Read_ifetch,
        AccType_ORDERED => Read_acquire,
        AccType_ATOMIC => Read_exclusive,
        AccType_ATOMICRW => Read_exclusive,
        AccType_ORDEREDATOMIC => Read_exclusive_acquire,
        AccType_ORDEREDATOMICRW => Read_exclusive_acquire,
        _ => Read_plain
    }
}

$ifdef HAVE_DEVICES
function _Mem_read (desc, size, accdesc) = {
  let paddress = desc.paddress.address;
  if (size >= 4 & paddress[(length(paddress) - 1) .. 16] == ZeroExtend(GIC_BASE)) then {
    // TODO: Pass read kind?
    ZeroExtend(__ReadGIC(paddress[15 .. 0]), 8 * size);
  } else if (paddress[(length(paddress) - 1) .. 16] == ZeroExtend(UART_BASE)) then {
    __ReadUART(paddress[15 .. 0], size);
  } else {
    __ReadMem(acctype_to_read_kind(accdesc.acctype), 64, ZeroExtend(paddress, 64), size)
  }
}
$else
function _Mem_read (desc, size, accdesc) = {
  __ReadMem(acctype_to_read_kind(accdesc.acctype), 64, ZeroExtend(desc.paddress.address, 64), size)
}
$endif

function _ReadMem (desc, size, accdesc) = _Mem_read(desc, size, accdesc)

val acctype_to_write_kind : AccType -> write_kind

function acctype_to_write_kind(acctype) = {
    match acctype {
        AccType_ORDERED => Write_release,
        AccType_ATOMIC => Write_exclusive,
        AccType_ATOMICRW => Write_exclusive,
        AccType_ORDEREDATOMIC => Write_exclusive_release,
        AccType_ORDEREDATOMICRW => Write_exclusive_release,
        _ => Write_plain
    }
}

$ifdef HAVE_DEVICES
function _Mem_set (desc, size, accdesc, data) = {
  let paddress = desc.paddress.address;
  //prerr_endline("[Sail] Write to address " ++ bits_str(paddress) ++ ": " ++ bits_str(data));
  if (size == 4 & paddress[(length(paddress) - 1) .. 16] == ZeroExtend(GIC_BASE)) then {
  // if (size == 4 & paddress[31 .. 16] == GIC_BASE) then {
    __WriteGIC(paddress[15 .. 0], data)
  } else if (paddress[(length(paddress) - 1) .. 16] == ZeroExtend(UART_BASE)) then {
  // } else if (paddress[31 .. 16] == UART_BASE) then {
    __WriteUART(paddress[15 .. 0], size, data)
  } else {
    let _ = __WriteMem(acctype_to_write_kind(accdesc.acctype), 64, ZeroExtend(paddress, 64), size, data);
    ()
  }
}
$else
function _Mem_set (desc, size, accdesc, data) = {
  let _ = __WriteMem(acctype_to_write_kind(accdesc.acctype), 64, ZeroExtend(desc.paddress.address, 64), size, data);
  ()
}
$endif

function _ReadTaggedMem(desc, size, accdesc) = {
  let rkind = acctype_to_read_kind(accdesc.acctype);
  if size == 16 then {
    let (data, tag) = __ReadTaggedMem(rkind, ZeroExtend(desc.paddress.address, 64), 16);
    return (Bits(tag), data)
  } else {
    // TODO: Endianness?
    let (data1, tag1) = __ReadTaggedMem(rkind, ZeroExtend(desc.paddress.address, 64), 16);
    let (data2, tag2) = __ReadTaggedMem(rkind, ZeroExtend(desc.paddress.address, 64) + 16, 16);
    return (Bits(tag1) @ Bits(tag2), data1 @ data2)
  }
}

function _WriteTaggedMem (desc, size, accdesc, tags, data) = {
  let wkind = acctype_to_write_kind(accdesc.acctype);
  if size == 16 then {
    let _ = __WriteTaggedMem(wkind, ZeroExtend(desc.paddress.address, 64), 16, data, tags[0]);
    ()
  } else {
    // TODO: Endianness?
    let _ = __WriteTaggedMem(wkind, ZeroExtend(desc.paddress.address, 64), 16, data[127..0], tags[0]);
    let _ = __WriteTaggedMem(wkind, ZeroExtend(desc.paddress.address, 64) + 16, 16, data[255..128], tags[1]);
    ()
  }
}

// TODO: Are the kinds from accdesc descriptor the right things to use here?

function _ReadTags (desc, size, accdesc) = {
  let rkind = acctype_to_read_kind(accdesc.acctype);
  let paddress = desc.paddress.address;
  tags : bits('size) = Zeros(size);
  foreach (i from 0 to (size - 1) by 1 in inc) {
    let (_, tag) = __ReadTaggedMem(rkind, ZeroExtend(paddress, 64) + (i * 16), 16);
    tags[i] = tag;
  };
  return(tags)
}

function _WriteTags (desc, size, tags, accdesc) = {
  let wkind = acctype_to_write_kind(accdesc.acctype);
  let paddress = desc.paddress.address;
  foreach (i from 0 to (size - 1) by 1 in inc) {
    // TODO: Add a builtin function for writing just tags:
    // let _ = __write_tag(Write_plain, ZeroExtend(paddress, 64) + (i * 16), 16, tags[i]);
    let data = __ReadMem(Read_plain, 64, ZeroExtend(paddress, 64) + (i * 16), 16);
    let _ = __WriteTaggedMem(wkind, ZeroExtend(paddress, 64) + (i * 16), 16, data, tags[i]);
    ()
  }
}
