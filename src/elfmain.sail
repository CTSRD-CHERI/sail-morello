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

$include <elf.sail>

let COLD_RESET : bool = true

val main : unit -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

val get_cycle_count = { c: "get_cycle_count" } : unit -> int effect {undef, wreg, rreg, rmem, wmem}
val check_cycle_count = { c: "cycle_count" } : unit -> unit
val __GetVerbosity = {c: "sail_get_verbosity"}: unit -> bits(64) effect {rreg, undef}

val step_model : unit -> unit effect {escape}

function step_model() = {
  SEE = -1;
  __TopLevel();
  __CycleEnd();
  ()
}

function main() = {
  try {
    let verbosity = __GetVerbosity();
    __InitSystem();
    while true do {
      if verbosity[0] == bitone then {
          nzcv = (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V);
          print(concat_str("[Sail] ",
                concat_str(DecStr(get_cycle_count()),
                concat_str(" PC=",
                concat_str(HexStr(UInt(_PC)),
                concat_str(" NZCV=",
                concat_str(HexStr(UInt(nzcv)),
                "\n")))))));
      };
      step_model();
      if verbosity[1] == bitone then {
          print(concat_str("[Sail] Instr=",
                concat_str(HexStr(UInt(__ThisInstr)),
                concat_str(" ESR_EL3=",
                concat_str(HexStr(UInt(ESR_EL3)),
                concat_str(if __BranchTaken then " branch taken" else "",
                "\n"))))));
      };
      check_cycle_count();
    }
  } catch {
    Error_ImplementationDefined(s) => {
      print_endline(concat_str("Unsupported implementation defined behaviour: ", s));
    }
  }
}

// Separate entry point for isla_footprint

val isla_reset_registers = "reset_registers" : unit -> unit

val isla_footprint_no_init : bits(32) -> bool effect {configuration, escape, rmem, rreg, undef, wmem, wreg}

function isla_footprint_no_init(opcode) = {
  SEE = -1;

  __BranchTaken = false;
  __ThisInstr = opcode;
  DBGEN = LOW;

  isla_reset_registers();

  __ThisInstrEnc = __A64;
  __ThisInstr = opcode;

  // The first cycle during footprint analysis is reserved for initialization, and ignored.
  check_cycle_count();
  try {
    __DecodeA64(UInt(_PC), opcode);
    Step_PC();
    true
  } catch {
    _ => false
  }
}

val isla_footprint : bits(32) -> bool effect {configuration, escape, rmem, rreg, undef, wmem, wreg}

function isla_footprint(opcode) = {
  __highest_el_aarch32 = false;
  TakeReset(COLD_RESET);
  AArch64_ResetGeneralRegisters();
  PSTATE.EL = EL0;

  _R00 = undefined;
  _R01 = undefined;
  _R02 = undefined;
  _R03 = undefined;
  _R04 = undefined;
  _R05 = undefined;
  _R06 = undefined;
  _R07 = undefined;
  _R08 = undefined;
  _R09 = undefined;
  _R10 = undefined;
  _R11 = undefined;
  _R12 = undefined;
  _R13 = undefined;
  _R14 = undefined;
  _R15 = undefined;
  _R16 = undefined;
  _R17 = undefined;
  _R18 = undefined;
  _R19 = undefined;
  _R20 = undefined;
  _R21 = undefined;
  _R22 = undefined;
  _R23 = undefined;
  _R24 = undefined;
  _R25 = undefined;
  _R26 = undefined;
  _R27 = undefined;
  _R28 = undefined;
  _R29 = undefined;
  _R30 = undefined;

  isla_footprint_no_init(opcode)
}
