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

val read_register = "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

val Step_PC : unit -> unit effect {escape, undef, wreg, rreg}

function Step_PC() = {
  if not_bool(__BranchTaken) then {
    PCC = CapAdd__1(PCC, DIV(ThisInstrLength(), 8));
    _PC = CapGetValue(PCC);
  };
  SSAdvance();
}

// Advance CPU by one cycle
val Step_CPU : unit -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

function Step_CPU() = {
  var fetch_ok : bool = false;
  var oldPC : bits(64) = _PC;
  var opcode : bits(32) = Zeros(32);
  try {
    opcode = __FetchNextInstr();
    __SetThisInstr(opcode);
    fetch_ok = true;
    if (__GetVerbosity()[1] == bitone) then {
      prerr_endline("[Sail] IFetch from PC=" ++ bits_str(oldPC) ++ " in cycle=" ++ DecStr(get_cycle_count()) ++ ": " ++ bits_str(opcode));
    };
  } catch {
    Error_ExceptionTaken() => {
      print("Exception taken during IFetch from PC=" ++ bits_str(oldPC) ++ " ESR=" ++ bits_str(ESR_read__1()) ++ " FAR=" ++ bits_str(FAR_read__1()) ++ " cycle=" ++ DecStr(get_cycle_count()) ++ "\n");
    },
    _ => {
      print("Exiting due to unhandled exception in IFetch\n");
      exit()
    }
  };

  // Use a magic instruction to kill the simulator in init
  if opcode == 0xfee1dead then {
    print("[Sail] Finished Successfully!\n");
    exit()
  };

  if fetch_ok then {
    try {
      __BranchTaken = false;
      __DecodeA64(UInt(_PC), opcode);
    } catch {
      Error_Undefined()         => try { UndefinedFault() } catch { _ => prerr_endline("Exception during Undefined recovery at PC=" ++ bits_str(oldPC) ++ " instr=" ++ bits_str(opcode)) },
      Error_See(_) => {
	print("Unexpected SEE, exiting.\n");
        exit()
      },
      Error_ReservedEncoding(_) => try { UndefinedFault() } catch { _ => prerr_endline("Exception during ReservedEncoding recovery") },
      Error_ExceptionTaken() => {
        prerr_endline("Exception taken during Decode/Execute from PC=" ++ bits_str(oldPC) ++ " ESR=" ++ bits_str(ESR_read__1()) ++ " FAR=" ++ bits_str(FAR_read__1()) ++ " cycle=" ++ DecStr(get_cycle_count()));
        // print("  This might just be a HINT like 0xd50320df\n");
      },
      Error_ImplementationDefined(s) => {
        print(concat_str("IMPLEMENTATION_DEFINED ",
              concat_str(s,
              "\n")));
        exit();
      }
    };
    Step_PC();
  };
}

//             EL1 physical        EL2 physical        EL3 physical        EL1 virtual,       EL2 virtual
let CNT_CVAL = [ref CNTP_CVAL_EL0, ref CNTHP_CVAL_EL2, ref CNTPS_CVAL_EL1, ref CNTV_CVAL_EL0, ref CNTHV_CVAL_EL2]
let CNT_TVAL = [ref CNTP_TVAL_EL0, ref CNTHP_TVAL_EL2, ref CNTPS_TVAL_EL1, ref CNTV_TVAL_EL0, ref CNTHV_TVAL_EL2]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_IRQ  = [0x0000_000d,       0x0000_000a,        0x0000_03ff,        0x0000_000b,       0x0000_03ff       ]
//                                                     No IRQ                                 No IRQ?

// SGI Interrupts are 0-15, PPI interrupts are 16-31, and SPI interrupts have an offset of 32.
let PPI_OFFSET = 16

let ISTATUS = 0x0000_0004
let IMASK = 0x0000_0002

val Init_Timers : unit -> unit effect {rreg, wreg}

function Init_Timers() = {
  foreach (timer from 0 to 4 by 1 in inc) {
    let CTL = CNT_CTL[timer];
    (*CTL) = ZeroExtend(0x0, 32)
  };
}

// Advance Timers by one cycle
val Step_Timers : unit -> unit effect {escape, undef, wreg, rreg}

function Step_Timers() = {
  // Increment the counter
  CNTPCT_EL0 = CNTPCT_EL0 + 1;
  CNTVCT_EL0 = CNTPCT_EL0 - CNTVOFF_EL2;

  // Timer value view for each timer
  foreach (timer from 0 to 4) {
    let CTL = CNT_CTL[timer];
    let ctl = read_register(CTL);
    // prerr_endline("[Clock] CTL[" ++ DecStr(timer) ++ "] = " ++ bits_str(ctl));

    // If the timer is enabled
    if ctl[0] == bitone then {
      let TVAL = CNT_TVAL[timer];
      // prerr_endline("[Clock] TVAL[" ++ DecStr(timer) ++ "] = " ++ bits_str(read_register(TVAL)));
      let nextTVAL = read_register(TVAL) - 1;
      (*TVAL) = nextTVAL;

      // If the timer condition is met
      if nextTVAL == 0x0000_0000 then {
	prerr_int("[Clock] Tick (TVAL) ", timer);
	(*CTL) = ctl | ISTATUS // Set the ISTATUS bit
      };

      if SInt(nextTVAL) <= 0 then {
	 /* IMASK unset         interrupts unmasked */
	 if ctl[1] == bitzero & PSTATE.I == 0b0 then {
	   __GIC_Pending = CNT_IRQ[timer] + PPI_OFFSET;
	   prerr_bits("[Clock] GIC interrupt ", __GIC_Pending);
	   AArch64_TakePhysicalIRQException()
	 }
      } else {
	(*CTL) = ctl & not_vec(ISTATUS)
      }
    }
  };
}

val Step_System : unit -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

function Step_System() = {
  try {
    Step_Timers();
  } catch {
    _ => {
      prerr_endline(concat_str("Exception taken during Step_Timers.  PC=",
                    concat_str(HexStr(UInt(_PC)),
                    concat_str(" cycle=",
                    concat_str(DecStr(get_cycle_count()),
                    "\n")))));
    }
  };

  var prevEL = PSTATE.EL;
  var prevI = PSTATE.I;

  // Store the old values of the Counter-timer Kernel/Hypervisor Control
  // registers, as we want to figure out when they changes.
  var prevCNTKCTL_EL1 = CNTKCTL_EL1;
  var prevCNTHCTL_EL2 = CNTHCTL_EL2;

  try {
    Step_CPU();
  } catch {
    _ => {
      prerr_endline(concat_str("Exception taken during Step_CPU.  PC=",
                    concat_str(HexStr(UInt(_PC)),
                    concat_str(" cycle=",
                    concat_str(DecStr(get_cycle_count()),
                    "\n")))));
    }
  };

  // We want to keep track of what exception level we are in for debugging purposes.
  if UInt(prevEL) != UInt(PSTATE.EL) then {
    prerr_bits(concat_str("[Sail] ",
               concat_str(DecStr(get_cycle_count()),
               " Exception level changed to: ")),
               PSTATE.EL);
  };
  if prevI != PSTATE.I then {
    prerr_bits("[Sail] PSTATE.I changed to: ", PSTATE.I);
    prerr_endline(concat_str("   at PC=",
                  concat_str(HexStr(UInt(_PC)),
                  concat_str(" in cycle=",
                  concat_str(DecStr(get_cycle_count()),
                  "\n")))));
  };
  if prevCNTKCTL_EL1 != CNTKCTL_EL1 then {
    prerr_bits("[Clock] CNTKCTL_EL1 changed to ", CNTKCTL_EL1);
  };
  if prevCNTHCTL_EL2 != CNTHCTL_EL2 then {
    prerr_bits("[Clock] CNTHCTL_EL2 changed to ", CNTHCTL_EL2);
  }
}

val __InitSystem : unit -> unit effect {wreg, rreg}

function __InitSystem() = {
  DBGEN = LOW;
  TakeReset(true);
  Init_Timers();
  Init_Devices();
}

// Simple top level fetch and execute function.
val __TopLevel : unit -> unit effect {configuration, escape, undef, wreg, rreg, rmem, wmem}

function __TopLevel () = {
  try {
    Step_System();
    __EndCycle();
  } catch {
    Error_ExceptionTaken(_) => {
      // enable_tracing()
      prerr_endline(concat_str("Exception taken during Step_System.  PC=",
                    concat_str(HexStr(UInt(_PC)),
                    concat_str(" cycle=",
                    concat_str(DecStr(get_cycle_count()),
                    "\n")))));
      ()
    },
    _ => {
      prerr_endline("Exiting due to unhandled exception\n");
      exit()
    }
  };
}

val __CycleEnd : unit -> unit

function __CycleEnd() = __EndCycle()
