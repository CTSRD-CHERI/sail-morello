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

$define HAVE_DEVICES

let UART_BASE = 0x3c00

let GIC_BASE = 0x2c00

// Interrupt Controller Type Register
//                                  SecurityExtn  CPUNumber       ITLinesNumber
// let GICD_TYPER = [Zeros(32) with 10 = bitzero, 7 .. 5 = 0b000, 4 .. 0 = 0b00111]
let GICD_TYPER = [[Zeros(32) with 10 .. 10 = 0b1] with 4 .. 0 = 0b00111]

// CPU Interface Control Register
register GICC_CTLR : bits(32)

// CPU Interface Identification Register
// 0x0002 = GICv2, 0x043B = Pretend to be ARM implementation (JEP106 code).
let GICC_IIDR = 0x0002_043B

function gic_readonly(offset : bits(16)) -> unit = {
  prerr_bits("[GIC] Write to RO offset: ", offset);
}

register __GIC_Pending : bits(32)

let GIC_PENDING_NONE : bits(32) = 0x0000_03ff

function __GIC_InterruptPending(() : unit) -> bool = (__GIC_Pending != GIC_PENDING_NONE)

// gic_{read,write}_ram() simply forward a request for a GIC address to memory.
function gic_read_ram(offset : bits(16)) -> bits(32) = {
  __read_mem(Read_plain, 64, ZeroExtend(GIC_BASE @ offset, 64), 4)
}

function gic_write_ram(offset : bits(16), data : bits(32)) -> unit = {
  let success = __write_mem(Write_plain, 64, ZeroExtend(GIC_BASE @ offset, 64), 4, data);
  ()
}

function HighestPendingInterrupt(() : unit) -> bits(32) = {
  let intID = __GIC_Pending;
  __GIC_Pending = GIC_PENDING_NONE;
  intID
}

val __ReadGIC : bits(16) -> bits(32) effect {rmem, rreg}

function __ReadGIC(offset) = {
  match offset {
    // ***** Distributor Interface *****
    0x1004 => GICD_TYPER,

    // Send all interrupts to CPU interface 0
    0x1800 => 0xffffffff,

    0x1C04 => {
      prerr_bits("[GIC] Read 1C04: ", gic_read_ram(0x1C04));
      gic_read_ram(0x1C04) // Linux timer
    },

    // ***** CPU Interface 0 *****
    0x2000 => {
      prerr_bits("[GIC] Read GICC_CTLR ", GICC_CTLR);
      GICC_CTLR
    },
    0x200C => {
       prerr_bits("[GIC] Request for highest pending interrupt ", __GIC_Pending);
       HighestPendingInterrupt()
    },
    0x20FC => GICC_IIDR,

    _ => {
      prerr_bits("[GIC] Read offset: ", offset);
      Zeros(32)
    }
  }
}

val __WriteGIC : (bits(16), bits(32)) -> unit effect {wmem, wreg}

function __WriteGIC(offset, data) = {
  match offset {
    // ***** Distributor Interface *****
    0x1004 => gic_readonly(offset),

    0x1100 => {
      prerr_bits("[GIC] Registering interrupts ", data);
      let intID = HighestSetBit(data);
      prerr_int("[GIC] Registering interrupt ", intID)
    },

    0x1800 => gic_readonly(offset),

    // ***** CPU Interface 0 *****
    0x2000 => {
      prerr_bits("[GIC] GICC_CTLR = ", data);
      GICC_CTLR = data
    },
    0x200C => gic_readonly(offset),
    0x20FC => gic_readonly(offset),

    0x2010 => {
      prerr_bits("[GIC] End of interrupt = ", data);
      __GIC_Pending = GIC_PENDING_NONE
    },

    0x3000 => {
      prerr_endline("[GIC] Deactivating interrupt");
      __GIC_Pending = GIC_PENDING_NONE
    },

    // We don't exhaustively model the GIC, so log and forward unrecognised writes to memory
    _ => {
      prerr_bits("[GIC] Unknown write offset: ", offset);
      prerr_bits("[GIC] Unknown write data: ", data);
      // TODO: Tag clearing
      // gic_write_ram(offset, data)
    }
  }
}

val __ReadUART : forall 'n, 'n > 0. (bits(16), int('n)) -> bits(8 * 'n)

function __ReadUART(offset, n) = {
  match offset {
    _ => {
      prerr_bits("[UART] Unknown read offset: ", offset);
      Zeros(8 * n)
    }
  }
}

val __WriteUART : forall 'n, 'n > 0. (bits(16), int('n), bits(8 * 'n)) -> unit

function __WriteUART(offset, n, data) = {
  match offset {
    0x0000 => {
      putchar(UInt(data[7 .. 0]));
    },

    _ => {
      prerr_bits("[UART] Unknown write offset: ", offset);
      prerr_bits("[UART] Unknown write data: ", data);
    }
  }
}

val Init_Devices : unit -> unit effect {wreg}

function Init_Devices() = {
  __GIC_Pending = GIC_PENDING_NONE
}
