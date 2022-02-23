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

function HaveFP16Ext() = true
function HasArchVersion(version) = {
  match(version) {
    ARMv8p0 => true,
    ARMv8p1 => true,
    ARMv8p2 => true,
    _ => false
  }
}
function HaveAArch32EL(el) = false
function HaveAnyAArch32() = false
function HaveEL(el) = true
function HighestELUsingAArch32() = false

function ProcessorID() = 0
function IsExclusiveGlobal(paddress, processorid, size) = true
function IsExclusiveLocal(paddress, processorid, size) = true
function AArch64_IsExclusiveVA(address, processorid, size) = true
function AArch64_MarkExclusiveVA(address, processorid, size) = ()
function ExclusiveMonitorsStatus() = 0b0

val AArch64_IMPDEFResets : unit -> unit effect {rreg, wreg}

function AArch64_IMPDEFResets () = {
    DCZID_EL0 = SetSlice(1, DCZID_EL0, 4, 0b0);
    DCZID_EL0 = SetSlice(4, DCZID_EL0, 0, 0b0100);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 36, 0b1111);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 32, 0b0000);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 28, 0b1111);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 20, 0b1111);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 12, 0b1111);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 4, 0b0000);
    ID_AA64DFR0_EL1 = SetSlice(4, ID_AA64DFR0_EL1, 0, 0b1001);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 44, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 40, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 36, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 32, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 28, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 20, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 16, 0b0000);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 12, 0b0001);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 8, 0b0001);
    ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0010);
    ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 0, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 28, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 24, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 20, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 16, 0b0000);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 12, 0b0001);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 8, 0b0000); // Morello has no mixed-endian support
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 4, 0b0010);
    ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 0, 0b0101);
    ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 16, 0b0001); // 52-bit VA support
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 28, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 24, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 16, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 8, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 4, 0b0000);
    ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 0, 0b0000);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 32, 0b0001);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 28, 0b0001); // RAS, to match Morello (8.2 mandatory too)
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 12, 0b0001); // AArch64 only, changed to match Morello
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 8, 0b0001); // AArch64 only, changed to match Morello
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 4, 0b0001); // AArch64 only, changed to match Morello
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 0, 0b0001); // AArch64 only, changed to match Morello
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 24, 0b0000); // In this model, no system register interface to the GIC is supported
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 20, 0b0000);
    ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 16, 0b0000);
    MPIDR_EL1[31 .. 0] = CFG_MPIDR;
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 32, 0b00000000);
    VMPIDR_EL2 = SetSlice(1, VMPIDR_EL2, 30, 0b0);
    VMPIDR_EL2 = SetSlice(1, VMPIDR_EL2, 24, 0b0);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 16, 0b00000000);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 8, 0b00000000);
    VMPIDR_EL2 = SetSlice(8, VMPIDR_EL2, 0, 0b00000000);
    if HasArchVersion(ARMv8p1) then {
        ID_ISAR5_EL1 = SetSlice(4, ID_ISAR5_EL1, 24, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 20, 0b0010);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 28, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 16, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 8, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 0, 0b0010)
    };
    if __crc32_implemented then {
        ID_ISAR5_EL1 = SetSlice(4, ID_ISAR5_EL1, 16, 0b0001);
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 16, 0b0001)
    };
    if __vmid16_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 4, 0b0010)
    };
    if __pan_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0001);
        ID_MMFR3_EL1 = SetSlice(4, ID_MMFR3_EL1, 16, 0b0001)
    };
    if __crypto_aes_implemented == 0 then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0000)
    };
    if __crypto_aes_implemented == 1 then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 4, 0b0001)
    };
    if not_bool(__crypto_sha1_implemented) then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 8, 0b0000)
    };
    if not_bool(__crypto_sha256_implemented) then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 12, 0b0000)
    };
    if HasArchVersion(ARMv8p2) then {
        if __support_52bit_pa then {
            ID_AA64MMFR0_EL1 = SetSlice(4, ID_AA64MMFR0_EL1, 0, 0b0110)
        };
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 28, 0b0001);
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 20, 0b0010);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 0, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 4, 0b0001);
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 8, 0b0001);
        if __support_52bit_va then {
            ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 16, 0b0001)
        };
        ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 12, 0b0001);
        ID_MMFR3_EL1 = SetSlice(4, ID_MMFR3_EL1, 16, 0b0010);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 8, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 12, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 20, 0b0001);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 4, 0b0001);
        if HaveEL(EL2) then {
            ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 28, 0b0010);
            ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 56, 0b0010)
        } else {
            ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 28, 0b0000);
            ID_AA64MMFR2_EL1 = SetSlice(4, ID_AA64MMFR2_EL1, 56, 0b0000)
        };
        ID_AA64ISAR1_EL1 = SetSlice(4, ID_AA64ISAR1_EL1, 0, 0b0001);
        ID_ISAR6_EL1 = SetSlice(4, ID_ISAR6_EL1, 4, 0b0001)
    };
    if __dot_product_implemented then {
        ID_AA64ISAR0_EL1 = SetSlice(4, ID_AA64ISAR0_EL1, 44, 0b0001)
    };
    if __fp16_implemented then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 16, 0b0001);
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 20, 0b0001)
    };
    if __aa32_hpd_implemented then {
        ID_AA64MMFR1_EL1 = SetSlice(4, ID_AA64MMFR1_EL1, 12, 0b0010);
        ID_MMFR4_EL1 = SetSlice(4, ID_MMFR4_EL1, 16, 0b0010)
    };
    if __mpam_implemented then {
        ID_AA64PFR0_EL1 = SetSlice(4, ID_AA64PFR0_EL1, 40, CFG_ID_AA64PFR0_EL1_MPAM);
        MPAMIDR_EL1 = SetSlice(16, MPAMIDR_EL1, 0, __mpam_partid_max);
        MPAMIDR_EL1 = SetSlice(8, MPAMIDR_EL1, 32, __mpam_pmg_max);
        if __mpam_has_hcr then {
            MPAMIDR_EL1 = SetSlice(1, MPAMIDR_EL1, 17, 0b1);
            MPAMIDR_EL1 = SetSlice(3, MPAMIDR_EL1, 18, __mpam_vpmr_max)
        }
    };
    SCR_EL3 = SetSlice(1, SCR_EL3, 15, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 14, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 13, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 12, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 11, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 10, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 9, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 8, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 7, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 3, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 2, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 1, 0b0);
    SCR_EL3 = SetSlice(1, SCR_EL3, 0, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, 31, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, if HaveVirtHostExt() & Slice(HCR_EL2, 34, 1) == 0b1 then 28 else 20, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, 10, 0b0);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, 8, 0b1);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, 31, 0b1);
    CPTR_EL2 = SetSlice(1, CPTR_EL2, if HaveVirtHostExt() & Slice(HCR_EL2, 34, 1) == 0b1 then 28 else 20, 0b1);
    CPTR_EL2 = SetSlice(2, CPTR_EL2, 20, 0b11);
    CPTR_EL2 = SetSlice(2, CPTR_EL2, 16, 0b11);
    HCR_EL2 = SetSlice(1, HCR_EL2, 49, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 52, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 50, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 38, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 37, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 36, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 35, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 34, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 33, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 32, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 31, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 30, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 29, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 28, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 27, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 26, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 25, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 24, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 23, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 22, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 21, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 20, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 19, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 18, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 17, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 16, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 15, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 14, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 13, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 12, 0b0);
    HCR_EL2 = SetSlice(2, HCR_EL2, 10, 0b00);
    HCR_EL2 = SetSlice(1, HCR_EL2, 9, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 8, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 7, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 6, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 5, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 4, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 3, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 2, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 1, 0b0);
    HCR_EL2 = SetSlice(1, HCR_EL2, 0, 0b0);
    HSTR_EL2 = SetSlice(16, HSTR_EL2, 0, Zeros());
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 25, 0b0);
    SCTLR_EL2 = SetSlice(1, SCTLR_EL2, 25, 0b0);
    CPACR_EL1 = SetSlice(1, CPACR_EL1, 28, 0b0);
    CPACR_EL1 = SetSlice(2, CPACR_EL1, 20, 0b00);
    CPACR_EL1 = SetSlice(2, CPACR_EL1, 16, 0b00);
    SCTLR_EL1 = SetSlice(1, SCTLR_EL1, 25, 0b0);
    SCTLR_EL3 = SetSlice(1, SCTLR_EL3, 25, 0b0);
    MDCR_EL2 = SetSlice(1, MDCR_EL2, 14, 0b0);
    MDCR_EL2 = SetSlice(2, MDCR_EL2, 12, 0b10);
    ICC_SRE_EL3 = SetSlice(1, ICC_SRE_EL3, 0, 0b1);
    ICC_SRE_EL3 = SetSlice(1, ICC_SRE_EL3, 3, 0b1);
    ICC_SRE_EL2 = SetSlice(1, ICC_SRE_EL2, 0, 0b1);
    ICC_SRE_EL1_S = SetSlice(1, ICC_SRE_EL1_S, 0, 0b1);
    ICC_SRE_EL1_NS = SetSlice(1, ICC_SRE_EL1_NS, 0, 0b1);
    CTR_EL0 = SetSlice(4, CTR_EL0, 20, __exclusive_granule_size);
    CCSIDR_EL1 = SetSlice(15, CCSIDR_EL1, 13, ZeroExtend(0xFF, 15));
    CCSIDR_EL1 = SetSlice(10, CCSIDR_EL1, 3, ZeroExtend(0x1, 10));
    CCSIDR_EL1 = SetSlice(3, CCSIDR_EL1, 0, 0b010);
    ERRIDR_EL1 = SetSlice(16, ERRIDR_EL1, 0, 0x0002);
    return()
}

function AArch64_ResetControlRegisters(cold) = {
  AArch64_AutoGen_ArchitectureReset(cold);
}

// The maximum capability CMAX is defined in rule VFMMV of the Morello spec as
// a capability with maximum bounds and capabilities, but without giving a
// concrete bit representation.  The representation below is copied from the
// reset value for DDC_EL0 given in §3.2.16.
let CMAX : Capability = truncate(0x1FFFFC000000100050000000000000000, 129)

function TakeReset(cold) = {
  RVBAR_EL3 = CFG_RVBAR;
  PCC = CMAX;
  EDSCR[5 .. 0] = 0b000010;  // Non-debug state
  AArch64_TakeReset(cold);
  AArch64_IMPDEFResets();
}
