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

function _TLB_Invalidate () = {
    TLBReset();
    return()
}

function __SAVE_EL __new_exception_level = {
    __saved_exception_level = PSTATE.EL;
    PSTATE.EL = __new_exception_level
}

function __RESTORE_EL () = {
    PSTATE.EL = __saved_exception_level
}

function AArch64_PARFaultStatus fault = {
    fst : bits(6) = undefined;
    if fault.statuscode == Fault_Domain then {
        assert(fault.level == 1 | fault.level == 2);
        fst[1 .. 0] = if fault.level == 1 then 0b01 else 0b10;
        fst[5 .. 2] = 0b1111
    } else {
        fst = EncodeLDFSC(fault.statuscode, fault.level)
    };
    return(fst)
}

function PARAttrsDecode memattrs = {
    result : bits(8) = undefined;
    if memattrs.memtype == MemType_Device then {
        result[7 .. 4] = 0b0000;
        if memattrs.device == DeviceType_nGnRnE then {
            result[3 .. 0] = 0b0000
        } else if memattrs.device == DeviceType_nGnRE then {
            result[3 .. 0] = 0b0100
        } else if memattrs.device == DeviceType_nGRE then {
            result[3 .. 0] = 0b1000
        } else {
            result[3 .. 0] = 0b1100
        }
    } else {
        if memattrs.outer.attrs == MemAttr_WT then {
            result[7 .. 6] = if memattrs.outer.transient then 0b00 else 0b10;
            result[5 .. 4] = memattrs.outer.hints
        } else if memattrs.outer.attrs == MemAttr_WB then {
            result[7 .. 6] = if memattrs.outer.transient then 0b01 else 0b11;
            result[5 .. 4] = memattrs.outer.hints
        } else {
            result[7 .. 4] = 0b0100
        };
        if memattrs.inner.attrs == MemAttr_WT then {
            result[3 .. 2] = if memattrs.inner.transient then 0b00 else 0b10;
            result[1 .. 0] = memattrs.inner.hints
        } else if memattrs.inner.attrs == MemAttr_WB then {
            result[3 .. 2] = if memattrs.inner.transient then 0b01 else 0b11;
            result[1 .. 0] = memattrs.inner.hints
        } else {
            result[3 .. 0] = 0b0100
        }
    };
    return(result)
}

function PARShareabilityDecode memattrs = {
    result : bits(2) = undefined;
    if memattrs.outer.attrs == MemAttr_NC & memattrs.inner.attrs == MemAttr_NC | memattrs.outershareable then {
        result = 0b10
    } else if memattrs.shareable then {
        result = 0b11
    } else {
        result = 0b00
    };
    return(result)
}

function AArch64_EncodePAR addrdesc = {
    par : bits(64) = ZeroExtend(0x800, 64);
    if not_bool(IsFault(addrdesc)) then {
        par[0] = Bit(0b0);
        par[8 .. 7] = PARShareabilityDecode(addrdesc.memattrs);
        par[9] = Bit(addrdesc.paddress.NS);
        par[48 - 1 .. 12] = addrdesc.paddress.address[48 - 1 .. 12];
        par[63 .. 56] = PARAttrsDecode(addrdesc.memattrs)
    } else {
        par[0] = Bit(0b1);
        par[6 .. 1] = AArch64_PARFaultStatus(addrdesc.fault);
        par[8] = Bit(if addrdesc.fault.s2fs1walk then 0b1 else 0b0);
        par[9] = Bit(if addrdesc.fault.secondstage then 0b1 else 0b0)
    };
    PAR_EL1[63 .. 0] = par
}

function AArch64_AT_S1Ex (val_name, el, iswrite) = {
    __SAVE_EL(el);
    let addrdesc : AddressDescriptor = AArch64_FirstStageTranslate(val_name, AccType_AT, iswrite, true, 1);
    __RESTORE_EL();
    if IsFault(addrdesc) then {
        if IsExternalAbort__1(addrdesc.fault) | (PSTATE.EL == EL1 & EL2Enabled()) & addrdesc.fault.s2fs1walk then {
            PAR_EL1 = __UNKNOWN_bits(64);
            AArch64_Abort(val_name, addrdesc.fault)
        } else ()
    } else ();
    AArch64_EncodePAR(addrdesc)
}

function AArch64_AT_S12Ex (val_name, el, iswrite) = {
    has_s2_translation : bool = undefined;
    if HaveEL(EL3) then {
        has_s2_translation = HaveEL(EL2) & Slice(SCR_EL3, 0, 1) == 0b1
    } else {
        has_s2_translation = HaveEL(EL2)
    };
    let has_s2_enabled : bool = has_s2_translation & (Slice(HCR_EL2, 0, 1) == 0b1 | Slice(HCR_EL2, 12, 1) == 0b1);
    if not_bool(has_s2_enabled) then {
        AArch64_AT_S1Ex(val_name, el, iswrite);
        return()
    } else ();
    __SAVE_EL(el);
    let addrdesc : AddressDescriptor = AArch64_FullTranslate(val_name, AccType_AT, iswrite, true, 1);
    __RESTORE_EL();
    if IsFault(addrdesc) then {
        if IsExternalAbort__1(addrdesc.fault) | (PSTATE.EL == EL1 & EL2Enabled()) & addrdesc.fault.s2fs1walk then {
            PAR_EL1 = __UNKNOWN_bits(64);
            AArch64_Abort(val_name, addrdesc.fault)
        } else ()
    } else ();
    AArch64_EncodePAR(addrdesc)
}

function AT_S12E0R val_name = {
    AArch64_AT_S12Ex(val_name, EL0, false)
}

function AT_S12E0W val_name = {
    AArch64_AT_S12Ex(val_name, EL0, true)
}

function AT_S12E1R val_name = {
    AArch64_AT_S12Ex(val_name, EL1, false)
}

function AT_S12E1W val_name = {
    AArch64_AT_S12Ex(val_name, EL1, true)
}

function AT_S1E0R val_name = {
    AArch64_AT_S1Ex(val_name, EL0, false)
}

function AT_S1E0W val_name = {
    AArch64_AT_S1Ex(val_name, EL0, true)
}

function AT_S1E1R val_name = {
    if ELIsInHost(EL0) then {
        AArch64_AT_S1Ex(val_name, EL2, false)
    } else {
        AArch64_AT_S1Ex(val_name, EL1, false)
    }
}

function AT_S1E1W val_name = {
    if ELIsInHost(EL0) then {
        AArch64_AT_S1Ex(val_name, EL2, true)
    } else {
        AArch64_AT_S1Ex(val_name, EL1, true)
    }
}

function AT_S1E2R val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        AArch64_AT_S1Ex(val_name, EL2, false)
    } else {
        UndefinedFault()
    }
}

function AT_S1E2W val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        AArch64_AT_S1Ex(val_name, EL2, true)
    } else {
        UndefinedFault()
    }
}

function AT_S1E3R val_name = {
    AArch64_AT_S1Ex(val_name, EL3, false)
}

function AT_S1E3W val_name = {
    AArch64_AT_S1Ex(val_name, EL3, true)
}

function AT_S1E1RP val_name = {
    AArch64_AT_S1Ex(val_name, EL1, false)
}

function AT_S1E1WP val_name = {
    AArch64_AT_S1Ex(val_name, EL1, true)
}

function DC_CISW val_name = {
    if PSTATE.EL == EL0 then {
        UndefinedFault()
    } else ();
    return()
}

function MorelloCheckForCMO (cval, requested_perms, acctype) = {
    let 'size = 64;
    va : VirtualAddress = undefined;
    if IsInC64() then {
        va = VAFromCapability(cval)
    } else {
        va = VAFromBits64(cval[63 .. 0])
    };
    let address : bits(64) = VAddress(va);
    let el : bits(2) = AArch64_AccessUsesEL(acctype);
    let 'msbit = AddrTop(address, el);
    let s1_enabled : bool = AArch64_IsStageOneEnabled(acctype);
    addressforbounds : bits(64) = address;
    if msbit != 63 then {
        if s1_enabled then {
            if ((el == EL0 | el == EL1) | ELIsInHost(el)) & [address[msbit]] == 0b1 then {
                addressforbounds = SignExtend(address[msbit .. 0])
            } else {
                addressforbounds = ZeroExtend(address[msbit .. 0])
            }
        } else {
            addressforbounds = ZeroExtend(address[msbit .. 0])
        }
    } else ();
    let addressforbounds : bits(64) = Align(addressforbounds, size);
    capforchecks : bits(129) = undefined;
    if VAIsCapability(va) then {
        capforchecks = VAToCapability(va)
    } else {
        capforchecks = DDC_read()
    };
    fault_type : Fault = Fault_None;
    if CapIsTagClear(capforchecks) then {
        fault_type = Fault_CapTag
    } else if CapIsSealed(capforchecks) then {
        fault_type = Fault_CapSeal
    } else if not_bool(CapCheckPermissions(capforchecks, requested_perms)) then {
        fault_type = Fault_CapPerm
    } else if (requested_perms & CAP_PERM_EXECUTE) != CAP_PERM_NONE & not_bool(CapIsExecutePermitted(capforchecks)) then {
        fault_type = Fault_CapPerm
    } else if not_bool(CapIsRangeInBounds(capforchecks, addressforbounds, size[64 .. 0])) then {
        fault_type = Fault_CapBounds
    } else ();
    if fault_type != Fault_None then {
        let is_store : bool = CapPermsInclude(requested_perms, CAP_PERM_STORE);
        let fault : FaultRecord = CapabilityFault(fault_type, acctype, is_store);
        AArch64_Abort(address, fault)
    } else ();
    return(address)
}

function DC_CIVAC_ val_name = {
    acctype : AccType = undefined;
    iswrite : bool = undefined;
    if PSTATE.EL == EL0 then {
        if ELUsingAArch32(PSTATE.EL) then {
            UndefinedFault()
        } else {
            acctype = AccType_DC_UNPRIV
        }
    } else {
        acctype = AccType_DC
    };
    let instr : bits(32) = ThisInstr();
    let op1 : bits(3) = instr[18 .. 16];
    let CRn : bits(4) = instr[15 .. 12];
    let CRm : bits(4) = instr[11 .. 8];
    let op2 : bits(3) = instr[7 .. 5];
    if ((CRm == 0b0110 & CRn == 0b0111) & op1 == 0b000) & op2 == 0b001 then {
        iswrite = true
    } else {
        iswrite = false
    };
    let memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(val_name, AccType_DC, iswrite, true, 8);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ()
}

function CAP_DC_CIVAC cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, acctype);
    DC_CIVAC_(val_name)
}

function DC_CVAC_ val_name = {
    acctype : AccType = undefined;
    if PSTATE.EL == EL0 then {
        if ELUsingAArch32(PSTATE.EL) then {
            UndefinedFault()
        } else {
            acctype = AccType_DC_UNPRIV
        }
    } else {
        acctype = AccType_DC
    };
    let iswrite : bool = false;
    let memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(val_name, acctype, iswrite, true, 4);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ();
    return()
}

function CAP_DC_CVAC cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, acctype);
    DC_CVAC_(val_name)
}

function CAP_DC_CVADP cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, acctype);
    DC_CVAC_(val_name)
}

function CAP_DC_CVAP cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, acctype);
    DC_CVAC_(val_name)
}

function DC_CVAU_ val_name = {
    acctype : AccType = undefined;
    if PSTATE.EL == EL0 then {
        if ELUsingAArch32(PSTATE.EL) then {
            UndefinedFault()
        } else {
            acctype = AccType_DC_UNPRIV
        }
    } else {
        acctype = AccType_DC
    };
    let iswrite : bool = false;
    let memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(val_name, acctype, iswrite, true, 4);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ();
    return()
}

function CAP_DC_CVAU cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 24, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 52, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 24, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 52, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, acctype);
    DC_CVAU_(val_name)
}

function DC_IVAC_ val_name = {
    acctype : AccType = undefined;
    if PSTATE.EL == EL0 then {
        if ELUsingAArch32(PSTATE.EL) then {
            UndefinedFault()
        } else {
            acctype = AccType_DC_UNPRIV
        }
    } else {
        acctype = AccType_DC
    };
    let iswrite : bool = true;
    let memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(val_name, acctype, iswrite, true, 4);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ();
    if HasS2Translation() & Slice(HCR_EL2, 0, 1) == 0b1 then () else ();
    return()
}

function CAP_DC_IVAC cval = {
    is_clean : bool = false;
    if PSTATE.EL == EL0 then {
        throw(Error_Undefined())
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 23, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 12, 1) @ Slice(HCR_EL2, 0, 1)) != 0b00 then {
            is_clean = true
        } else ()
    } else ();
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_STORE, acctype);
    if is_clean then {
        DC_CIVAC_(val_name)
    } else {
        DC_IVAC_(val_name)
    }
}

function DC_ZVA_ val_name = {
    accdesc : AccessDescriptor = undefined;
    let iswrite : bool = true;
    let 'size = 4 * pow2(UInt(Slice(DCZID_EL0, 0, 4)));
    let vaddress : bits(64) = Align(val_name, size);
    memaddrdesc : AddressDescriptor = AArch64_FullTranslate(vaddress, AccType_DCZVA, iswrite, true, 1);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ();
    foreach (i from 0 to (size - 1) by 1 in inc) {
        accdesc = CreateAccessDescriptor(AccType_DCZVA);
        _Mem_set(memaddrdesc, 1, accdesc) = Zeros();
        memaddrdesc.paddress.address = memaddrdesc.paddress.address + 1
    };
    return()
}

function CAP_DC_ZVA cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 14, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 28, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 14, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 28, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_STORE, AccType_DCZVA);
    DC_ZVA_(val_name)
}

function IC_IVAU val_name = {
    let iswrite : bool = false;
    let memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(val_name, AccType_DC, iswrite, true, 4);
    if IsFault(memaddrdesc) then {
        AArch64_Abort(val_name, memaddrdesc.fault)
    } else ();
    return()
}

function CAP_IC_IVAU cval = {
    if PSTATE.EL == EL0 then {
        if (not_bool(ELUsingAArch32(EL1)) & not_bool(EL2Enabled() & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11)) & Slice(SCTLR_EL1, 26, 1) == 0b0 then {
            if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 27, 1) == 0b1 then {
                AArch64_SystemAccessTrap(EL2, UInt(0x18))
            } else {
                AArch64_SystemAccessTrap(EL1, UInt(0x18))
            }
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 24, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) != 0b11) & Slice(HCR_EL2, 52, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if ((EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & (Slice(HCR_EL2, 34, 1) @ Slice(HCR_EL2, 27, 1)) == 0b11) & Slice(SCTLR_EL2, 26, 1) == 0b0 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else if PSTATE.EL == EL1 then {
        if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 24, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else if (EL2Enabled() & not_bool(ELUsingAArch32(EL2))) & Slice(HCR_EL2, 52, 1) == 0b1 then {
            AArch64_SystemAccessTrap(EL2, UInt(0x18))
        } else ()
    } else ();
    let val_name : bits(64) = MorelloCheckForCMO(cval, CAP_PERM_LOAD, AccType_IC);
    IC_IVAU(val_name)
}

function AArch64_SysInstrWithCapability (op0, op1, crn, crm, op2, val_name) = {
    assert((op0 == 1 & crn == 7) & op2 == 1);
    if op1 == 0 & crm == 6 then {
        CAP_DC_IVAC(val_name)
    } else if op1 == 3 & crm == 4 then {
        CAP_DC_ZVA(val_name)
    } else if op1 == 3 & crm == 5 then {
        CAP_IC_IVAU(val_name)
    } else if op1 == 3 & crm == 10 then {
        CAP_DC_CVAC(val_name)
    } else if op1 == 3 & crm == 11 then {
        CAP_DC_CVAU(val_name)
    } else if op1 == 3 & crm == 12 then {
        CAP_DC_CVAP(val_name)
    } else if op1 == 3 & crm == 13 then {
        CAP_DC_CVADP(val_name)
    } else if op1 == 3 & crm == 14 then {
        CAP_DC_CIVAC(val_name)
    } else {
        Unreachable()
    }
}

function DC_CIVAC val_name__arg = {
    val_name : bits(64) = val_name__arg;
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(ZeroExtend(val_name, 129), CAP_PERM_LOAD, acctype);
    DC_CIVAC_(val_name)
}

function DC_CSW val_name = {
    if PSTATE.EL == EL0 then {
        UndefinedFault()
    } else ();
    return()
}

function DC_CVAC val_name__arg = {
    val_name : bits(64) = val_name__arg;
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(ZeroExtend(val_name, 129), CAP_PERM_LOAD, acctype);
    DC_CVAC_(val_name)
}

function DC_CVAP val_name = {
    DC_CVAC(val_name)
}

function DC_CVAU val_name__arg = {
    val_name : bits(64) = val_name__arg;
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(ZeroExtend(val_name, 129), CAP_PERM_LOAD, acctype);
    DC_CVAU_(val_name)
}

function DC_ISW val_name = {
    if PSTATE.EL == EL0 then {
        UndefinedFault()
    } else ();
    if HasS2Translation() & (Slice(HCR_EL2, 0, 1) == 0b1 | Slice(HCR_EL2, 1, 1) == 0b1) then () else ();
    return()
}

function DC_CVADP val_name = {
    DC_CVAP(val_name)
}

function DVP_RCTX val_name = {
    return()
}

function CPP_RCTX val_name = {
    return()
}

function CFP_RCTX val_name = {
    return()
}

function DC_IVAC val_name__arg = {
    val_name : bits(64) = val_name__arg;
    let acctype : AccType = if PSTATE.EL == EL0 then AccType_DC_UNPRIV else AccType_DC;
    let val_name : bits(64) = MorelloCheckForCMO(ZeroExtend(val_name, 129), CAP_PERM_STORE, acctype);
    DC_IVAC_(val_name)
}

function DC_ZVA val_name__arg = {
    val_name : bits(64) = val_name__arg;
    let val_name : bits(64) = MorelloCheckForCMO(ZeroExtend(val_name, 129), CAP_PERM_STORE, AccType_DCZVA);
    DC_ZVA_(val_name)
}

function IC_IALLU () = {
    if PSTATE.EL == EL0 then {
        UndefinedFault()
    } else ();
    return()
}

function IC_IALLUIS () = {
    if PSTATE.EL == EL0 then {
        UndefinedFault()
    } else ();
    return()
}

function TLBI_ALLE1IS () = {
    _TLB_Invalidate()
}

function TLBI_ALLE1 () = {
    _TLB_Invalidate()
}

function TLBI_ALLE2IS () = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_ALLE2 () = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_ALLE3IS () = {
    _TLB_Invalidate()
}

function TLBI_ALLE3 () = {
    _TLB_Invalidate()
}

function TLBI_ASIDE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_ASIDE1 val_name = {
    _TLB_Invalidate()
}

function TLBI_IPAS2E1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_IPAS2E1 val_name = {
    _TLB_Invalidate()
}

function TLBI_IPAS2LE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_IPAS2LE1 val_name = {
    _TLB_Invalidate()
}

function TLBI_VAAE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VAAE1 val_name = {
    _TLB_Invalidate()
}

function TLBI_VAALE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VAALE1 val_name = {
    _TLB_Invalidate()
}

function TLBI_VAE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VAE1 val_name = {
    _TLB_Invalidate()
}

function TLBI_VAE2IS val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_VAE2 val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_VAE3IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VAE3 val_name = {
    _TLB_Invalidate()
}

function TLBI_VALE1IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VALE2IS val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_VALE2 val_name = {
    if HaveEL(EL2) | PSTATE.EL != EL3 then {
        _TLB_Invalidate()
    } else {
        UndefinedFault()
    }
}

function TLBI_VALE3IS val_name = {
    _TLB_Invalidate()
}

function TLBI_VALE3 val_name = {
    _TLB_Invalidate()
}

function TLBI_VMALLE1 () = {
    _TLB_Invalidate()
}

function TLBI_VMALLE1IS () = {
    _TLB_Invalidate()
}

function TLBI_VMALLS12E1 () = {
    _TLB_Invalidate()
}

function TLBI_VMALLS12E1IS () = {
    _TLB_Invalidate()
}
