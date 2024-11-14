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

function __IMPDEF_boolean_map (x if x == "Has Trace Architecture functionality") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space Supported") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space Traps Supported") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Reserved Control Space EL0 Trapped") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Illegal Execution State on return to AArch32") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Floating-Point Traps Support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Floating-Point Traps Information") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Condition valid for trapped T32") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Translation fault on misprogrammed contiguous bit") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Virtual SError syndrome valid") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Have CRC extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Report I-cache maintenance fault in IFSR") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "UNDEF unallocated CP15 access at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Align PC on illegal exception return") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "EL from SPSR on illegal exception return") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has AES Crypto instructions") = {
    return(__crypto_aes_implemented == 1 | __crypto_aes_implemented == 2)
}
and __IMPDEF_boolean_map (x if x == "Has SHA1 Crypto instructions") = {
    return(__crypto_sha1_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SHA256 Crypto instructions") = {
    return(__crypto_sha256_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has 128-bit form of PMULL instructions") = {
    return(__crypto_aes_implemented == 2)
}
and __IMPDEF_boolean_map (x if x == "vector instructions set TFV to 1") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JOSCR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JMCR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "JIDR UNDEFINED at EL0") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has accumulate FP16 product into FP32 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has RAS extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Implicit Error Synchronization Barrier") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Implicit Error Synchronization Barrier before Exception") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has Dot Product extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has SHA512 Crypto instructions") = {
    return(__crypto_sha512_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SHA3 Crypto instructions") = {
    return(__crypto_sha3_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SM3 Crypto instructions") = {
    return(__crypto_sm3_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SM4 Crypto instructions") = {
    return(__crypto_sm4_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has MPAM extension") = {
    return(__mpam_implemented)
}
and __IMPDEF_boolean_map (x if x == "Has SB extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has SSBS extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Have SVE ISA") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 AES extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 128 bit PMULL extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 SHA3 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 SM4 extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Have SVE2 BitPerm extension") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has AArch32 BFloat16 extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has AArch32 Int8 Mat Mul extension") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "ID_MMFR4_EL1 trapped by HCR_EL2.TID3 and ID_MMFR4 trapped by HCR_EL2.TID3 and HCR.TID3") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has large 52-bit PA/IPA support") = {
    return(false)
}
and __IMPDEF_boolean_map (x if x == "Has large 52-bit VA support") = {
    return(true)
}
and __IMPDEF_boolean_map (x if x == "Has 16-bit VMID") = {
    return(true)
}
and __IMPDEF_boolean_map x = {
    throw(Error_ImplementationDefined("Unrecognized boolean"))
}

function __IMPDEF_integer_map (x if x == "Maximum Physical Address Size") = {
    return(48)
}
and __IMPDEF_integer_map (x if x == "Reserved Intermediate Physical Address size value") = {
    return(48)
}
and __IMPDEF_integer_map (x if x == "Maximum Virtual Address Size") = {
    return(52)
}
and __IMPDEF_integer_map x = {
    throw(Error_ImplementationDefined("Unrecognized integer"))
}

function __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-1") = {
    __ConfigureV81Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_arm_v8-2") = {
    __ConfigureV82Features(value_name == 1)
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.CONFIG64") = {
    CFG_RMR_AA64 = [value_name[0]]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.RVBAR") = {
    CFG_RVBAR = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregions") = {
    LORID_EL1 = SetSlice(8, LORID_EL1, 0, value_name[7 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "cpu.num_loregion_descriptors") = {
    LORID_EL1 = SetSlice(8, LORID_EL1, 16, value_name[7 .. 0])
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_pstate_pan") = {
    __pan_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_16bit_vmids") = {
    __vmid16_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.enable_crc32") = {
    __crc32_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_dot_product") = {
    __dot_product_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_fp16") = {
    __fp16_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_aarch32_hpd") = {
    __aa32_hpd_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_aes") = {
    __crypto_aes_implemented = value_name
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha1") = {
    __crypto_sha1_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha256") = {
    __crypto_sha256_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha512") = {
    __crypto_sha512_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sha3") = {
    __crypto_sha3_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm3") = {
    __crypto_sm3_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.crypto_sm4") = {
    __crypto_sm4_implemented = value_name != 0
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.BBM") = {
    __block_bbm_implemented = value_name
}
and __SetConfig ((arg, value_name) if arg == "counter_addr") = {
    __CNTControlBase = value_name[48 - 1 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_cacheable_read_is_sync") = {
    __syncAbortOnReadNormCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_noncacheable_read_is_sync") = {
    __syncAbortOnReadNormNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_device_read_is_sync") = {
    __syncAbortOnDeviceRead = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_so_read_is_sync") = {
    __syncAbortOnSoRead = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_so_write_is_sync") = {
    __syncAbortOnSoWrite = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_prefetch_is_sync") = {
    __syncAbortOnPrefetch = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_ttw_cacheable_read_is_sync") = {
    __syncAbortOnTTWCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_ttw_noncacheable_read_is_sync") = {
    __syncAbortOnTTWNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_cacheable_write_is_sync") = {
    __syncAbortOnWriteNormCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_normal_noncacheable_write_is_sync") = {
    __syncAbortOnWriteNormNonCache = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.ext_abort_device_write_is_sync") = {
    __syncAbortOnDeviceWrite = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_mpam") = {
    __mpam_implemented = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_has_hcr") = {
    __mpam_has_hcr = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_partid") = {
    __mpam_partid_max = value_name[15 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_pmg") = {
    __mpam_pmg_max = value_name[7 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.mpam_max_vpmr") = {
    __mpam_vpmr_max = value_name[2 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.unpred_tsize_aborts") = {
    __unpred_tsize_aborts = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.CONFIG64") = {
    CFG_RMR_AA64 = [value_name[0]]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.RVBAR") = {
    CFG_RVBAR = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_tlb") = {
    __tlb_enabled = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.has_trickbox") = {
    __trickbox_enabled = value_name == 1
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.MPIDR-override") = {
    CFG_MPIDR = value_name[31 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-heap_base") = {
    HEAP_BASE = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-heap_limit") = {
    HEAP_LIMIT = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-stack_base") = {
    STACK_BASE = value_name[63 .. 0]
}
and __SetConfig ((arg, value_name) if arg == "cpu.cpu0.semihosting-stack_limit") = {
    STACK_LIMIT = value_name[63 .. 0]
}
and __SetConfig (arg, value_name) = ()
