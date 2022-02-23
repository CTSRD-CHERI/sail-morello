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

val AArch64_CheckAndUpdateDescriptor : forall ('hwupdatewalk : Bool) ('iswrite : Bool) ('iswritevalidcap : Bool) ('s2fs1walk : Bool) ('secondstage : Bool).
  (DescriptorUpdate, FaultRecord, bool('secondstage), bits(64), AccType, bool('iswrite), bool('s2fs1walk), bool('hwupdatewalk), bool('iswritevalidcap)) -> FaultRecord

function AArch64_CheckAndUpdateDescriptor (result, fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk__arg, iswritevalidcap) = fault

function AArch64_FirstStageTranslateWithTag (vaddress, acctype, iswrite, wasaligned, size, iswritevalidcap) = {
  addrdesc = undefined : AddressDescriptor;
  addrdesc.paddress.address = vaddress[47..0];
  addrdesc.vaddress = vaddress;

  let el : bits(2) = AArch64_AccessUsesEL(acctype);
  let 'msbit = AddrTop(vaddress, el);
  let s1_enabled : bool = AArch64_IsStageOneEnabled(acctype);
  let top_bits_correct = {
    if msbit != 63 then
      let ttbr1 = ((el == EL0 | el == EL1) | ELIsInHost(el)) & [vaddress[msbit]] == 0b1 in
      let check_bits : bits(4) = (if ttbr1 then 0b1111 else 0b0000) in
      vaddress[55 .. 52] == check_bits
    else true
  };
  addrdesc.fault = if top_bits_correct then AArch64_NoFault() else AArch64_AddressSizeFault(undefined, 0, acctype, iswrite, false, false);
  return addrdesc
}

val AArch64_SecondStageTranslate : forall ('hwupdatewalk : Bool) ('iswrite : Bool) ('iswritevalidcap : Bool) ('s2fs1walk : Bool) 'size ('wasaligned : Bool).
  (AddressDescriptor, bits(64), AccType, bool('iswrite), bool('wasaligned), bool('s2fs1walk), int('size), bool('hwupdatewalk), bool('iswritevalidcap)) -> AddressDescriptor

function AArch64_SecondStageTranslate (S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk, iswritevalidcap) = {
  return S1
}

val AArch64_TranslationTableWalk : forall ('iswrite : Bool) ('s1_nonsecure : Bool) ('s2fs1walk : Bool) ('secondstage : Bool) 'size.
  (bits(48), bits(64), AccType, bool('iswrite), bool('secondstage), bool('s2fs1walk), int('size)) -> TLBRecord effect {undef}

function AArch64_TranslationTableWalk (ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size) = {
  return undefined
}

// Stub out a function that only gets called in AArch32 (which doesn't exist in
// Morello) but confuses the register footprint analysis of the T-CHERI lemma
// generation tool

function AArch64_MaybeZeroRegisterUppers () = {
    assert(false)
}
