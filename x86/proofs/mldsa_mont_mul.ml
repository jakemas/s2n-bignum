(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA mont mul operation proof.                                          *)
(* ========================================================================= *)

(* debuggin loading check the x86.ml file loads correctly *)
use_file_raise_failure := true;;
loadt "x86/proofs/base.ml";;

(* Working Proof *)
needs "x86/proofs/base.ml";;

(*
 # print_literal_from_elf "x86/mldsa/mldsa_mont_mul.o";;
[
  0xc4; 0x42; 0x75; 0x28; 0xe8;         (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8) *)                  
  0xc4; 0x41; 0x7e; 0x16; 0xe0;         (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)               
  0xc4; 0x42; 0x75; 0x28; 0xf4;         (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm12) *)              
  0xc4; 0x42; 0x6d; 0x28; 0xc0;         (* VPMULDQ (%_% ymm8) (%_% ymm2) (%_% ymm8) *)             
  0xc4; 0x42; 0x6d; 0x28; 0xe4;         (* VPMULDQ (%_% ymm12) (%_% ymm2) (%_% ymm12) *)           
  0xc4; 0x42; 0x7d; 0x28; 0xed;         (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm13) *)      
  0xc4; 0x42; 0x7d; 0x28; 0xf6;         (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;         (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)      
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;   (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)             
  0xc3                                  (* RET *)
];;
 *)

(*
# Montgomery multiplication: h * zeta -> t (instructions 1-9)
vpmuldq    %ymm1,%ymm8,%ymm13          # h * zeta_low -> ymm13
vmovshdup  %ymm8,%ymm12                # extract high parts of h
vpmuldq    %ymm1,%ymm12,%ymm14         # high_h * zeta_low -> ymm14  
vpmuldq    %ymm2,%ymm8,%ymm8           # h * zeta_high -> ymm8
vpmuldq    %ymm2,%ymm12,%ymm12         # high_h * zeta_high -> ymm12
vpmuldq    %ymm0,%ymm13,%ymm13         # apply qinv to ymm13
vpmuldq    %ymm0,%ymm14,%ymm14         # apply qinv to ymm14
vmovshdup  %ymm8,%ymm8                 # shuffle high parts of ymm8
vpblendd   $0xAA,%ymm12,%ymm8,%ymm8    # blend -> Montgomery result
*)

let mldsa_mont_mul = define_assert_from_elf "mldsa_mont_mul" "x86/mldsa/mldsa_mont_mul.o"
[
  0xc4; 0x42; 0x75; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x75; 0x28; 0xf4;
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x6d; 0x28; 0xc0;
                           (* VPMULDQ (%_% ymm8) (%_% ymm2) (%_% ymm8) *)
  0xc4; 0x42; 0x6d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm2) (%_% ymm12) *)
  0xc4; 0x42; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm13) *)
  0xc4; 0x42; 0x7d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm14) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc3                     (* RET *)
];;

(* 
val mldsa_mont_mul : thm =
  |- mldsa_mont_mul =
     [word 196; word 66; word 117; word 40; word 232; word 196; word 65;
      word 126; word 22; word 224; word 196; word 66; word 117; word 40;
      word 244; word 196; word 66; word 109; word 40; word 192; word 196;
      word 66; word 109; word 40; word 228; word 196; word 66; word 125;
      word 40; word 237; word 196; word 66; word 125; word 40; word 246;
      word 196; word 65; word 126; word 22; word 192; word 196; word 67;
      word 61; word 2; word 196; word 170; word 195]
*)

let EXEC = X86_MK_EXEC_RULE mldsa_mont_mul;;

(* 
val EXEC : thm * thm option array =
  (|- LENGTH mldsa_mont_mul = 47,
   [|Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word pc)
                 (5,VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm8));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 5))
                 (5,VMOVSHDUP (%_% ymm12) (%_% ymm8));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 10))
                 (5,VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm12));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 15))
                 (5,VPMULDQ (%_% ymm8) (%_% ymm2) (%_% ymm8));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 20))
                 (5,VPMULDQ (%_% ymm12) (%_% ymm2) (%_% ymm12));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 25))
                 (5,VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm13));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 30))
                 (5,VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm14));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 35))
                 (5,VMOVSHDUP (%_% ymm8) (%_% ymm8));
     None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 40))
                 (6,
                  VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12)
                  (Imm8 (word 170)));
     None; None; None; None; None;
     Some
      |- forall s pc.
             bytes_loaded s (word pc) mldsa_mont_mul
             ==> x86_decode s (word (pc + 46)) (1,RET)|])
*)