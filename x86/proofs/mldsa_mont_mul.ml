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

(* We are taking 9 instructions from within the mldsa NTT.
https://github.com/pq-code-package/mldsa-native/blob/main/mldsa/native/x86_64/src/ntt.S#L36-L48 *)

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
];;
 *)


(* A description of these 9 instructions is as follows:

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
      word 61; word 2; word 196; word 170]
*)

let EXEC = X86_MK_EXEC_RULE mldsa_mont_mul;;
let EXEC_length, EXEC_contents = EXEC;;
(* 
val EXEC : thm * thm option array =
  (|- LENGTH mldsa_mont_mul = 46,
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
     None; None; None; None; None|])
*)

(* Specifications *)

let MLDSA_MONT_MUL_SPEC = prove(
  `forall pc h zeta qinv zeta_high.
  ensures x86
    (\s. bytes_loaded s (word pc) mldsa_mont_mul /\
         read RIP s = word pc /\
         read YMM0 s = qinv /\
         read YMM1 s = zeta /\
         read YMM2 s = zeta_high /\
         read YMM8 s = h)
    (\s. read RIP s = word (pc + 46))
    (MAYCHANGE [RIP] ,, MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,, MAYCHANGE SOME_FLAGS)`,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SOME_FLAGS; fst EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Output from stepping each part in Hol-light REPL server (while working on proof) *)

(* Set current term as goal:
`forall pc h zeta qinv zeta_high.
     ensures x86
     (\s.
          bytes_loaded s (word pc) mldsa_mont_mul /\
          read RIP s = word pc /\
          read YMM0 s = qinv /\
          read YMM1 s = zeta /\
          read YMM2 s = zeta_high /\
          read YMM8 s = h)
     (\s. read RIP s = word (pc + 46))
     (MAYCHANGE [RIP] ,,
      MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
      MAYCHANGE SOME_FLAGS)`
*)

(* Output:
`forall pc h zeta qinv zeta_high.
     ensures x86
     (\s.
          bytes_loaded s (word pc) mldsa_mont_mul /\
          read RIP s = word pc /\
          read YMM0 s = qinv /\
          read YMM1 s = zeta /\
          read YMM2 s = zeta_high /\
          read YMM8 s = h)
     (\s. true)
     (MAYCHANGE [RIP] ,,
      MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
      MAYCHANGE SOME_FLAGS)`
*)


(* Execute current tatic: REPEAT STRIP_TAC *)
(* Output:
`ensures x86
 (\s.
      bytes_loaded s (word pc) mldsa_mont_mul /\
      read RIP s = word pc /\
      read YMM0 s = qinv /\
      read YMM1 s = zeta /\
      read YMM2 s = zeta_high /\
      read YMM8 s = h)
 (\s. read RIP s = word (pc + 46))
 (MAYCHANGE [RIP] ,,
  MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
  MAYCHANGE SOME_FLAGS)`
*)

(* Execute current tatic: REWRITE_TAC [SOME_FLAGS; fst EXEC]  *)
(* Output:
`ensures x86
 (\s.
      bytes_loaded s (word pc) mldsa_mont_mul /\
      read RIP s = word pc /\
      read YMM0 s = qinv /\
      read YMM1 s = zeta /\
      read YMM2 s = zeta_high /\
      read YMM8 s = h)
 (\s. read RIP s = word (pc + 46))
 (MAYCHANGE [RIP] ,,
  MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
  MAYCHANGE [CF; PF; AF; ZF; SF; OF])`
*)

(* Execute current tatic: ENSURES_INIT_TAC "s0"  *)
(* Output:
val it : goalstack = 1 subgoal (1 total)

  0 [`bytes_loaded s0 (word pc) mldsa_mont_mul`]
  1 [`read RIP s0 = word pc`]
  2 [`read YMM0 s0 = qinv`]
  3 [`read YMM1 s0 = zeta`]
  4 [`read YMM2 s0 = zeta_high`]
  5 [`read YMM8 s0 = h`]
  6 [`(MAYCHANGE:((x86state,?272209)component)list->x86state->x86state->bool)
      []
      s0
      s0`]

`eventually x86
 (\s'.
      read RIP s' = word (pc + 46) /\
      (MAYCHANGE [RIP] ,,
       MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF])
      s0
      s')
 s0`
*)

(* Execute current tatic: X86_STEPS_TAC EXEC (1--9) *)
(* Output:
Stepping to state s1
CPU time (user): 0.160738
Stepping to state s2
CPU time (user): 0.133099
Stepping to state s3
CPU time (user): 0.191659
Stepping to state s4
CPU time (user): 0.173835
Stepping to state s5
CPU time (user): 0.20204
Stepping to state s6
CPU time (user): 0.220225
Stepping to state s7
CPU time (user): 0.328331
Stepping to state s8
CPU time (user): 0.245162
Stepping to state s9
CPU time (user): 0.266097
val it : goalstack = 1 subgoal (1 total)

  0 [`bytes_loaded s9 (word pc) mldsa_mont_mul`]
  1 [`read YMM13 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (0,64))
      (0,32)))))`]
  2 [`read YMM2 s9 = zeta_high`]
  3 [`read YMM1 s9 = zeta`]
  4 [`read YMM0 s9 = qinv`]
  5 [`read YMM12 s9 =
      word_join
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (192,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32)))))`]
  6 [`read YMM14 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (0,64))
      (0,32)))))`]
  7 [`(MAYCHANGE [RIP] ,,
       MAYCHANGE [YMM13] ,,
       MAYCHANGE [YMM12] ,,
       MAYCHANGE [YMM14] ,,
       MAYCHANGE [YMM8])
      s0
      s9`]
  8 [`read YMM8 s9 =
      msimd8 (\i x y. if i = word 1 then x else y) (word 170)
      (word_join
       (word_join
        (word_join
         (word_subword
          (word_join
           (word_join
            (word_mul
             (word_sx
             (word_subword (word_subword zeta_high (192,64)) (0,32)))
            (word_sx (word_subword (word_subword h (192,64)) (0,32))))
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
           (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
           (word_sx (word_subword (word_subword h (64,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
          (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
         (224,32))
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (224,32)))
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (160,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (160,32))))
      (word_join
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (96,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (96,32)))
      (word_join
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (32,32))
      (word_subword
       (word_join
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
         (word_sx (word_subword (word_subword h (192,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
        (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
        (word_sx (word_subword (word_subword h (64,64)) (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
       (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
      (32,32)))))
      (word_join
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (192,64))
        (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (128,64))
       (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32))))))`]
  9 [`read RIP s9 = word (pc + 46)`]

`eventually x86
 (\s'.
      read RIP s' = word (pc + 46) /\
      (MAYCHANGE [RIP] ,,
       MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF])
      s0
      s')
 s9`
*)

(* Execute current tatic: ENSURES_FINAL_STATE_TAC *)
(* Output:
val it : goalstack = 1 subgoal (1 total)

  0 [`bytes_loaded s9 (word pc) mldsa_mont_mul`]
  1 [`read YMM13 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (0,64))
      (0,32)))))`]
  2 [`read YMM2 s9 = zeta_high`]
  3 [`read YMM1 s9 = zeta`]
  4 [`read YMM0 s9 = qinv`]
  5 [`read YMM12 s9 =
      word_join
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (192,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32)))))`]
  6 [`read YMM14 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (0,64))
      (0,32)))))`]
  7 [`(MAYCHANGE [RIP] ,,
       MAYCHANGE [YMM13] ,,
       MAYCHANGE [YMM12] ,,
       MAYCHANGE [YMM14] ,,
       MAYCHANGE [YMM8])
      s0
      s9`]
  8 [`read YMM8 s9 =
      msimd8 (\i x y. if i = word 1 then x else y) (word 170)
      (word_join
       (word_join
        (word_join
         (word_subword
          (word_join
           (word_join
            (word_mul
             (word_sx
             (word_subword (word_subword zeta_high (192,64)) (0,32)))
            (word_sx (word_subword (word_subword h (192,64)) (0,32))))
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
           (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
           (word_sx (word_subword (word_subword h (64,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
          (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
         (224,32))
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (224,32)))
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (160,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (160,32))))
      (word_join
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (96,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (96,32)))
      (word_join
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (32,32))
      (word_subword
       (word_join
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
         (word_sx (word_subword (word_subword h (192,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
        (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
        (word_sx (word_subword (word_subword h (64,64)) (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
       (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
      (32,32)))))
      (word_join
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (192,64))
        (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (128,64))
       (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32))))))`]
  9 [`read RIP s9 = word (pc + 46)`]

`read RIP s9 = word (pc + 46) /\
 (MAYCHANGE [RIP] ,,
  MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
  MAYCHANGE [CF; PF; AF; ZF; SF; OF])
 s0
 s9`
*)

(* Execute current tatic: ASM_REWRITE_TAC[] *)
(* Output:
val it : goalstack = 1 subgoal (1 total)

  0 [`bytes_loaded s9 (word pc) mldsa_mont_mul`]
  1 [`read YMM13 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (0,64))
      (0,32)))))`]
  2 [`read YMM2 s9 = zeta_high`]
  3 [`read YMM1 s9 = zeta`]
  4 [`read YMM0 s9 = qinv`]
  5 [`read YMM12 s9 =
      word_join
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (192,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32)))))`]
  6 [`read YMM14 s9 =
      word_join
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (192,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (192,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (128,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (128,64))
      (0,32)))))
      (word_join
       (word_mul (word_sx (word_subword (word_subword qinv (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
           (word_sx
           (word_subword
            (word_subword
             (word_join
              (word_join
               (word_join (word_subword h (224,32))
               (word_subword h (224,32)))
              (word_join (word_subword h (160,32)) (word_subword h (160,32))))
             (word_join
              (word_join (word_subword h (96,32)) (word_subword h (96,32)))
             (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
            (192,64))
           (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (128,64))
          (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (64,64))
          (0,32))))
         (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (0,64))
         (0,32))))))
        (64,64))
       (0,32))))
      (word_mul (word_sx (word_subword (word_subword qinv (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta (192,64)) (0,32)))
          (word_sx
          (word_subword
           (word_subword
            (word_join
             (word_join
              (word_join (word_subword h (224,32)) (word_subword h (224,32)))
             (word_join (word_subword h (160,32)) (word_subword h (160,32))))
            (word_join
             (word_join (word_subword h (96,32)) (word_subword h (96,32)))
            (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
           (192,64))
          (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta (128,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (128,64))
         (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta (64,64)) (0,32)))
         (word_sx
         (word_subword
          (word_subword
           (word_join
            (word_join
             (word_join (word_subword h (224,32)) (word_subword h (224,32)))
            (word_join (word_subword h (160,32)) (word_subword h (160,32))))
           (word_join
            (word_join (word_subword h (96,32)) (word_subword h (96,32)))
           (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
          (64,64))
         (0,32))))
        (word_mul (word_sx (word_subword (word_subword zeta (0,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (0,64))
        (0,32))))))
       (0,64))
      (0,32)))))`]
  7 [`(MAYCHANGE [RIP] ,,
       MAYCHANGE [YMM13] ,,
       MAYCHANGE [YMM12] ,,
       MAYCHANGE [YMM14] ,,
       MAYCHANGE [YMM8])
      s0
      s9`]
  8 [`read YMM8 s9 =
      msimd8 (\i x y. if i = word 1 then x else y) (word 170)
      (word_join
       (word_join
        (word_join
         (word_subword
          (word_join
           (word_join
            (word_mul
             (word_sx
             (word_subword (word_subword zeta_high (192,64)) (0,32)))
            (word_sx (word_subword (word_subword h (192,64)) (0,32))))
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
           (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
           (word_sx (word_subword (word_subword h (64,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
          (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
         (224,32))
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (224,32)))
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (160,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (160,32))))
      (word_join
       (word_join
        (word_subword
         (word_join
          (word_join
           (word_mul
            (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
           (word_sx (word_subword (word_subword h (192,64)) (0,32))))
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
          (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
          (word_sx (word_subword (word_subword h (64,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
         (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
        (96,32))
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (96,32)))
      (word_join
       (word_subword
        (word_join
         (word_join
          (word_mul
           (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
          (word_sx (word_subword (word_subword h (192,64)) (0,32))))
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
         (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
         (word_sx (word_subword (word_subword h (64,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
        (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
       (32,32))
      (word_subword
       (word_join
        (word_join
         (word_mul
          (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
         (word_sx (word_subword (word_subword h (192,64)) (0,32))))
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
        (word_sx (word_subword (word_subword h (128,64)) (0,32)))))
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
        (word_sx (word_subword (word_subword h (64,64)) (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
       (word_sx (word_subword (word_subword h (0,64)) (0,32))))))
      (32,32)))))
      (word_join
       (word_join
        (word_mul
         (word_sx (word_subword (word_subword zeta_high (192,64)) (0,32)))
        (word_sx
        (word_subword
         (word_subword
          (word_join
           (word_join
            (word_join (word_subword h (224,32)) (word_subword h (224,32)))
           (word_join (word_subword h (160,32)) (word_subword h (160,32))))
          (word_join
           (word_join (word_subword h (96,32)) (word_subword h (96,32)))
          (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
         (192,64))
        (0,32))))
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (128,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (128,64))
       (0,32)))))
      (word_join
       (word_mul
        (word_sx (word_subword (word_subword zeta_high (64,64)) (0,32)))
       (word_sx
       (word_subword
        (word_subword
         (word_join
          (word_join
           (word_join (word_subword h (224,32)) (word_subword h (224,32)))
          (word_join (word_subword h (160,32)) (word_subword h (160,32))))
         (word_join
          (word_join (word_subword h (96,32)) (word_subword h (96,32)))
         (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
        (64,64))
       (0,32))))
      (word_mul
       (word_sx (word_subword (word_subword zeta_high (0,64)) (0,32)))
      (word_sx
      (word_subword
       (word_subword
        (word_join
         (word_join
          (word_join (word_subword h (224,32)) (word_subword h (224,32)))
         (word_join (word_subword h (160,32)) (word_subword h (160,32))))
        (word_join
         (word_join (word_subword h (96,32)) (word_subword h (96,32)))
        (word_join (word_subword h (32,32)) (word_subword h (32,32)))))
       (0,64))
      (0,32))))))`]
  9 [`read RIP s9 = word (pc + 46)`]

`(MAYCHANGE [RIP] ,,
  MAYCHANGE [YMM8; YMM12; YMM13; YMM14] ,,
  MAYCHANGE [CF; PF; AF; ZF; SF; OF])
 s0
 s9`
*)