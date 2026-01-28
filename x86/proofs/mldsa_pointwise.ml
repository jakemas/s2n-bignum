(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication of polynomials in NTT domain for ML-DSA.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise.o";;
 ***)
let mldsa_pointwise_mc = define_assert_from_elf "mldsa_pointwise_mc" "x86/mldsa/mldsa_pointwise.o"
[

];;

let mldsa_pointwise_tmc = define_trimmed "mldsa_pointwise_tmc" mldsa_pointwise_mc;;
let MLDSA_POINTWISE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_tmc;;

(* ------------------------------------------------------------------------- *)
(* Mathematical definitions for pointwise multiplication.                    *)
(* ------------------------------------------------------------------------- *)

(* Simple pointwise multiplication: c[i] = a[i] * b[i] in NTT domain *)
let pmul_mldsa = define
  `pmul_mldsa (a: int) (b: int) = a * b`;;

(* Montgomery reduction modulo Q=8380417 with R=2^32 *)
let pmontred_mldsa = define
  `pmontred_mldsa (x: int) = 
     (&(inverse_mod 8380417 4294967296) * x) rem &8380417`;;

(* Pointwise multiplication with Montgomery reduction *)
let pmul_montred_mldsa = define
  `pmul_montred_mldsa (a: int) (b: int) = 
     pmontred_mldsa (pmul_mldsa a b)`;;

(* ------------------------------------------------------------------------- *)
(* Main correctness goal (in g() form for interactive development).          *)
(* ------------------------------------------------------------------------- *)

g `!c a b qdata x y pc.
        aligned 32 c /\
        aligned 32 a /\
        aligned 32 b /\
        aligned 32 qdata /\
        ALL (nonoverlapping (c, 1024))
            [(word pc, 0x400); (a, 1024); (b, 1024); (qdata, 64)] /\
        ALL (nonoverlapping (a, 1024))
            [(word pc, 0x400); (b, 1024); (qdata, 64)] /\
        ALL (nonoverlapping (b, 1024))
            [(word pc, 0x400); (qdata, 64)] /\
        nonoverlapping (word pc, 0x400) (qdata, 64)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_pointwise_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [c; a; b; qdata] s /\
                  (* Input bounds: coefficients bounded by 9*Q *)
                  (!i. i < 256 ==> abs(ival(x i)) <= &(9 * 8380417)) /\
                  (!i. i < 256 ==> abs(ival(y i)) <= &(9 * 8380417)) /\
                  (* Load 256 coefficients from polynomial a *)
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           x i) /\
                  (* Load 256 coefficients from polynomial b *)
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i)))) s =
                           y i))
             (\s. read RIP s = word(pc + 0x3FF) /\
                  (* Output: c[i] = Montgomery_reduce(a[i] * b[i]) *)
                  (!i. i < 256
                       ==> let ci = read(memory :> bytes32
                                        (word_add c (word(4 * i)))) s in
                           (ival ci == pmul_montred_mldsa (ival(x i)) 
                                                           (ival(y i)))
                           (mod &8380417) /\
                           abs(ival ci) <= &8380416))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
              MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(c, 1024)])`;;
