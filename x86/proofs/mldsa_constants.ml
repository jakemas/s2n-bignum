(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA constants.                                                         *)
(* ========================================================================= *)

(* Modulus for ML-DSA *)
let mldsa_q = define `mldsa_q = &8380417`;;

(* Half of the modulus *)
let mldsa_q_half = define `mldsa_q_half = &4190208`;;

(* Montgomery reduction constant: -q^(-1) mod 2^32 *)
let mldsa_qinv = define `mldsa_qinv = &4236238847`;;

(* Bound for NTT output *)
let mld_ntt_bound = define `mld_ntt_bound = &75423753`;;
