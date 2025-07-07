(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA specifications.                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_constants.ml";;
needs "Library/words.ml";;
needs "Library/isum.ml";;

(* Montgomery multiplication *)
let montgomery_multiply = define
 `montgomery_multiply a b q qinv =
   let t = a * b in
   let m = (t * qinv) mod (2 EXP 32) in
   let t' = (t + m * q) DIV (2 EXP 32) in
   if t' >= q then t' - q else t'`;;

(* Butterfly operation specification *)
let butterfly_spec = define
 `butterfly_spec l h zl zh q qinv =
   let t = montgomery_multiply h zl q qinv in
   (l + t, l - t)`;;
