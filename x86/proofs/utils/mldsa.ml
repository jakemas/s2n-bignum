(* ========================================================================= *)
(* ML-DSA utilities                                                          *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* AVX2 SIMD operation definitions                                           *)
(* ------------------------------------------------------------------------- *)

let vpmuldq_ymm = define
 `vpmuldq_ymm (a:int256) (b:int256) =
  (word_join:(128)word->(128)word->(256)word)
    ((word_join:(64)word->(64)word->(128)word)
     (word_mul (word_sx (word_subword a (192,32):(32)word)) 
               (word_sx (word_subword b (192,32):(32)word)))
     (word_mul (word_sx (word_subword a (128,32):(32)word)) 
               (word_sx (word_subword b (128,32):(32)word))))
    ((word_join:(64)word->(64)word->(128)word)
     (word_mul (word_sx (word_subword a (64,32):(32)word)) 
               (word_sx (word_subword b (64,32):(32)word)))
     (word_mul (word_sx (word_subword a (0,32):(32)word)) 
               (word_sx (word_subword b (0,32):(32)word))))`;;

let vmovshdup_ymm = define
 `vmovshdup_ymm (a:int256) =
  (word_join:(128)word->(128)word->(256)word)
    ((word_join:(64)word->(64)word->(128)word)
     ((word_join:(32)word->(32)word->(64)word)
      (word_subword a (224,32):(32)word) (word_subword a (224,32):(32)word))
     ((word_join:(32)word->(32)word->(64)word)
      (word_subword a (160,32):(32)word) (word_subword a (160,32):(32)word)))
    ((word_join:(64)word->(64)word->(128)word)
     ((word_join:(32)word->(32)word->(64)word)
      (word_subword a (96,32):(32)word) (word_subword a (96,32):(32)word))
     ((word_join:(32)word->(32)word->(64)word)
      (word_subword a (32,32):(32)word) (word_subword a (32,32):(32)word)))`;;

let vpblendd_ymm = define
 `vpblendd_ymm (mask:(8)word) (a:int256) (b:int256) =
  msimd8 (\(i:(1)word) (x:(32)word) (y:(32)word). if i = word 1 then x else y) 
         mask a b`;;

(* ------------------------------------------------------------------------- *)
(* x86 SIMD simplification                                                   *)
(* ------------------------------------------------------------------------- *)

let X86_SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let X86_SIMD_SIMPLIFY_TAC unfold_defs =
  let simdable = can (term_match [] `read YMM (s:x86state):int256 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (X86_SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;
