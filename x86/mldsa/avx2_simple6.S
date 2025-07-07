.intel_syntax noprefix
  .text

  /* Basic x86 instructions */
  mov eax, 42
  mov ebx, 7
  add eax, ebx
  
  /* AVX2 instructions */
  vpbroadcastd ymm0, xmm0
  vpaddd ymm1, ymm0, ymm0
  vpsubd ymm2, ymm1, ymm0
  vpmulld ymm3, ymm1, ymm2
  vpsrad ymm4, ymm3, 2
  vpmuldq ymm5, ymm1, ymm2
  vmovshdup ymm6, ymm3


  
  /* Return */
  ret
