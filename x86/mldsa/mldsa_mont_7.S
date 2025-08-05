.intel_syntax noprefix
.text

vpmuldq ymm13, ymm1, ymm8
vmovshdup ymm12, ymm8
vpmuldq ymm14, ymm1, ymm12
vpmuldq ymm8, ymm2, ymm8
vpmuldq ymm12, ymm2, ymm12
vpmuldq ymm13, ymm0, ymm13
vpmuldq ymm14, ymm0, ymm14
vmovshdup ymm8, ymm8