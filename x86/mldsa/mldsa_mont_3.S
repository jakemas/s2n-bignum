.intel_syntax noprefix
.text

vpmuldq ymm13, ymm1, ymm8
vmovshdup ymm12, ymm8
vpmuldq ymm14, ymm1, ymm12
vpmuldq ymm8, ymm2, ymm8