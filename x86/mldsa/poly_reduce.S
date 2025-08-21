.intel_syntax noprefix
.text

vpaddd ymm3, ymm2, ymm1
vpsrad ymm3, ymm3, 23
vpmulld ymm3, ymm3, ymm0
vpsubd ymm2, ymm2, ymm3
