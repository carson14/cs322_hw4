	.text
			  # _main () (b, i, j)
	.p2align 4,0x90
	.globl _main
_main:
	subq $40,%rsp
			  #  b = true
	movq $1,%r10
	movl %r10d,(%rsp)
			  #  i = 2
	movq $2,%r10
	movl %r10d,4(%rsp)
			  #  j = 6
	movq $6,%r10
	movl %r10d,8(%rsp)
			  #  call _printBool(b)
	movslq (%rsp),%rdi
	call _printBool
			  #  call _printInt(i)
	movslq 4(%rsp),%rdi
	call _printInt
			  #  call _printInt(j)
	movslq 8(%rsp),%rdi
	call _printInt
			  #  return 
	addq $40,%rsp
	ret
			  # Total inst cnt: 18
