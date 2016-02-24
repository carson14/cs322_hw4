	.text
			  # _go () (i, j)
	.p2align 4,0x90
	.globl _go
_go:
	subq $24,%rsp
			  #  i = 4
	movq $4,%r10
	movl %r10d,(%rsp)
			  #  t1 = i + 2
	movslq (%rsp),%r10
	movq $2,%r11
	addq %r11,%r10
	movl %r10d,8(%rsp)
			  #  j = t1
	movslq 8(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  return j
	movslq 4(%rsp),%rax
	addq $24,%rsp
	ret
			  # _main () (r)
	.p2align 4,0x90
	.globl _main
_main:
	subq $20,%rsp
			  #  t2 = call _go()
	call _go
	movl %eax,4(%rsp)
			  #  r = t2
	movslq 4(%rsp),%r10
	movl %r10d,(%rsp)
			  #  call _printInt(r)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $20,%rsp
	ret
			  # Total inst cnt: 26
