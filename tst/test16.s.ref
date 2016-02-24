	.text
			  # _main () (r)
	.p2align 4,0x90
	.globl _main
_main:
	subq $28,%rsp
			  #  t1 = 1
	movq $1,%r10
	movl %r10d,4(%rsp)
			  #  t2 = 2
	movq $2,%r10
	movl %r10d,8(%rsp)
			  #  t3 = 3
	movq $3,%r10
	movl %r10d,12(%rsp)
			  #  t4 = call _f(t1, t2, t3)
	movslq 4(%rsp),%rdi
	movslq 8(%rsp),%rsi
	movslq 12(%rsp),%rdx
	call _f
	movl %eax,16(%rsp)
			  #  call _printInt(t4)
	movslq 16(%rsp),%rdi
	call _printInt
			  #  return 
	addq $28,%rsp
	ret
			  # _f (a, b, c) 
	.p2align 4,0x90
	.globl _f
_f:
	subq $28,%rsp
	movl %edi,(%rsp)
	movl %esi,4(%rsp)
	movl %edx,8(%rsp)
			  #  t1 = call _g(a, b, c)
	movslq (%rsp),%rdi
	movslq 4(%rsp),%rsi
	movslq 8(%rsp),%rdx
	call _g
	movl %eax,12(%rsp)
			  #  t2 = call _g(b, c, a)
	movslq 4(%rsp),%rdi
	movslq 8(%rsp),%rsi
	movslq (%rsp),%rdx
	call _g
	movl %eax,16(%rsp)
			  #  t3 = t2 - t1
	movslq 16(%rsp),%r10
	movslq 12(%rsp),%r11
	subq %r11,%r10
	movl %r10d,20(%rsp)
			  #  return t3
	movslq 20(%rsp),%rax
	addq $28,%rsp
	ret
			  # _g (x, y, z) 
	.p2align 4,0x90
	.globl _g
_g:
	subq $24,%rsp
	movl %edi,(%rsp)
	movl %esi,4(%rsp)
	movl %edx,8(%rsp)
			  #  t1 = z + y
	movslq 8(%rsp),%r10
	movslq 4(%rsp),%r11
	addq %r11,%r10
	movl %r10d,12(%rsp)
			  #  t2 = t1 - x
	movslq 12(%rsp),%r10
	movslq (%rsp),%r11
	subq %r11,%r10
	movl %r10d,16(%rsp)
			  #  return t2
	movslq 16(%rsp),%rax
	addq $24,%rsp
	ret
			  # Total inst cnt: 59
