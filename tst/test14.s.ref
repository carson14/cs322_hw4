	.text
			  # _foo (i, j) 
	.p2align 4,0x90
	.globl _foo
_foo:
	subq $24,%rsp
	movl %edi,(%rsp)
	movl %esi,4(%rsp)
			  #  t1 = i + j
	movslq (%rsp),%r10
	movslq 4(%rsp),%r11
	addq %r11,%r10
	movl %r10d,8(%rsp)
			  #  return t1
	movslq 8(%rsp),%rax
	addq $24,%rsp
	ret
			  # _main () (b, i, j)
	.p2align 4,0x90
	.globl _main
_main:
	subq $56,%rsp
			  #  b = true
	movq $1,%r10
	movl %r10d,(%rsp)
			  #  t2 = call _foo(1, 2)
	movq $1,%rdi
	movq $2,%rsi
	call _foo
	movl %eax,12(%rsp)
			  #  i = t2
	movslq 12(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  t3 = 2 * 3
	movq $2,%r10
	movq $3,%r11
	imulq %r11,%r10
	movl %r10d,16(%rsp)
			  #  j = t3
	movslq 16(%rsp),%r10
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
	addq $56,%rsp
	ret
			  # Total inst cnt: 38
