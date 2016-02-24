	.text
			  # _main () (a)
	.p2align 4,0x90
	.globl _main
_main:
	subq $72,%rsp
			  #  t1 = call _malloc(8)
	movq $8,%rdi
	call _malloc
	movl %eax,4(%rsp)
			  #  a = t1
	movslq 4(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t2 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,8(%rsp)
			  #  t3 = a + t2
	movslq (%rsp),%r10
	movslq 8(%rsp),%r11
	addq %r11,%r10
	movl %r10d,12(%rsp)
			  #  [t3] = 1
	movq $1,%r10
	movslq 12(%rsp),%r11
	movl %r10d,(%r11)
			  #  t4 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,16(%rsp)
			  #  t5 = a + t4
	movslq (%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  [t5] = 2
	movq $2,%r10
	movslq 20(%rsp),%r11
	movl %r10d,(%r11)
			  #  t6 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,24(%rsp)
			  #  t7 = a + t6
	movslq (%rsp),%r10
	movslq 24(%rsp),%r11
	addq %r11,%r10
	movl %r10d,28(%rsp)
			  #  t8 = [t7]
	movslq 28(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,32(%rsp)
			  #  call _printInt(t8)
	movslq 32(%rsp),%rdi
	call _printInt
			  #  t9 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,36(%rsp)
			  #  t10 = a + t9
	movslq (%rsp),%r10
	movslq 36(%rsp),%r11
	addq %r11,%r10
	movl %r10d,40(%rsp)
			  #  t11 = [t10]
	movslq 40(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,44(%rsp)
			  #  call _printInt(t11)
	movslq 44(%rsp),%rdi
	call _printInt
			  #  return 
	addq $72,%rsp
	ret
			  # Total inst cnt: 59
