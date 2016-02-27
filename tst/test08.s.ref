	.text
			  # _main () (a, b, i)
	.p2align 4,0x90
	.globl _main
_main:
	subq $92,%rsp
			  #  t1 = call _malloc(8)
	movq $8,%rdi
	call _malloc
	movl %eax,12(%rsp)
			  #  a = t1
	movslq 12(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t2 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,16(%rsp)
			  #  t3 = a + t2
	movslq (%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  [t3] = 2
	movq $2,%r10
	movslq 20(%rsp),%r11
	movl %r10d,(%r11)
			  #  t4 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,24(%rsp)
			  #  t5 = a + t4
	movslq (%rsp),%r10
	movslq 24(%rsp),%r11
	addq %r11,%r10
	movl %r10d,28(%rsp)
			  #  [t5] = 4
	movq $4,%r10
	movslq 28(%rsp),%r11
	movl %r10d,(%r11)
			  #  i = 0
	movq $0,%r10
	movl %r10d,8(%rsp)
			  #  t6 = i * 4
	movslq 8(%rsp),%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,32(%rsp)
			  #  t7 = a + t6
	movslq (%rsp),%r10
	movslq 32(%rsp),%r11
	addq %r11,%r10
	movl %r10d,36(%rsp)
			  #  t8 = [t7]
	movslq 36(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,40(%rsp)
			  #  t9 = i + 1
	movslq 8(%rsp),%r10
	movq $1,%r11
	addq %r11,%r10
	movl %r10d,44(%rsp)
			  #  t10 = t9 * 4
	movslq 44(%rsp),%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,48(%rsp)
			  #  t11 = a + t10
	movslq (%rsp),%r10
	movslq 48(%rsp),%r11
	addq %r11,%r10
	movl %r10d,52(%rsp)
			  #  t12 = [t11]
	movslq 52(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,56(%rsp)
			  #  t13 = t8 + t12
	movslq 40(%rsp),%r10
	movslq 56(%rsp),%r11
	addq %r11,%r10
	movl %r10d,60(%rsp)
			  #  b = t13
	movslq 60(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  call _printInt(b)
	movslq 4(%rsp),%rdi
	call _printInt
			  #  return 
	addq $92,%rsp
	ret
			  # Total inst cnt: 69
