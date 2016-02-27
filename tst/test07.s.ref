	.text
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t1 = call _go()
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t1)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # _go () (a, b)
	.p2align 4,0x90
	.globl _go
_go:
	subq $120,%rsp
			  #  t2 = call _malloc(8)
	movq $8,%rdi
	call _malloc
	movl %eax,8(%rsp)
			  #  a = t2
	movslq 8(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t3 = call _malloc(8)
	movq $8,%rdi
	call _malloc
	movl %eax,12(%rsp)
			  #  b = t3
	movslq 12(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  t4 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,16(%rsp)
			  #  t5 = a + t4
	movslq (%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  [t5] = 1
	movq $1,%r10
	movslq 20(%rsp),%r11
	movl %r10d,(%r11)
			  #  t6 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,24(%rsp)
			  #  t7 = a + t6
	movslq (%rsp),%r10
	movslq 24(%rsp),%r11
	addq %r11,%r10
	movl %r10d,28(%rsp)
			  #  [t7] = 2
	movq $2,%r10
	movslq 28(%rsp),%r11
	movl %r10d,(%r11)
			  #  t8 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,32(%rsp)
			  #  t9 = b + t8
	movslq 4(%rsp),%r10
	movslq 32(%rsp),%r11
	addq %r11,%r10
	movl %r10d,36(%rsp)
			  #  [t9] = 3
	movq $3,%r10
	movslq 36(%rsp),%r11
	movl %r10d,(%r11)
			  #  t10 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,40(%rsp)
			  #  t11 = b + t10
	movslq 4(%rsp),%r10
	movslq 40(%rsp),%r11
	addq %r11,%r10
	movl %r10d,44(%rsp)
			  #  [t11] = 4
	movq $4,%r10
	movslq 44(%rsp),%r11
	movl %r10d,(%r11)
			  #  t12 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,48(%rsp)
			  #  t13 = a + t12
	movslq (%rsp),%r10
	movslq 48(%rsp),%r11
	addq %r11,%r10
	movl %r10d,52(%rsp)
			  #  t14 = [t13]
	movslq 52(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,56(%rsp)
			  #  call _printInt(t14)
	movslq 56(%rsp),%rdi
	call _printInt
			  #  t15 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,60(%rsp)
			  #  t16 = b + t15
	movslq 4(%rsp),%r10
	movslq 60(%rsp),%r11
	addq %r11,%r10
	movl %r10d,64(%rsp)
			  #  t17 = [t16]
	movslq 64(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,68(%rsp)
			  #  call _printInt(t17)
	movslq 68(%rsp),%rdi
	call _printInt
			  #  t18 = 0 * 4
	movq $0,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,72(%rsp)
			  #  t19 = a + t18
	movslq (%rsp),%r10
	movslq 72(%rsp),%r11
	addq %r11,%r10
	movl %r10d,76(%rsp)
			  #  t20 = [t19]
	movslq 76(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,80(%rsp)
			  #  return t20
	movslq 80(%rsp),%rax
	addq $120,%rsp
	ret
			  # Total inst cnt: 107
