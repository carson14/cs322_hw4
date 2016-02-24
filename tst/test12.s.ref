	.text
			  # _main () (r)
	.p2align 4,0x90
	.globl _main
_main:
	subq $120,%rsp
			  #  t1 = 1
	movq $1,%r10
	movl %r10d,4(%rsp)
			  #  t2 = 2
	movq $2,%r10
	movl %r10d,8(%rsp)
			  #  t3 = 3
	movq $3,%r10
	movl %r10d,12(%rsp)
			  #  t4 = 4
	movq $4,%r10
	movl %r10d,16(%rsp)
			  #  t5 = 5
	movq $5,%r10
	movl %r10d,20(%rsp)
			  #  t6 = 6
	movq $6,%r10
	movl %r10d,24(%rsp)
			  #  t7 = 7
	movq $7,%r10
	movl %r10d,28(%rsp)
			  #  t8 = 8
	movq $8,%r10
	movl %r10d,32(%rsp)
			  #  t9 = 9
	movq $9,%r10
	movl %r10d,36(%rsp)
			  #  t10 = 10
	movq $10,%r10
	movl %r10d,40(%rsp)
			  #  t11 = 11
	movq $11,%r10
	movl %r10d,44(%rsp)
			  #  t12 = 12
	movq $12,%r10
	movl %r10d,48(%rsp)
			  #  r = 0
	movq $0,%r10
	movl %r10d,(%rsp)
			  #  r = r + t12
	movslq (%rsp),%r10
	movslq 48(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t11
	movslq (%rsp),%r10
	movslq 44(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t10
	movslq (%rsp),%r10
	movslq 40(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t9
	movslq (%rsp),%r10
	movslq 36(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t8
	movslq (%rsp),%r10
	movslq 32(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t7
	movslq (%rsp),%r10
	movslq 28(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t6
	movslq (%rsp),%r10
	movslq 24(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t5
	movslq (%rsp),%r10
	movslq 20(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t4
	movslq (%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t3
	movslq (%rsp),%r10
	movslq 12(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t2
	movslq (%rsp),%r10
	movslq 8(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  r = r + t1
	movslq (%rsp),%r10
	movslq 4(%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  call _printInt(r)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $120,%rsp
	ret
			  # Total inst cnt: 82
