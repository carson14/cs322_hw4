	.text
			  # _main () (r)
	.p2align 4,0x90
	.globl _main
_main:
	subq $44,%rsp
			  #  r = 1
	movq $1,%r10
	movl %r10d,(%rsp)
			  #  t1 = r
	movslq (%rsp),%r10
	movl %r10d,4(%rsp)
			  #  t2 = t1 + r
	movslq 4(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,8(%rsp)
			  #  t3 = t2 + r
	movslq 8(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,12(%rsp)
			  #  t4 = t3 + r
	movslq 12(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,16(%rsp)
			  #  t5 = t4 + r
	movslq 16(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  t6 = t5 + r
	movslq 20(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,24(%rsp)
			  #  r = t5 + r
	movslq 20(%rsp),%r10
	movslq (%rsp),%r11
	addq %r11,%r10
	movl %r10d,(%rsp)
			  #  call _printInt(r)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $44,%rsp
	ret
			  # Total inst cnt: 36
