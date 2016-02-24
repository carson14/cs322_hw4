	.text
			  # _main () (i, b)
	.p2align 4,0x90
	.globl _main
_main:
	subq $104,%rsp
			  #  t1 = 2 * 4
	movq $2,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,8(%rsp)
			  #  t2 = 2 + t1
	movq $2,%r10
	movslq 8(%rsp),%r11
	addq %r11,%r10
	movl %r10d,12(%rsp)
			  #  t3 = 9 / 3
	movq $9,%rax
	cqto
	movq $3,%r11
	idivq %r11
	movl %eax,16(%rsp)
			  #  t4 = t2 - t3
	movslq 12(%rsp),%r10
	movslq 16(%rsp),%r11
	subq %r11,%r10
	movl %r10d,20(%rsp)
			  #  i = t4
	movslq 20(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t5 = true
	movq $1,%r10
	movl %r10d,24(%rsp)
			  #  t6 = 1 > 2
	movq $1,%r10
	movq $2,%r11
	cmpq %r11,%r10
	setg %r10b
	movzbl %r10b,%r10d
	movl %r10d,28(%rsp)
			  #  if t6 == true goto L0
	movslq 28(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _main_L0
			  #  t7 = false
	movq $0,%r10
	movl %r10d,32(%rsp)
			  #  t8 = 3 < 4
	movq $3,%r10
	movq $4,%r11
	cmpq %r11,%r10
	setl %r10b
	movzbl %r10b,%r10d
	movl %r10d,36(%rsp)
			  #  if t8 == false goto L1
	movslq 36(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _main_L1
			  #  t9 = !false
	movq $0,%r10
	notq %r10
	movl %r10d,40(%rsp)
			  #  if t9 == false goto L1
	movslq 40(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _main_L1
			  #  t7 = true
	movq $1,%r10
	movl %r10d,32(%rsp)
			  # L1:
_main_L1:
			  #  if t7 == true goto L0
	movslq 32(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _main_L0
			  #  t5 = false
	movq $0,%r10
	movl %r10d,24(%rsp)
			  # L0:
_main_L0:
			  #  b = t5
	movslq 24(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  call _printInt(i)
	movslq (%rsp),%rdi
	call _printInt
			  #  call _printBool(b)
	movslq 4(%rsp),%rdi
	call _printBool
			  #  return 
	addq $104,%rsp
	ret
			  # Total inst cnt: 70
