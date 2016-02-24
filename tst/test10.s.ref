	.text
			  # _go () 
	.p2align 4,0x90
	.globl _go
_go:
	subq $60,%rsp
			  #  t1 = 1 < 2
	movq $1,%r10
	movq $2,%r11
	cmpq %r11,%r10
	setl %r10b
	movzbl %r10b,%r10d
	movl %r10d,(%rsp)
			  #  if t1 == false goto L0
	movslq (%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  call _printInt(1)
	movq $1,%rdi
	call _printInt
			  #  goto L1
	jmp _go_L1
			  # L0:
_go_L0:
			  #  t2 = 3 * 4
	movq $3,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,4(%rsp)
			  #  t3 = t2 == 10
	movslq 4(%rsp),%r10
	movq $10,%r11
	cmpq %r11,%r10
	sete %r10b
	movzbl %r10b,%r10d
	movl %r10d,8(%rsp)
			  #  if t3 == false goto L2
	movslq 8(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L2
			  #  call _printInt(4)
	movq $4,%rdi
	call _printInt
			  #  goto L3
	jmp _go_L3
			  # L2:
_go_L2:
			  #  call _printInt(5)
	movq $5,%rdi
	call _printInt
			  # L3:
_go_L3:
			  # L1:
_go_L1:
			  #  return 6
	movq $6,%rax
	addq $60,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t4 = call _go()
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t4)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 48
