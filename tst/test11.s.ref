	.text
			  # _go () (a, b, c, x)
	.p2align 4,0x90
	.globl _go
_go:
	subq $100,%rsp
			  #  a = true
	movq $1,%r10
	movl %r10d,(%rsp)
			  #  t1 = !a
	movslq (%rsp),%r10
	notq %r10
	movl %r10d,16(%rsp)
			  #  b = t1
	movslq 16(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  t2 = true
	movq $1,%r10
	movl %r10d,20(%rsp)
			  #  t3 = false
	movq $0,%r10
	movl %r10d,24(%rsp)
			  #  if a == false goto L1
	movslq (%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L1
			  #  if b == false goto L1
	movslq 4(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L1
			  #  t3 = true
	movq $1,%r10
	movl %r10d,24(%rsp)
			  # L1:
_go_L1:
			  #  if t3 == true goto L0
	movslq 24(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  if a == true goto L0
	movslq (%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  t2 = false
	movq $0,%r10
	movl %r10d,20(%rsp)
			  # L0:
_go_L0:
			  #  c = t2
	movslq 20(%rsp),%r10
	movl %r10d,8(%rsp)
			  #  if c == false goto L2
	movslq 8(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L2
			  #  x = 1
	movq $1,%r10
	movl %r10d,12(%rsp)
			  #  goto L3
	jmp _go_L3
			  # L2:
_go_L2:
			  #  x = 0
	movq $0,%r10
	movl %r10d,12(%rsp)
			  # L3:
_go_L3:
			  #  return x
	movslq 12(%rsp),%rax
	addq $100,%rsp
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
			  # Total inst cnt: 58
