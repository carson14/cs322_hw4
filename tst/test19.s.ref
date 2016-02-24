	.text
			  # _go (n) (i)
	.p2align 4,0x90
	.globl _go
_go:
	subq $44,%rsp
	movl %edi,(%rsp)
			  #  i = 0
	movq $0,%r10
	movl %r10d,4(%rsp)
			  #  t1 = n > 0
	movslq (%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	setg %r10b
	movzbl %r10b,%r10d
	movl %r10d,8(%rsp)
			  #  if t1 == false goto L0
	movslq 8(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  call _printInt(n)
	movslq (%rsp),%rdi
	call _printInt
			  #  t2 = n - 1
	movslq (%rsp),%r10
	movq $1,%r11
	subq %r11,%r10
	movl %r10d,12(%rsp)
			  #  t3 = call _back(t2)
	movslq 12(%rsp),%rdi
	call _back
	movl %eax,16(%rsp)
			  #  i = t3
	movslq 16(%rsp),%r10
	movl %r10d,4(%rsp)
			  # L0:
_go_L0:
			  #  return i
	movslq 4(%rsp),%rax
	addq $44,%rsp
	ret
			  # _back (n) (i)
	.p2align 4,0x90
	.globl _back
_back:
	subq $20,%rsp
	movl %edi,(%rsp)
			  #  t4 = call _go(n)
	movslq (%rsp),%rdi
	call _go
	movl %eax,8(%rsp)
			  #  i = t4
	movslq 8(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  return 0
	movq $0,%rax
	addq $20,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t5 = call _go(5)
	movq $5,%rdi
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t5)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 53
