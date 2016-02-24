	.text
			  # _foo (i) 
	.p2align 4,0x90
	.globl _foo
_foo:
	subq $36,%rsp
	movl %edi,(%rsp)
			  #  t1 = i > 1
	movslq (%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	setg %r10b
	movzbl %r10b,%r10d
	movl %r10d,4(%rsp)
			  #  if t1 == false goto L0
	movslq 4(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _foo_L0
			  #  t2 = call _bar()
	call _bar
	movl %eax,8(%rsp)
			  #  return t2
	movslq 8(%rsp),%rax
	addq $36,%rsp
	ret
			  #  goto L1
	jmp _foo_L1
			  # L0:
_foo_L0:
			  #  return 3
	movq $3,%rax
	addq $36,%rsp
	ret
			  # L1:
_foo_L1:
			  # _bar () 
	.p2align 4,0x90
	.globl _bar
_bar:
	subq $8,%rsp
			  #  t3 = call _foo(1)
	movq $1,%rdi
	call _foo
	movl %eax,(%rsp)
			  #  return t3
	movslq (%rsp),%rax
	addq $8,%rsp
	ret
			  # _main () (i)
	.p2align 4,0x90
	.globl _main
_main:
	subq $20,%rsp
			  #  t4 = call _foo(2)
	movq $2,%rdi
	call _foo
	movl %eax,4(%rsp)
			  #  i = t4
	movslq 4(%rsp),%r10
	movl %r10d,(%rsp)
			  #  call _printInt(i)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $20,%rsp
	ret
			  # Total inst cnt: 45
