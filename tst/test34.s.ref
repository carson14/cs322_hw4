	.text
			  # _foo (i) (k)
	.p2align 4,0x90
	.globl _foo
_foo:
	subq $44,%rsp
	movl %edi,(%rsp)
			  #  k = 10
	movq $10,%r10
	movl %r10d,4(%rsp)
			  #  t1 = i > 0
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
	je _foo_L0
			  #  t2 = call _bar(i)
	movslq (%rsp),%rdi
	call _bar
	movl %eax,12(%rsp)
			  #  t3 = call _foo(t2)
	movslq 12(%rsp),%rdi
	call _foo
	movl %eax,16(%rsp)
			  #  t4 = k + t3
	movslq 4(%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  k = t4
	movslq 20(%rsp),%r10
	movl %r10d,4(%rsp)
			  # L0:
_foo_L0:
			  #  return k
	movslq 4(%rsp),%rax
	addq $44,%rsp
	ret
			  # _bar (i) 
	.p2align 4,0x90
	.globl _bar
_bar:
	subq $12,%rsp
	movl %edi,(%rsp)
			  #  t5 = i - 1
	movslq (%rsp),%r10
	movq $1,%r11
	subq %r11,%r10
	movl %r10d,4(%rsp)
			  #  return t5
	movslq 4(%rsp),%rax
	addq $12,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t6 = call _foo(2)
	movq $2,%rdi
	call _foo
	movl %eax,(%rsp)
			  #  call _printInt(t6)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 53
