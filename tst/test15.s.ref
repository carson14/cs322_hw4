	.text
			  # _foo (i) (x)
	.p2align 4,0x90
	.globl _foo
_foo:
	subq $12,%rsp
	movl %edi,(%rsp)
			  #  return i
	movslq (%rsp),%rax
	addq $12,%rsp
	ret
			  # _bar (i) (x)
	.p2align 4,0x90
	.globl _bar
_bar:
	subq $24,%rsp
	movl %edi,(%rsp)
			  #  x = 2
	movq $2,%r10
	movl %r10d,4(%rsp)
			  #  return x
	movslq 4(%rsp),%rax
	addq $24,%rsp
	ret
			  # _main () (i, j)
	.p2align 4,0x90
	.globl _main
_main:
	subq $36,%rsp
			  #  t1 = call _foo(1)
	movq $1,%rdi
	call _foo
	movl %eax,8(%rsp)
			  #  i = t1
	movslq 8(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t2 = call _bar(1)
	movq $1,%rdi
	call _bar
	movl %eax,12(%rsp)
			  #  j = t2
	movslq 12(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  call _printInt(i)
	movslq (%rsp),%rdi
	call _printInt
			  #  call _printInt(j)
	movslq 4(%rsp),%rdi
	call _printInt
			  #  return 
	addq $36,%rsp
	ret
			  # Total inst cnt: 36
