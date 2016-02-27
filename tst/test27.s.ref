	.text
			  # _go () 
	.p2align 4,0x90
	.globl _go
_go:
	subq $8,%rsp
			  #  t1 = call _value(true)
	movq $1,%rdi
	call _value
	movl %eax,(%rsp)
			  #  return t1
	movslq (%rsp),%rax
	addq $8,%rsp
	ret
			  # _value (cond) (i, j, k)
	.p2align 4,0x90
	.globl _value
_value:
	subq $52,%rsp
	movl %edi,(%rsp)
			  #  i = 5
	movq $5,%r10
	movl %r10d,4(%rsp)
			  #  j = 6
	movq $6,%r10
	movl %r10d,8(%rsp)
			  #  if cond == false goto L0
	movslq (%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _value_L0
			  #  k = i
	movslq 4(%rsp),%r10
	movl %r10d,12(%rsp)
			  #  goto L1
	jmp _value_L1
			  # L0:
_value_L0:
			  #  k = j
	movslq 8(%rsp),%r10
	movl %r10d,12(%rsp)
			  # L1:
_value_L1:
			  #  return k
	movslq 12(%rsp),%rax
	addq $52,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t2 = call _go()
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t2)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 39
