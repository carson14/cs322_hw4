	.text
			  # _value (i, j, k) 
	.p2align 4,0x90
	.globl _value
_value:
	subq $24,%rsp
	movl %edi,(%rsp)
	movl %esi,4(%rsp)
	movl %edx,8(%rsp)
			  #  t1 = i + j
	movslq (%rsp),%r10
	movslq 4(%rsp),%r11
	addq %r11,%r10
	movl %r10d,12(%rsp)
			  #  t2 = t1 + k
	movslq 12(%rsp),%r10
	movslq 8(%rsp),%r11
	addq %r11,%r10
	movl %r10d,16(%rsp)
			  #  return t2
	movslq 16(%rsp),%rax
	addq $24,%rsp
	ret
			  # _go () 
	.p2align 4,0x90
	.globl _go
_go:
	subq $24,%rsp
			  #  t3 = call _value(1, 1, 1)
	movq $1,%rdi
	movq $1,%rsi
	movq $1,%rdx
	call _value
	movl %eax,(%rsp)
			  #  t4 = call _value(2, 2, 2)
	movq $2,%rdi
	movq $2,%rsi
	movq $2,%rdx
	call _value
	movl %eax,4(%rsp)
			  #  t5 = t3 + t4
	movslq (%rsp),%r10
	movslq 4(%rsp),%r11
	addq %r11,%r10
	movl %r10d,8(%rsp)
			  #  return t5
	movslq 8(%rsp),%rax
	addq $24,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t6 = call _go()
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t6)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 47
