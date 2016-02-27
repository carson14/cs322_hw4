	.text
			  # _go () (b, i, a)
	.p2align 4,0x90
	.globl _go
_go:
	subq $180,%rsp
			  #  i = 0
	movq $0,%r10
	movl %r10d,4(%rsp)
			  #  t1 = call _malloc(16)
	movq $16,%rdi
	call _malloc
	movl %eax,12(%rsp)
			  #  a = t1
	movslq 12(%rsp),%r10
	movl %r10d,8(%rsp)
			  #  t2 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,16(%rsp)
			  #  t3 = a + t2
	movslq 8(%rsp),%r10
	movslq 16(%rsp),%r11
	addq %r11,%r10
	movl %r10d,20(%rsp)
			  #  [t3] = 2
	movq $2,%r10
	movslq 20(%rsp),%r11
	movl %r10d,(%r11)
			  #  t4 = true
	movq $1,%r10
	movl %r10d,24(%rsp)
			  #  t5 = true
	movq $1,%r10
	movl %r10d,28(%rsp)
			  #  t6 = 1 < 2
	movq $1,%r10
	movq $2,%r11
	cmpq %r11,%r10
	setl %r10b
	movzbl %r10b,%r10d
	movl %r10d,32(%rsp)
			  #  if t6 == true goto L1
	movslq 32(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L1
			  #  t7 = false
	movq $0,%r10
	movl %r10d,36(%rsp)
			  #  t8 = 3 > 4
	movq $3,%r10
	movq $4,%r11
	cmpq %r11,%r10
	setg %r10b
	movzbl %r10b,%r10d
	movl %r10d,40(%rsp)
			  #  if t8 == false goto L2
	movslq 40(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L2
			  #  t9 = 7 * 8
	movq $7,%r10
	movq $8,%r11
	imulq %r11,%r10
	movl %r10d,44(%rsp)
			  #  t10 = 6 + t9
	movq $6,%r10
	movslq 44(%rsp),%r11
	addq %r11,%r10
	movl %r10d,48(%rsp)
			  #  t11 = 5 == t10
	movq $5,%r10
	movslq 48(%rsp),%r11
	cmpq %r11,%r10
	sete %r10b
	movzbl %r10b,%r10d
	movl %r10d,52(%rsp)
			  #  if t11 == false goto L2
	movslq 52(%rsp),%r10
	movq $0,%r11
	cmpq %r11,%r10
	je _go_L2
			  #  t7 = true
	movq $1,%r10
	movl %r10d,36(%rsp)
			  # L2:
_go_L2:
			  #  if t7 == true goto L1
	movslq 36(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L1
			  #  t5 = false
	movq $0,%r10
	movl %r10d,28(%rsp)
			  # L1:
_go_L1:
			  #  if t5 == true goto L0
	movslq 28(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  t12 = !true
	movq $1,%r10
	notq %r10
	movl %r10d,56(%rsp)
			  #  if t12 == true goto L0
	movslq 56(%rsp),%r10
	movq $1,%r11
	cmpq %r11,%r10
	je _go_L0
			  #  t4 = false
	movq $0,%r10
	movl %r10d,24(%rsp)
			  # L0:
_go_L0:
			  #  b = t4
	movslq 24(%rsp),%r10
	movl %r10d,(%rsp)
			  #  t13 = -3
	movq $3,%r10
	negq %r10
	movl %r10d,60(%rsp)
			  #  t14 = -t13
	movslq 60(%rsp),%r10
	negq %r10
	movl %r10d,64(%rsp)
			  #  t15 = 5 * 4
	movq $5,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,68(%rsp)
			  #  t16 = t15 / 2
	movslq 68(%rsp),%rax
	cqto
	movq $2,%r11
	idivq %r11
	movl %eax,72(%rsp)
			  #  t17 = 1 * 4
	movq $1,%r10
	movq $4,%r11
	imulq %r11,%r10
	movl %r10d,76(%rsp)
			  #  t18 = a + t17
	movslq 8(%rsp),%r10
	movslq 76(%rsp),%r11
	addq %r11,%r10
	movl %r10d,80(%rsp)
			  #  t19 = [t18]
	movslq 80(%rsp),%r10
	movslq (%r10),%r11
	movl %r11d,84(%rsp)
			  #  t20 = t16 * t19
	movslq 72(%rsp),%r10
	movslq 84(%rsp),%r11
	imulq %r11,%r10
	movl %r10d,88(%rsp)
			  #  t21 = t14 + t20
	movslq 64(%rsp),%r10
	movslq 88(%rsp),%r11
	addq %r11,%r10
	movl %r10d,92(%rsp)
			  #  t22 = i * 2
	movslq 4(%rsp),%r10
	movq $2,%r11
	imulq %r11,%r10
	movl %r10d,96(%rsp)
			  #  t23 = t21 + t22
	movslq 92(%rsp),%r10
	movslq 96(%rsp),%r11
	addq %r11,%r10
	movl %r10d,100(%rsp)
			  #  i = t23
	movslq 100(%rsp),%r10
	movl %r10d,4(%rsp)
			  #  call _printBool(b)
	movslq (%rsp),%rdi
	call _printBool
			  #  return i
	movslq 4(%rsp),%rax
	addq $180,%rsp
	ret
			  # _main () 
	.p2align 4,0x90
	.globl _main
_main:
	subq $12,%rsp
			  #  t24 = call _go()
	call _go
	movl %eax,(%rsp)
			  #  call _printInt(t24)
	movslq (%rsp),%rdi
	call _printInt
			  #  return 
	addq $12,%rsp
	ret
			  # Total inst cnt: 147
