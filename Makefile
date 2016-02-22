# Makefile for CS322 Homework 4.
#
JFLAGS = -g
JC = javac

.SUFFIXES: .java .class

.java.class:
	$(JC) $(JFLAGS) $*.java

all:	codegen

ir:	ir/IR1.class ir/IR1Parser.class

codegen: ir CodeGen.class

clean:
	'rm' *.class ir/*.class


