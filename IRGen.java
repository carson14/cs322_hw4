// This is supporting software for CS321/CS322 Compilers and Language Design.
// Copyright (c) Portland State University
//---------------------------------------------------------------------------
// For CS322 W'16 (J. Li).
//

// IR code generator for miniJava's AST. (Simplified version)
//
// Assumptions:
//  - No static data or methods other than the "main" method.
//  - Methods are implemented with static binding. 
//    (hence no need to create class descriptors in IR code)
//  - No init routines for new objects.
//    (hence class fields' init values are ignored)
//  - In source program, base classes are defined before their subclasses.
//    (hence a simple sequential processing of class decls is sufficient)
//
import java.util.*;
import java.io.*;
import ast.*;
import ir.*;

public class IRGen {

  static class GenException extends Exception {
    public GenException(String msg) { super(msg); }
  }

  //------------------------------------------------------------------------------
  // ClassInfo Records
  //------------------
  //  For keeping information about a class decl for later use in the codegen.
  //
  static class ClassInfo {
    String name;			// class name
    ClassInfo parent;			// pointer to parent's record
    Ast.ClassDecl classDecl; 		// class source AST
    HashMap<String,Integer> offsets; 	// instance variable offsets
    int objSize; 			// class object size

    // Constructor -- clone a parent's record
    //
    ClassInfo(Ast.ClassDecl cdecl, ClassInfo parent) {
      this.name = cdecl.nm;
      this.parent = parent;
      this.classDecl = cdecl;
      this.offsets = new HashMap<String,Integer>(parent.offsets); 
      this.objSize = parent.objSize;
    }      

    // Constructor -- create a blank new record
    //
    ClassInfo(Ast.ClassDecl cdecl) {
      this.name = cdecl.nm;
      this.parent = null;
      this.classDecl = cdecl;
      this.offsets = new HashMap<String,Integer>(); 
      this.objSize = 0;
    }      

    // Return method's base class record
    //
    ClassInfo methodBaseClass(String mname) throws Exception {
      for (Ast.MethodDecl mdecl: classDecl.mthds)
	if (mdecl.nm.equals(mname)) 
	  return this;
      if (parent != null)
        return parent.methodBaseClass(mname);
      throw new GenException("Can't find base class for method " + mname);
    }	

    // Return method's return type
    //
    Ast.Type methodType(String mname) throws Exception {
      for (Ast.MethodDecl mdecl: classDecl.mthds)
	if (mdecl.nm.equals(mname))
	  return mdecl.t;
      if (parent != null)
        return parent.methodType(mname);
      throw new GenException("Can't find MethodDecl for method " + mname);
    }

    // Return field's type
    //
    Ast.Type fieldType(String fname) throws Exception {
      for (Ast.VarDecl fdecl: classDecl.flds) {
	if (fdecl.nm.equals(fname))
	  return fdecl.t;
      }
      if (parent != null)
        return parent.fieldType(fname);
      throw new GenException("Can't find VarDecl for field " + fname);
    }

    // Return field's offset
    //
    int fieldOffset(String fname) {
      return offsets.get(fname);
    }

    public String toString() {
      return "ClassInfo: " + " " + name + " " + parent
	+ " " + offsets + " " + objSize + " " + classDecl;
    }
  }

  //------------------------------------------------------------------------------
  // Other Supporting Data Structures
  //---------------------------------

  // CodePack
  // --------
  // For returning <type,src,code> tuple from gen routines
  //
  static class CodePack {
    IR.Type type;
    IR.Src src;
    List<IR.Inst> code;
    CodePack(IR.Type type, IR.Src src, List<IR.Inst> code) { 
      this.type=type; this.src=src; this.code=code; 
    }
    CodePack(IR.Type type, IR.Src src) { 
      this(type, src, new ArrayList<IR.Inst>()); 
    }
  }

  // Env
  // ---
  // For keeping track of local variables and parameters, and their types.
  //
  static class Env extends HashMap<String, Ast.Type> {}

  //------------------------------------------------------------------------------
  // Global Variables and Utility Routines
  //--------------------------------------

  static HashMap<String, ClassInfo> classEnv 	// a map for all ClassInfos
            = new HashMap<String, ClassInfo>();

  static IR.Id thisObj = new IR.Id("obj");	// the "current" object

  // Return an object's base ClassInfo.
  //
  static ClassInfo getClassInfo(Ast.Exp obj, ClassInfo cinfo, 
					Env env) throws Exception {
    ClassInfo info = null;
    if (obj instanceof Ast.This) {
      info = cinfo;
    } else if (obj instanceof Ast.Id) {
      String nm = ((Ast.Id) obj).nm;
      Ast.ObjType type = (Ast.ObjType) env.get(nm);
      if (type != null)
	  if (classEnv != null)
           info = classEnv.get(type.nm);
    } else if (obj instanceof Ast.Field) {
      info = getClassInfo(((Ast.Field) obj).obj, cinfo, env);
      Ast.ObjType type = (Ast.ObjType) info.fieldType(((Ast.Field) obj).nm);
      info = classEnv.get(type.nm);
    } else {
      throw new GenException("Unexpected obj epxression " + obj);  
    }
    return info;
  }

  // Type mapping (AST.Type -> IR.Type)
  //
  static IR.Type gen(Ast.Type n) throws Exception {
    if (n instanceof Ast.IntType)  return IR.Type.INT;
    if (n instanceof Ast.BoolType) return IR.Type.BOOL;
    if (n instanceof Ast.ObjType)  return IR.Type.PTR;
    if (n == null)                 return null;
    throw new GenException("Invalid Ast type: " + n);
  }

  //------------------------------------------------------------------------------
  // The Main Codegen Routine
  //-------------------------
  //
  public static void main(String [] args) throws Exception {
    if (args.length == 1) {
      FileInputStream stream = new FileInputStream(args[0]);
      Ast.Program p = new AstParser(stream).Program();
      stream.close();
      IR.Program ir = gen(p);
      System.out.print(ir.toString());
    } else {
      System.out.println("You must provide an input file name.");
    }
  }

  //------------------------------------------------------------------------------
  // Codegen Routines for Individual AST Nodes
  //------------------------------------------

  // Program ---
  // ClassDecl[] classes;
  //
  // Codegen Guideline: 
  //  Perform two passes over class decls:
  //  1. create ClassInfo records 
  //  2. generate IR code (a list of functions)
  //
  public static IR.Program gen(Ast.Program n) throws Exception {
    // allData list is not used for this assignment
    List<IR.Data> allData = new ArrayList<IR.Data>();	// empty
    List<IR.Func> allFuncs = new ArrayList<IR.Func>();
    // pass 1: create class info records 
    if (n.classes != null) {
    for (Ast.ClassDecl c: n.classes) {
      ClassInfo cinfo = createClassInfo(c);
      classEnv.put(c.nm, cinfo);
    }
    // pass 2: generate IR code
    //  ... NEED CODE ...
    for (Ast.ClassDecl c: n.classes)
      allFuncs.addAll(gen(c, classEnv.get(c.nm)));
    }
    return new IR.Program(allData, allFuncs);
  }

  // Create a class info record for an Ast.ClassDecl node
  //
  // Codegen Guideline: 
  //  1. If parent exists, clone parent's record; otherwise create a new one
  //  2. Walk the VarDecl list; compute offset values for field variables;
  //     - You can use the type mapping utility routine to find out the size
  //       of a var: gen(var's type).size
  //  3. Decide this class' object size
  //
  private static ClassInfo createClassInfo(Ast.ClassDecl n) throws Exception {
    ClassInfo cinfo = null;
    int offset = 0;
    int tsize = 0;
    //IR.Type type = null;
    //  ... NEED CODE ..
    if (n.pnm != null) {
      cinfo = new ClassInfo(n, classEnv.get(n.pnm));
      //cinfo.objsize = parent.objsize
    }
    else {
      cinfo = new ClassInfo(n);
      //cinfo.objsize = 0
    }
    for (Ast.VarDecl v: n.flds) {
      tsize = gen(v.t).size;
      // add the var offset to cinfo.offsets
      cinfo.offsets.put(v.nm,tsize);
      // update cinfo.objsize
      cinfo.objSize += tsize;  
   }

    return cinfo;
  }

  // ClassDecl ---
  // String nm, pnm;
  // VarDecl[] flds;
  // MethodDecl[] mthds;
  //
  // Codegen Guideline: 
  //  Straightforward -- generate an IR.Func for each mthdDecl.
  //
  static List<IR.Func> gen(Ast.ClassDecl n, ClassInfo cinfo) throws Exception {
    List<IR.Func> funcs = new ArrayList<IR.Func>();
    //  ... NEED CODE ...
    for (Ast.MethodDecl m: n.mthds) {
	funcs.add(gen(m, cinfo));
    }
    return funcs;
  }

  // MethodDecl ---
  // Type t;
  // String nm;
  // Param[] params;
  // VarDecl[] vars;
  // Stmt[] stmts;
  //
  // Codegen Guideline: 
  //  (Skip Steps 1,2 if method is "main".)
  //  1. Construct a global label of form "_<base class name>_<method name>"
  //  2. Add thisObj into the params list as the 0th item
  //  3. Create an Env() and add all params and all local vars to it
  //  (Call IR.Temp.reset() to reset the temp counter before Step 4.)
  //  4. Generate IR code for all var decls' init expressions
  //  5. Generate IR code for all statements
  //  6. Return an IR.Func with the above
  //
  static IR.Func gen(Ast.MethodDecl n, ClassInfo cinfo) throws Exception {
    IR.Global irnm = null;
    List<IR.Id> irparams = new ArrayList<IR.Id>();
    List<IR.Id> irlocals = new ArrayList<IR.Id>();
    List<IR.Inst> ircode = new ArrayList<IR.Inst>();
    Env env = new Env();
    // ... NEED CODE ...

    if ("main".equals(n.nm) != true) {
	irnm = new IR.Global("_"+cinfo.parent+"_"+n.nm);
	irparams.add(thisObj);
    }
    // add all params and all local vars to env
    if (n.params != null) {
    for (Ast.Param p: n.params) {
      env.put(p.nm, p.t);
      irparams.add(new IR.Id(p.nm));
    }
    }
    if(n.vars != null) {
    for (Ast.VarDecl v: n.vars) {
      env.put(v.nm, v.t);
      irlocals.add(new IR.Id(v.nm));
    }
    }
    // reset temp counter
    IR.Temp.reset();
    if (n.vars != null) {
    for (Ast.VarDecl v: n.vars)
      ircode.addAll(gen(v, cinfo, env));
    }
    if (n.stmts !=null) {
    for (Ast.Stmt s: n.stmts)
      ircode.addAll(gen(s, cinfo, env));
    }
    return new IR.Func(irnm, irparams!=null?irparams:null, irlocals!=null?irlocals:null, ircode!=null?ircode:null);
  } 

  // VarDecl ---
  // Type t;
  // String nm;
  // Exp init;
  //
  // Codegen Guideline: 
  //  (Note: Same as in IR1Gen.java)
  //  If init exp exists, generate code to evaluate the exp, and add an
  //  IR.Move instruction to assign the result to the var in the decl.
  //
  static List<IR.Inst> gen(Ast.VarDecl n, ClassInfo cinfo, 
				   Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    CodePack cp = null;

    if (n.init != null) {
      cp = gen(n.init, cinfo, env);
      if (cp != null) {
        if (cp.code != null) {
	  code.addAll(cp.code);
        }
        code.add(new IR.Move((IR.Dest) new IR.Id(n.nm), n.init!=null?cp.src:null));
      }
    }
    return code;
  }

  // STATEMENTS

  // Dispatch a generic call to a specific Stmt routine
  // 
  static List<IR.Inst> gen(Ast.Stmt n, ClassInfo cinfo, Env env) throws Exception {
    if (n instanceof Ast.Block)    return gen((Ast.Block) n, cinfo, env);
    if (n instanceof Ast.Assign)   return gen((Ast.Assign) n, cinfo, env);
    if (n instanceof Ast.CallStmt) return gen((Ast.CallStmt) n, cinfo, env);
    if (n instanceof Ast.If)       return gen((Ast.If) n, cinfo, env);
    if (n instanceof Ast.While)    return gen((Ast.While) n, cinfo, env);
    if (n instanceof Ast.Print)    return gen((Ast.Print) n, cinfo, env);
    if (n instanceof Ast.Return)   return gen((Ast.Return) n, cinfo, env);
    throw new GenException("Illegal Stmt: " + n);
  }

  // Block ---
  // Stmt[] stmts;
  //
  static List<IR.Inst> gen(Ast.Block n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    //  ... NEED CODE ...
    for (Ast.Stmt s: n.stmts)
      code.addAll(gen(s, cinfo, env));
    return code;
  }

  // Assign ---
  // Exp lhs, rhs;
  //
  // Codegen Guideline: 
  //  (Note: lhs can only be Id or Field)
  //  1. Call gen() on rhs
  //  2. If lhs is Id, check against Env to see if it's a local var or a param;
  //     if yes, generate an IR.Move instruction
  //  3. Otherwise, lhs is Field, need to generate its address:
  //     (a) Call gen() on the obj component to generate base address
  //     (b) Call getClassInfo() on the obj component to get the base ClassInfo
  //     (c) From base ClassInfo, find out the field's offset
  //     (d) Combine base address and offset to form an IR.Addr
  //     (e) Generate and IR.Store instruction
  //
  static List<IR.Inst> gen(Ast.Assign n, ClassInfo cinfo, Env env) throws Exception {
     List<IR.Inst> code = new ArrayList<IR.Inst>();
     CodePack cp1 = gen(n.rhs, cinfo, env);
     CodePack cp2 = gen(n.lhs, cinfo, env);
     //IR.Type t = null;
    //  ... NEED CODE ...
     if (n.lhs instanceof Ast.Id && env.containsValue(cp2.src))
       code.add(new IR.Move((IR.Dest)cp2.src, cp1.src));
     else {
       ClassInfo base = getClassInfo(n.lhs, cinfo, env);
       //Ast.Field field = (Ast.Field) n.lhs;
       int offset = base.fieldOffset(((Ast.Field) n.lhs).nm);
       IR.Addr addr = new IR.Addr(cp2.src, offset);
       /*       if ((Ast.Type) l.lhs).obj instanceof Ast.BoolLit) t = IR.Type.BOOL;
		if (field.obj instanceof Ast.IntLit) t = IR.Type.INT;*/
       IR.Type type = gen(base.fieldType(((Ast.Field) n.lhs).nm));
       code.add(new IR.Store(type, addr, cp1.src));
     }
    return code;
  }

  // CallStmt ---
  // Exp obj; 
  // String nm;
  // Exp[] args;
  //
  //
  static List<IR.Inst> gen(Ast.CallStmt n, ClassInfo cinfo, Env env) throws Exception {

    CodePack p = genCall(n.obj, n.nm, n.args, cinfo, env, false);
    return p.code;
  }

  // genCall
  // -------
  // Common routine for Call and CallStmt nodes.
  //
  // Codegen Guideline: 
  //  1. Call getClassInfo() on obj to get the base ClassInfo
  //  2. From base ClassInfo, find out the method's base class
  //  3. Combine base class name and method name to form an IR.Global
  //  4. Call gen() on obj to get obj's address; add the address as the 0th 
  //     arg to the args list
  //  5. Gen and add other arguments
  //  6. If retFlag is set, need to receive return value
  //     (a) From base ClassInfo, find out the method's return type
  //     (b) Create a new temp
  //  7. Generate IR.Call instruction (set the indirect flag to false)
  //
  static CodePack genCall(Ast.Exp obj, String name, Ast.Exp[] args, 
			  ClassInfo cinfo, Env env, boolean retFlag) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    List<IR.Src> largs = new ArrayList<IR.Src>();
    CodePack cp = null; 
    ClassInfo base = getClassInfo(obj, cinfo, env);
    ClassInfo mbase = base.methodBaseClass(name);
    IR.Global gname = new IR.Global("_" + base.name + "_" + mbase.name);
    IR.Temp t = null;
    IR.Type type = null;

    cp = gen(obj!=null?obj:null, cinfo!=null?cinfo:null, env!=null?env:null);
    largs.add(cp.src);

    for (Ast.Exp a: args) {
      cp = gen(a, cinfo, env);
      largs.add(cp.src);
    }

    if (retFlag) {
      type = gen(base.methodType(name));
      t = new IR.Temp();
      code.add(new IR.Call((IR.CallTgt) gname, false, largs, (IR.Dest) t));  
    }
    else
      code.add(new IR.Call((IR.CallTgt) gname, false, largs));

    return new CodePack(type, t!=null?t:null, code);
  }

  // If ---
  // Exp cond;
  // Stmt s1, s2;
  //
  // Codegen Guideline: 
  //  (Note: Same as in IR1Gen.java)
  //  newLabel: L1[,L2]
  //  code: cond.c 
  //        + "if cond.v == 0 goto L1" 
  //        + s1.c 
  //        [+ "goto L2"] 
  //        + "L1:" 
  //        [+ s2.c]
  //        [+ "L2:"]
  //
  static List<IR.Inst> gen(Ast.If n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    IR.Label L1 = new IR.Label();
    IR.Label L2 = null;
    
    CodePack cp = gen(n.cond, cinfo, env);

    if (n.s2 != null)
      L2 = new IR.Label();

    if (cp.code != null)
      code.addAll(cp.code);

    code.add(new IR.CJump(IR.ROP.EQ, cp.src, new IR.BoolLit(false), L1));
    code.addAll(gen(n.s1, cinfo, env));

    if (n.s2 != null)
      code.add(new IR.Jump(L2));

    code.add(new IR.LabelDec(L1));

    if (n.s2 != null) {
	code.addAll(gen(n.s2, cinfo, env));
      code.add(new IR.LabelDec(L2));
    }
    return code;
  }

  // While ---
  // Exp cond;
  // Stmt s;
  //
  // Codegen Guideline: 
  //  (Note: Same as in IR1Gen.java)
  //  newLabel: L1,L2
  //  code: "L1:" 
  //        + cond.c 
  //        + "if cond.v == 0 goto L2" 
  //        + s.c 
  //        + "goto L1" 
  //        + "L2:"
  //
  static List<IR.Inst> gen(Ast.While n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    IR.Label L1 = new IR.Label();
    IR.Label L2 = new IR.Label();
    CodePack cp = gen(n.cond, cinfo, env);

    code.add(new IR.LabelDec(L1));

    if (cp.code != null)
	code.addAll(cp.code);

    code.add(new IR.CJump(IR.ROP.EQ, cp.src, new IR.BoolLit(false), L2));
    code.addAll(gen(n.s, cinfo, env));
    code.add(new IR.Jump(L1));
    code.add(new IR.LabelDec(L2));

    return code;
  }
  
  // Print ---
  // Exp arg;
  //
  // Codegen Guideline: 
  //  1. If arg is null or StrLit, generate an IR.Call with "printStr"
  //  2. Otherwise, generate IR code for arg, and use its type info
  //     to decide between "printInt" and "printBool"
  //
  static List<IR.Inst> gen(Ast.Print n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    List<IR.Src> args = new ArrayList<IR.Src>();
    CodePack cp = null;
    IR.Global name = null;
    
    if (n.arg == null || n.arg instanceof Ast.StrLit) {
	cp = gen(n.arg, cinfo, env);
	if (cp != null)
	  args.add(cp.src);
	name = new IR.Global("_printStr"); 
	code.add(new IR.Call((IR.CallTgt) name, false, args, null));
    }
    else {
      if (n!= null)
	  if (n.arg!=null)
            cp = gen(n.arg, cinfo, env);
      switch (cp.type) {
      case BOOL: 
	  name = new IR.Global("_printBool");
	  code.add(new IR.Call((IR.CallTgt) name, false, args, null));
	  break;
      case INT:
	  name = new IR.Global("_printInt");
	  code.add(new IR.Call((IR.CallTgt) name, false, args, null));
	  break;
      }
    }
    return code;
  }

  // Return ---  
  // Exp val;
  //
  // Codegen Guideline: 
  //  (Note: Same as in IR1Gen.java)
  //  1. If val is non-null, generate IR code for it
  //  2. Generate an IR.Return instruction
  //
  static List<IR.Inst> gen(Ast.Return n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    
    if (n.val == null)
      code.add(new IR.Return());
    else {
      CodePack cp = gen(n.val, cinfo, env);
      if (cp.code != null)
	code.addAll(cp.code);
      code.add(new IR.Return(cp.src));
    }
    return code;
  }

  // EXPRESSIONS

  // Dispatch a generic gen call to a specific gen routine
  //
  static CodePack gen(Ast.Exp n, ClassInfo cinfo, Env env) throws Exception {
    if (n instanceof Ast.Call)    return gen((Ast.Call) n, cinfo, env);
    if (n instanceof Ast.NewObj)  return gen((Ast.NewObj) n, cinfo, env);
    if (n instanceof Ast.Field)   return gen((Ast.Field) n, cinfo, env);
    if (n instanceof Ast.Id)	  return gen((Ast.Id) n, cinfo, env);
    if (n instanceof Ast.This)    return gen((Ast.This) n, cinfo);
    if (n instanceof Ast.IntLit)  return gen((Ast.IntLit) n);
    if (n instanceof Ast.BoolLit) return gen((Ast.BoolLit) n);
    if (n instanceof Ast.StrLit)  return gen((Ast.StrLit) n);
    if (n == null)                return null;
    throw new GenException("Exp node not supported in this codegen: " + n);
  }

  // Call ---
  // Exp obj; 
  // String nm;
  // Exp[] args;
  //
  static CodePack gen(Ast.Call n, ClassInfo cinfo, Env env) throws Exception {
    return genCall(n.obj, n.nm, n.args, cinfo, env, true);
  } 
  
  // NewObj ---
  // String nm;
  //
  // Codegen Guideline: 
  //  1. Use class name to get its ClassInfo
  //  2. From ClassInfo, find out class object size
  //  3. If the size is non-zero, generate a malloc call to allocate space,
  //     otherwise, just generate an IR.IntLit(0).
  //
  static CodePack gen(Ast.NewObj n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    List<IR.Src> size = new ArrayList<IR.Src>(); 
    ClassInfo info = null;
    if (n != null && cinfo != null && env != null) {
	if (n.nm != null){
	    Ast.Id foo = new Ast.Id(n.nm);
	    info = getClassInfo(foo, cinfo, env);
	}
    }
    IR.Temp t = null;
    if (info != null)
      size.add((IR.Src) new IR.IntLit(info.objSize));

    if (info != null) {
      if (info.objSize != 0){
	t = new IR.Temp();
	IR.Global name = new IR.Global("_malloc");
	code.add(new IR.Call((IR.CallTgt) name, false, size, (IR.Dest)t)); 
        return new CodePack(null, t, code);
      }
      else
        return gen(new Ast.IntLit(0));
    }
    else return null;
  }
  
  // Field ---
  // Exp obj; 
  // String nm;
  //
  // Codegen Guideline: 
  //  1. Call gen() on the obj component to generate base address
  //  2. Call getClassInfo() on the obj component to get the base ClassInfo
  //  3. From base ClassInfo, find out the field's offset
  //  4. Combine base address and offset to form an IR.Addr
  //  5. From base ClassInfo, find out the field's type
  //  6. Generate and IR.Load instruction
  //
  static CodePack gen(Ast.Field n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    int offset = 0;
    CodePack cp = gen(n.obj, cinfo, env);
    ClassInfo base = getClassInfo(n.obj, cinfo, env);
    if (base != null)
	if (n != null)
	    if (n.nm != null)
              offset = base.fieldOffset(n.nm);
    IR.Addr addr = new IR.Addr(cp.src, offset);
    IR.Type type = gen(base.fieldType(((Ast.Field) n.obj).nm));

    IR.Temp t = new IR.Temp();
    code.add(new IR.Load(type, t, addr));

    return new CodePack(type, t, code);
  }
  
  // Id ---
  // String nm;
  //
  // Codegen Guideline: 
  //  1. Check to see if the Id is in the env; if so, it is a local var or
  //     param, just return the Id (in a CodePack)
  //  2. Otherwise, it is an instance variable:
  //     (a) Convert it to an Ast.Field node with Ast.This() as its obj
  //     (b) Call gen on this new node
  //
  static CodePack gen(Ast.Id n, ClassInfo cinfo, Env env) throws Exception {
    List<IR.Inst> code = new ArrayList<IR.Inst>();
    if (env.containsValue(n.nm)) {
	IR.Type type = gen(env.get(n.nm));
       return new CodePack(type, new IR.Id(n.nm));
    }
    else {
      Ast.Field fld = new Ast.Field(new Ast.This(), n.nm);
      return gen(fld, cinfo, env);
    }
  }

  // This ---
  //
  static CodePack gen(Ast.This n, ClassInfo cinfo) throws Exception {
    return new CodePack(IR.Type.PTR, thisObj);
  }

  // IntLit ---
  // int i;
  //
  static CodePack gen(Ast.IntLit n) throws Exception {
    return  new CodePack(IR.Type.INT, new IR.IntLit(n.i));
  }

  // BoolLit ---
  // boolean b;
  //
  static CodePack gen(Ast.BoolLit n) throws Exception {
    return  new CodePack(IR.Type.BOOL, n.b ? IR.TRUE : IR.FALSE);
  }

  // StrLit ---
  // String s;
  //
  static CodePack gen(Ast.StrLit n) throws Exception {
    return new CodePack(null, new IR.StrLit(n.s));
  }

}
