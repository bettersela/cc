(* File TypedFun/TypedFun.fs
   An explicitly typed strict first-order functional language. 
   sestoft@itu.dk 2009-09-11

   Different abstract syntax from the first-order and higher-order 
   functional language in Fun/Fun.fs and Fun/HigherFun.fs because
   of the explicit types on function parameters and function results.

   Does not admit mutually recursive function bindings.

   Every function takes exactly one argument.

   Type checking.  Explicit types on the argument and result of each
   declared function.  Expressions and variables may have type int or
   bool or a functional type.  Functions are monomorphically and
   explicitly typed. 

   There is no lexer or parser specification for this explicitly typed
   language because next week we shall infer types rather than check
   them.  
*)

module TypedFun
open Absyn
open Parse
open Machine

(* ------------------------------------------------------------------- *)

(* Simple environment operations *)

type 'data Env = (string * 'data) list

let rec lookup env x = 
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x

(* A global variable has an absolute address, a local one has an offset: *)

type Var = 
     | Glovar of int                   (* absolute address in stack           *)
     | Locvar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and 
   keeps track of next available offset for local variables *)

type VarEnv = (Var * typ) Env * int

(* The function environment maps function name to label and parameter decs *)

type Paramdecs = (typ * string) list
type FunEnv = (label * typ option * Paramdecs) Env

(* Bind declared variable in env and generate code to allocate it: *)

let allocate (kind : int -> Var) (typ, x) (varEnv : VarEnv) : VarEnv * typ =
    printf "allocate called!\n"      
    let (env, fdepth) = varEnv 
    match typ with
    | TypA (TypA _, _) -> 
      raise (Failure "allocate: array of arrays not permitted")
    | TypA (t, Some i) -> 
      let newEnv = ((x, (kind (fdepth+i), typ)) :: env, fdepth+i+1) //数组占用 i个位置
      (newEnv, typ)
    | _ -> 
      let newEnv = ((x, (kind (fdepth), typ)) :: env, fdepth+1)      
      printf "new varEnv: %A\n" newEnv // 调试 显示分配后环境变化
      (newEnv, typ)

(* Bind declared parameters in env: *)

let bindParam (env, fdepth) (typ, x)  : VarEnv = 
    ((x, (Locvar fdepth, typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : VarEnv) : VarEnv = 
    List.fold bindParam (env, fdepth) paras;

(* ------------------------------------------------------------------- *)

(* Build environments for global variables and functions *)

let makeGlobalEnvs (topdecs : topdec list) : VarEnv * FunEnv * instr list = 
    let rec addv decs varEnv funEnv = 
        printf "Global funEnv: %A\n" funEnv  
        match decs with 
        | []         -> (varEnv, funEnv, [])
        | dec::decr  -> 
          match dec with
          | Vardec (typ, var) ->
            let (varEnv1, code1)        = allocate Glovar (typ, var) varEnv
            let (varEnvr, funEnvr, coder) = addv decr varEnv1 funEnv
            (varEnvr, funEnvr, code1 @ coder)
          | Fundec (tyOpt, f, xs, body) ->
            addv decr varEnv ((f, (newLabel(), tyOpt, xs)) :: funEnv)
    addv topdecs ([], 0) []

(* ------------------------------------------------------------------- *)

(* Compiling micro-C statements: 
   * stmt    is the statement to compile
   * varenv  is the local and global variable environment 
   * funEnv  is the global function environment
*)

(* Type checking for the first-order functional language: *)

(* 环境是什么？是env 还是varEnv和funEnv*)
let rec typExpr (e:expr) (varEnv : VarEnv) (funEnv : FunEnv) : typ = 
    match e with
    | Access acc -> TypP
    | Assign(acc, e) ->
      let t1 = typAccess acc varEnv funEnv
      let t2 = typExpr e varEnv funEnv
      if t1 = t2 then t1 
      else failwith "you have wrong between two sides of ="
    | CstI i -> TypI
    | Addr acc -> TypP
    | Prim1(ope, e1) -> 
        let t1 = typExpr e1 env
        let t2 = 
        match ope with
        | "!" -> TypI
        | "printi" -> TypI
        | "printc" -> TypC
        if t1 = t2 then t1
      else failwith "You have wrong type in Prim1."
    | Prim2(ope e1 e2)->
        let t1 = typExpr e1 env
      let t2 = typExpr e2 env
      match (ope, t1, t2) with
      | ("*", TypI, TypI) -> TypI
      | ("+", TypI, TypI) -> TypI
      | ("-", TypI, TypI) -> TypI
      | ("/", TypI, TypI) -> TypI
      | ("%", TypI, TypI) -> TypI
      | ("==", TypI, TypI) -> TypI
      | ("!=", TypI, TypI) -> TypI
      | ("<", TypI, TypI) -> TypI
      | (">=", TypI, TypI) -> TypI
      | (">", TypI, TypI) -> TypI
      | ("<=", TypI, TypI) -> TypI
      | _   -> failwith "unknown op, or type error"
    | Andalso(e1, e2) ->
        t1 = typExpr e1 varEnv funEnv
        t2 = typExpr e2 varEnv funEnv
        if t1 = t2 then TypI
        else failwith "Diffierent type between Andalso(e1,e2) " 
    | Orelse(e1, e2) ->
        Andalso(e1, e2) ->
        t1 = typExpr e1 env
        t2 = typExpr e2 env
        if t1 = t2 then TypI
        else failwith "Diffierent type between Orelse(e1,e2) " 
    | Call(f, es) -> 
        Map typExpr es varEnv funEnv
        let (labf, tyOpt, paras) = lookup funEnv f
        tyOpt
(*如何检查list 遍历es*)
(*Access*)
let typAccess access varEnv funEnv : typ =
  match access with
   | AccVar x-> lookup x(*去环境里面去找参数类型*)--------------
   | AccDeref e -> typExpr e varEnv funEnv
   | AccIndex(acc,idx)-> typAccess acc varEnv funEnv
   | _ -> failwith"Wrong access!"

(*StmtOrDec*)
let typStmtOrDec stmtOrDec (varEnv : VarEnv) (funEnv : FunEnv) : VarEnv *typ =
  match stmtOrDec with
   | Stmt stmt -> (varEnv,typStmt stmt varEnv funEnv)
   | Dec (typ, x)-> allocate Locvar (typ, x) varEnv

let rec typStmt (e : stmt) (varEnv : VarEnv) (funEnv : FunEnv) : typ =
    match e with
    |If(e1,stmt1,stmt2)->
      match typExpr e1 varEnv funEnv with
      | TypI -> let t1 = typStmt stmt1 varEnv funEnv
                let t2 = typStmt stmt2 varEnv funEnv
                if t1 = t2 then t1
                else failwith "You have wrong type after your if experssion." 
      | _ -> failwith "You have wrong type after your if experssion."
    |While(e, body)->
        if typExpr e varEnv funEnv = TypI then typStmt body varEnv funEnv
        else failwith "Wrong with While"
    |Expr e -> typExpr e varEnv funEnv
    |Block stmts -> 
      let rec loop stmts varEnv = 
          match stmts with
          | [] -> TypN
          | s1::sr -> 
              let (v1, t1) = typStmtOrDec s1 varEnv funEnv
              let (fdepthr, t2) = loop sr varEnv1
      TypN
    | Return None -> TypN
    | Return (Some e)->
        typExpr e varEnv funEnv


let typTopdec (Prog topdecs) =
  let _ = resetLabels() (*清空所有标签*)
  let ((globalVarEnv, _), funEnv, globalInit) = makeGlobalEnvs topdecs
  (*这个是makeGlobalEnvs的三个返回值 其中(globalVarEnv,_)就是全局变量，funEnv就是函数变量*)
  let cherkfun (tyOpt, f, xs, body) =
      let (labf, _, paras) = lookup funEnv f
      let (envf, fdepthf) = bindParams paras (globalVarEnv, 0)
      let typRet = typStmt body (envf, fdepthf) funEnv
  List.choose(
   | Fundec(rTy, name, argTy, body) -> 
      cherkfun (rTy, name, argTy, body) 
   | Vardec(t, var)-> None
   )topdecs

(*检查函数入口*)
let typeCheck filename = typTopdec fromFile filename;;


