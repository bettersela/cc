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
open System.IO

(* ------------------------------------------------------------------- *)

(* Simple environment operations *)

type 'data Env = (string * 'data) list

let rec lookup env x = 
    (*printfn "\n  lookup %A\n" env*) (*debugging code*)
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x

(* A global variable has an absolute address, a local one has an offset: *)

type Var = 
     | Glovar of int                   (* absolute address in stack           *)
     | Locvar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and 
   keeps track of next available offset for local variables *)

type VarEnv = (Var * typ) Env * int   (*(string * (('a * int) * typ)) list * int *)

let findType (var : Var) (varEnv : VarEnv) : typ =
    (*printfn "\n  findType: var: %A, varEnv: %A\n" var varEnv*)(*debugging code*)
    let (env,fdepth) = varEnv (*env : (Var * typ) Env*)
    let rec find env : typ = 
        match env with
        | [] -> failwith "Cannot find the type var in varEnv" (*failwith*)
        | (_, (x, typvar)) :: envr -> if x = var then 
                                             (*printfn "typvar:%A\n" typvar*)(*debugging code*)
                                             match typvar with
                                             | TypA (t, Some i) -> t
                                             | TypP typ -> typ
                                             | _ -> typvar 
                                      else find envr
    find env
(* The function environment maps function name to label and parameter decs *)

type Paramdecs = (typ * string) list
type FunEnv = (label * typ option * Paramdecs) Env

(* Bind declared variable in env and generate code to allocate it: *)

let allocate (kind : int -> Var) (typ, x) (varEnv : VarEnv) : VarEnv * instr list = 
    let (env,fdepth) = varEnv 
    match typ with
    | TypA (TypA _, _) -> 
      raise (Failure "allocate: array of arrays not permitted")
    | TypA (t, Some i) -> 
      let newEnv = ((x, (kind (fdepth+i), typ)) :: env, fdepth+i+1) //数组占用 i个位置
      let code = [INCSP i; GETSP; CSTI (i-1); SUB]
      (newEnv, code)
    | _ -> 
      let newEnv = ((x, (kind (fdepth), typ)) :: env, fdepth+1)
      let code = [INCSP 1]

      (*printf "new varEnv: %A\n" newEnv*)  (*debugging code调试 显示分配后环境变化*)
      (newEnv, code)

(* Bind declared parameters in env: *)

let bindParam (env, fdepth) (typ, x)  : VarEnv = 
    ((x, (Locvar fdepth, typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : VarEnv) : VarEnv = 
    List.fold bindParam (env, fdepth) paras;

(* ------------------------------------------------------------------- *)

(* Build environments for global variables and functions *)

let makeGlobalEnvs (topdecs : topdec list) : VarEnv * FunEnv * instr list = 
    let rec addv decs varEnv funEnv = 
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

let rec typExpr (e:expr) (varEnv : VarEnv) (funEnv : FunEnv) : typ = 
    (*printf "expr in typExpr:%A\n" funEnv*) (*debugging code*)
    match e with
    | Access acc -> typAccess acc varEnv funEnv
    | Assign(acc, e) ->
      let t1 = typAccess acc varEnv funEnv
      let t2 = typExpr e varEnv funEnv
      if t1 = t2 then t1
      else 
          printf "WRONG INFO: Fail to Assign %A to %A, for %A does not match %A\n" e acc t2 t1
          failwith "WRONG!\n"
    | CstI i -> TypI
    | Addr acc -> TypI  (*需要找一个方法把TypP找出来*)
    | Prim1(ope, e1) -> 
        let t1 = typExpr e1 varEnv funEnv
        let t2 = ref TypN
        match ope with
        | "!" -> t2 := TypI
        | "printi" -> t2 := TypI
        | "printc" -> t2 := TypC
        (*printf "ope:%A" (ope,t1,t2)*) (*debugging code*)
        if t1 = !t2 then t1
        else 
             printf "WRONG INFO: Fail to operate %A on %A, for %A does not match %A\n" ope e1 t1 t2
             failwith "Wrong Prim1: type of e1 and t2 dismatch\n" (*failwith*)
    | Prim2(ope,e1,e2)->
        let t1 = typExpr e1 varEnv funEnv
        let t2 = typExpr e2 varEnv funEnv
        if t1 = t2 then t1
        else 
             printf "WRONG INFO: Fail to operate %A on %A and %A, for %A does not match %A\n" ope e1 e2 t1 t2
             failwith "Wrong Prim2: type of e1 and type of e2 dismatch\n" (*failwith*)
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
        | _   -> failwith ("Unknown op"+ope+", or type error\n")
    | Andalso(e1, e2) ->
        let t1 = typExpr e1 varEnv funEnv
        let t2 = typExpr e2 varEnv funEnv
        if t1 = t2 then TypI
        else 
             printf "WRONG INFO: Operands on both sides of 'and' dismatch, for %A does not match %A\n" t1 t2
             failwith "Diffierent type between Andalso(e1 , e2)\n" (*failwith*)
    | Orelse(e1, e2) ->
        let t1 = typExpr e1 varEnv funEnv
        let t2 = typExpr e2 varEnv funEnv
        if t1 = t2 then TypI
        else 
             printf "WRONG INFO: Operands on both sides of 'or' dismatch, for %A does not match %A\n" t1 t2
             failwith "Diffierent type between Orelse(e1 , e2)\n" (*failwith*)
    | Call(f, es) -> 
        (*Map typExpr es varEnv funEnv*)
        (*let (labf, tyOpt, paras) = lookup funEnv f
        tyOpt*)
        TypI
(*如何检查list 遍历es*)
(*Access*)
and typAccess access (varEnv:VarEnv) funEnv : typ =
  (*printf "varEnv in typAccess:%A\n" varEnv*) (*debugging code*)
  match access with
   | AccVar x-> (* TypI*)
        let (data,a) = lookup (fst varEnv) x
        let typeAcc = findType data varEnv
        match typeAcc with
           | TypA (typ,_) -> typ
           | TypP typ -> typ
           | _ -> typeAcc
        (*match lookup varEnv x with
      | Glovar addr,_ -> TypI
      | Locvar addr,_ -> TypI  (*如何用地址找到类型*)*)
   | AccDeref e -> typExpr e varEnv funEnv
   | AccIndex(acc,idx)-> typAccess acc varEnv funEnv
   | _ -> failwith "Wrong at access!"

(*StmtOrDec*)
and typStmtOrDec stmtOrDec (varEnv : VarEnv) (funEnv : FunEnv) : VarEnv *typ =
  match stmtOrDec with
   | Stmt stmt -> (varEnv,typStmt stmt varEnv funEnv)
   | Dec (typ, x)-> let (newVar,_)=allocate Locvar (typ, x) varEnv
                    (*printf "DEC: %A\n" newVar*) (*debugging code*)
                    (newVar,typ)

and  typStmt (e : stmt) (varEnv : VarEnv) (funEnv : FunEnv) : typ =
    (*printf "stmt in typStmt:%A\n" e *)(*debugging code*)
    match e with
    |If(e1,stmt1,stmt2)->
      match typExpr e1 varEnv funEnv with
      | TypI ->(* let t1 = typStmt stmt1 varEnv funEnv
                let t2 = typStmt stmt2 varEnv funEnv
                printf "In If %A\n" (stmt1,stmt2,t1,t2)
                if t1 = t2 then t1
                else failwith "You have wrong type after your if experssion." *)
                typStmt stmt1 varEnv funEnv
                typStmt stmt2 varEnv funEnv
                TypN
      | _ -> failwith "Type dismatch in 'if' expression of e1\n" (*failwith*)
    |While(e, body)->
        (*printf "in while %A\n" e *)(*debugging code*)
        let TypeExpr = typExpr e varEnv funEnv
        if TypeExpr = TypI then typStmt body varEnv funEnv
        else 
             printf "WRONG INFO: 'while' expression types dismatch, for %A does not match %A\n" TypeExpr TypI
             failwith "Wrong in while\n" (*failwith*)
    |Expr e -> typExpr e varEnv funEnv
    |Block stmts -> 
        let rec loop stmts varEnv = 
            match stmts with
            | [] -> 
                    (*printf "block[] %A\n" stmts *)(*debugging code*)
                    (varEnv,TypN)
            | s1::sr -> 
                (*printf "block %A\n" s1 *)(*debugging code*)
                let (v1, t1) = typStmtOrDec s1 varEnv funEnv
                (*printf "block %A\n" v1 *)(*debugging code*)
                let (fdepthr, t2) = loop sr v1
                (v1,t2)
        loop stmts varEnv
        TypN
    | Return None -> TypN
    | Return (Some e)->
        typExpr e varEnv funEnv


and typTopdec (Prog topdecs): typ  =
  let _ = resetLabels() (*清空所有标签*)
  let ((globalVarEnv, _), funEnv, globalInit) = makeGlobalEnvs topdecs
  (*这个是makeGlobalEnvs的三个返回值 其中(globalVarEnv,_)就是全局变量，funEnv就是函数变量*)
  let cherkfun (tyOpt, f, xs, body) =
      let (labf, _, paras) = lookup funEnv f
      let (envf, fdepthf) = bindParams paras (globalVarEnv, 0)
      (*printf "env:%A\n" (envf,fdepthf)*) (*debugging code*)
      let typRet = typStmt body (envf, fdepthf) funEnv
      (*printf "body:%A\n" body*)(*debugging code*)
      None
  List.choose(function
                | Fundec (rTy, name, argTy, body) -> 
                      cherkfun (rTy, name, argTy, body)
                | Vardec(t, var)-> None)
              topdecs
  printf "%A\nTypecheck is FINE!\n" topdecs
  TypN
(*检查函数入口*)
(*let typeCheck filename = typTopdec (fromFile filename);;*)


