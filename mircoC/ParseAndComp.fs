(* File MicroC/ParseAndComp.fs *)

module ParseAndComp

let fromString = Parse.fromString

let fromFile = Parse.fromFile

let compileToFile = Comp.compileToFile

let cherk = TypedFun.typeCheck
