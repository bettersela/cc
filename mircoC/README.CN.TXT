 编译 micro-C编译器，运行编译器 To compile and use the micro-C compiler

   fslex --unicode CLex.fsl
   fsyacc --module CPar CPar.fsy
   
   //启动fsi
   fsi -r FsLexYacc.Runtime.dll Absyn.fs CPar.fs CLex.fs Parse.fs Machine.fs Comp.fs
typedFun.fs ParseAndComp.fs   

   //fsi 中输入，运行编译器
   open ParseAndComp;;
   checkType (fromFile "Testing Data/ex1.c");; //检查ex11.c
   #q;;
   
   

