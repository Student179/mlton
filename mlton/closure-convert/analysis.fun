(* Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(*
 * All local variables in the Sxml are renamed to new variables in Ssa,
 * unless they are global, as determined by the Globalization pass.
 * Renaming must happen because an Sxml variable will be bound in the Ssa
 * once for each lambda it occurs in.  The main trickiness is caused because a
 * property is used to implement the renamer map.  Hence, a variable binding
 * must always be visited with "newVar" or "newScope" before it is looked up
 * with "getNewVar".  "newScope" also handles resetting the variable to its
 * old value once the processing of the lambda is done.
 *)
functor Analysis (S: ANALYSIS_STRUCTS): ANALYSIS = 
struct

open S


fun analysis {program = Program.T {datatypes, body, ...} } =
   let
      val _ =
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach
          (cons, fn {con, arg} =>
           setConArg (con, (case arg of
                               NONE => NONE
                             | SOME t => SOME (Value.fromType t)))))
      val _ =
         let
            open Sxml
            val bogusFrees = ref []
            fun newVar' (x, v, lambda) =
               setVarInfo (x, {frees = ref bogusFrees,
                               isGlobal = ref false,
                               lambda = lambda,
                               replacement = ref x,
                               status = ref Status.init,
                               value = v})
            fun newVar (x, v) = newVar' (x, v, NONE)
            val newVar =
               Trace.trace2 
               ("ClosureConvert.newVar",
                Var.layout, Layout.ignore, Unit.layout)
               newVar
            fun varExps xs = Vector.map (xs, varExp)
            fun loopExp (e: Exp.t): Value.t =
               let
                  val {decs, result} = Exp.dest e
                  val () = List.foreach (decs, loopDec)
               in
                  varExp result
               end
            and loopDec (d: Dec.t): unit =
               let
                  datatype z = datatype Dec.t
               in
                  case d of
                     Fun {decs, ...} =>
                        (Vector.foreach (decs, fn {var, lambda, ty, ...} =>
                                         newVar' (var, Value.fromType ty,
                                                  SOME lambda))
                         ; (Vector.foreach
                            (decs, fn {var, lambda, ...} =>
                             Value.unify (value var,
                                          loopLambda (lambda, var)))))
                   | MonoVal b => loopBind b
                   | _ => Error.bug "ClosureConvert.loopDec: strange dec"
               end
            and loopBind arg =
               traceLoopBind
               (fn {var, ty, exp} =>
               let
                  fun set v = newVar (var, v)
                  fun new () =
                     let val v = Value.fromType ty
                     in set v; v
                     end
                  val new' = ignore o new
                  datatype z = datatype PrimExp.t
               in
                  case exp of
                     App {func, arg} =>
                        let val arg = varExp arg
                           val result = new ()
                        in Value.addHandler
                           (varExp func, fn l =>
                            let
                               val lambda = Value.Lambda.dest l
                               val {arg = formal, body, ...} =
                                  Lambda.dest lambda
                            in Value.coerce {from = arg,
                                             to = value formal}
                               ; Value.coerce {from = expValue body,
                                               to = result}
                            end)
                        end
                   | Case {cases, default, ...} =>
                        let
                           val result = new ()
                           fun branch e =
                              Value.coerce {from = loopExp e, to = result}
                           fun handlePat (Pat.T {con, arg, ...}) =
                              case (arg,      conArg con) of
                                 (NONE,        NONE)       => ()
                               | (SOME (x, _), SOME v)     => newVar (x, v)
                               | _ => Error.bug "ClosureConvert.loopBind: Case"
                           val _ = Cases.foreach' (cases, branch, handlePat)
                           val _ = Option.app (default, branch o #1)
                        in ()
                        end
                   | ConApp {con, arg, ...} =>
                        (case (arg,    conArg con) of
                            (NONE,   NONE)       => ()
                          | (SOME x, SOME v)     =>
                               Value.coerce {from = varExp x, to = v}
                          | _ => Error.bug "ClosureConvert.loopBind: ConApp"
                         ; new' ())
                   | Const _ => new' ()
                   | Handle {try, catch = (x, t), handler} =>
                        let
                           val result = new ()
                        in Value.coerce {from = loopExp try, to = result}
                           ; newVar (x, Value.fromType t)
                           ; Value.coerce {from = loopExp handler, to = result}
                        end
                   | Lambda l => set (loopLambda (l, var))
                   | PrimApp {prim, args, ...} =>
                        set (Value.primApply {prim = prim,
                                              args = varExps args,
                                              resultTy = ty})
                   | Profile _ => new' ()
                   | Raise _ => new' ()
                   | Select {tuple, offset} =>
                        set (Value.select (varExp tuple, offset))
                   | Tuple xs =>
                        if Value.typeIsFirstOrder ty
                           then new' ()
                      else set (Value.tuple (Vector.map (xs, varExp)))
                   | Var x => set (varExp x)
               end) arg
            and loopLambda (lambda: Lambda.t, x: Var.t): Value.t =
               let
                  val _ = List.push (allLambdas, lambda)
                  val {arg, argType, body, ...} = Lambda.dest lambda
                  val _ =
                     setLambdaInfo
                     (lambda,
                      LambdaInfo.T {con = ref Con.bogus,
                                    frees = ref (Vector.new0 ()),
                                    name = Func.newString (Var.originalName x),
                                    recs = ref (Vector.new0 ()),
                                    ty = ref NONE})
                  val _ = newVar (arg, Value.fromType argType)
               in
                  Value.lambda (lambda,
                                Type.arrow (argType, Value.ty (loopExp body)))
               end
            val _ =
               Control.trace (Control.Pass, "flow analysis")
               loopExp body
         in 
            ()
         end
   in
      ()
   end

end
