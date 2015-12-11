(* Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ANALYSIS_STRUCTS = 
   sig
      structure Sxml: SXML
   end

signature ANALYSIS = 
   sig
      include ANALYSIS_STRUCTS

      val analysis: { program: Program.t } -> unit
   end
