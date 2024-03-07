/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Data.Cnf
import LeanSAT.Model.PropAssn

namespace LeanSAT

/-- Partial assignment implementation backed by `Std.HashMap`.

Good for sparse partial assignments.
-/
def HashAssn (L : Type u) [LitVar L ν] [BEq ν] [Hashable ν] :=
  Std.HashMap ν Bool

namespace HashAssn

variable {L : Type u} {ν : Type v} [LitVar L ν] [BEq ν] [Hashable ν]

def empty : HashAssn L := Std.HashMap.empty

variable (self : HashAssn L)

def set (l : L) : HashAssn L := Std.HashMap.insert self (LitVar.toVar l) (LitVar.polarity l)

def toLitArray : Array L := Std.HashMap.toArray self |>.map (fun (a,b) => LitVar.mkLit L a b)

def toPropAssn : Model.PropAssignment ν :=
  fun v => self.find? v |>.getD false

instance [ToString L] : ToString (HashAssn L) where
  toString a := a.fold (fun s v b => s ++ toString (LitVar.mkLit L v b)) ""
