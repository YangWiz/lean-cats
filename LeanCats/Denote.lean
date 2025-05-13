import Mathlib.Data.Set.Basic

def State : Type :=
  String → Nat

def Identity {α : Type} : Set (α × α) :=
  {ab | ab.fst = ab.snd }

inductive Stmt : Type where
  | assign : String -> (State -> Nat) -> Stmt
  | seq : Stmt -> Stmt -> Stmt

inductive CatDenote ->
