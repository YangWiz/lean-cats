import LeanCats.Syntax
import LeanCats.Relations
import LeanCats.Data

namespace Cats

syntax "[expr|" expr "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term
syntax "[inst|" inst "]" : command

macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) => `(Event.union [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr & $e₂:expr]) => `(Event.inter [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr ; $e₂:expr]) => `(Event.sequence [expr| $e₁] [expr| $e₂])
  | `([expr| $k:keyword ]) => `([keyword| $k])

macro_rules
  | `(keyword| co) => `(Event.co)
  | `(keyword| rf) => `(Event.rf)
  | `(keyword| fr) => `(Event.fr)
  | `(keyword| po) => `(Event.po)
  | `(keyword| W) => `(Event.W)
  | `(keyword| R) => `(Event.R)
  | `(keyword| M) => `(Event.M)
  | `(keyword| emptyset) => `(CandidateExecution.empty)

macro_rules
  | `([assertion| acyclic]) => `(Acyclic)
  | `([assertion| irreflexive]) => `(Irreflexive)
  | `([assertion| empty]) => `(IsEmpty)

macro_rules
  | `([inst| let $nm = $e]) => `(def $nm := [expr|$e])
  | `([inst| $a:assertion $e as $nm]) => `(def $nm : Prop := [assertion| $a] [expr| $e])
  | `([inst| (* $_ *)]) => `(#print "")
