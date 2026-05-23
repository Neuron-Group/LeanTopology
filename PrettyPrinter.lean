import Mathlib.Util.Delaborators

open Lean
open Lean.PrettyPrinter.Delaborator

/--
Override the builtin lambda delaborator so pretty-printed terms in infoview use
`λ` instead of `fun`.
-/
@[delab lam]
def delabLamLambda : Delab := do
  let stx ← Lean.PrettyPrinter.Delaborator.delabLam
  match stx with
  | `(fun $binders* ↦ $body) => `(λ $binders* ↦ $body)
  | _ => pure stx
