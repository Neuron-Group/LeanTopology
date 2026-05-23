import LeanTopology.TopologicalSpace
import LeanTopology.Tactic.TopologyAttr
import Mathlib.Tactic

/-!
# Topology-intro tactics

This file provides small repo-local tactics for introducing a named topology family and a
matching `IsTopology_1_1` proof into the local context.

The preferred entry point is `topo_auto`, which searches theorems tagged with `@[topology]`.
The explicit helper `topo_set` remains available when the proof should be supplied directly.
-/

open Lean Meta Elab Tactic

namespace LeanTopology

open TopologicalSpace
open EuclideanSpaceTopology

private def introduceNamedTopologyCore (goal : MVarId) (O hO : Syntax)
    (XStx : TSyntax `term) (topologyType topologyValue topologyProof : Expr) : TermElabM MVarId :=
    goal.withContext do
  let (oFVarId, goal) ← (← goal.define O.getId topologyType topologyValue).intro1P
  goal.withContext do
    Term.addLocalVarInfo O (mkFVar oFVarId)
  let hType ← goal.withContext do
    Term.elabType (← `(IsTopology_1_1 ($XStx) $(mkIdent O.getId)))
  let (hFVarId, goal) ← (← goal.assert hO.getId hType topologyProof).intro1P
  goal.withContext do
    Term.addLocalVarInfo hO (mkFVar hFVarId)
  pure goal

private def introduceNamedTopology (goal : MVarId) (O hO : Syntax)
    (XExpr topologyValue topologyProof : Expr) : TermElabM MVarId := goal.withContext do
  let xStx ← Term.exprToSyntax XExpr
  let topologyType ← Term.elabType (← `(Set (Set $xStx)))
  introduceNamedTopologyCore goal O hO xStx topologyType topologyValue topologyProof

private def introduceNamedTopologyFromStx (goal : MVarId) (O hO : Syntax)
    (XStx : TSyntax `term) (topologyValue topologyProof : Expr) : TermElabM MVarId :=
    goal.withContext do
  let topologyType ← Term.elabType (← `(Set (Set ($XStx))))
  introduceNamedTopologyCore goal O hO XStx topologyType topologyValue topologyProof

private def tryInstantiateTopologyProof (proofName : Name) (XExpr topologyValue : Expr) : MetaM (Option Expr) := do
  let proofConst ← mkConstWithFreshMVarLevels proofName
  let proofType ← inferType proofConst
  let isTopologyConst ← mkConstWithFreshMVarLevels ``IsTopology_1_1
  let targetType ← whnf (mkApp2 isTopologyConst XExpr topologyValue)
  observing? do
    let (xs, _, body) ← forallMetaTelescopeReducing proofType
    let body ← whnf body
    guard <| ← withTransparency .reducible <| isDefEq body targetType
    let applied := mkAppN proofConst xs
    let instantiated ← instantiateMVars applied
    let instantiatedType ← whnf (← inferType instantiated)
    guard <| ← withTransparency .reducible <| isDefEq instantiatedType targetType
    pure instantiated

private def findTaggedTopologyProofs (XExpr topologyValue : Expr) : MetaM (List (Name × Expr)) := do
  let env ← getEnv
  let consts := env.constants.toList
  let tagged := consts.foldl (init := []) fun acc (declName, _) =>
    if topologyAttr.hasTag env declName then declName :: acc else acc
  tagged.foldlM (init := []) fun acc declName => do
      let proof? ←
        if declName == ``inducedTopology_isTopology_1_17 then
          observing? do
            let inducedValue ← mkAppOptM ``inducedTopology_1_17 #[some XExpr, none]
            guard <| ← withTransparency .reducible <| isDefEq topologyValue inducedValue
            mkAppOptM ``inducedTopology_isTopology_1_17 #[some XExpr, none]
        else
          tryInstantiateTopologyProof declName XExpr topologyValue
      match proof? with
      | some proof => pure ((declName, proof) :: acc)
      | none => pure acc

private def throwTopoAutoFailure (ref : Syntax) : TermElabM α :=
  throwErrorAt ref
    "`topo_auto` found no `@[topology]` theorem proving `IsTopology_1_1` for this topology"

/--
`topo_set O hO for X := T using hT` introduces a local name `O` for the topology family `T`
on `X` and a proof `hO : IsTopology_1_1 X O`, using the supplied proof term `hT`.
-/
syntax (name := topoSet) "topo_set" ident ident "for" term " := " term " using " term : tactic

elab_rules : tactic
| `(tactic| topo_set $O:ident $hO:ident for $X:term := $T:term using $hT:term) =>
    withMainContext do
      let XExpr ← elabTerm X none
      let topologyValue ← elabTerm T none
      let topologyProof ← elabTerm hT none
      let goal ← introduceNamedTopology (← getMainGoal) O hO XExpr topologyValue topologyProof
      replaceMainGoal [goal]

/--
`topo_auto O hO for X := T` introduces a local name `O` for the topology family `T` on `X`
and searches declarations marked `@[topology]` for a matching proof.
-/
syntax (name := topoAuto) "topo_auto" ident ident "for" term " := " term : tactic

elab_rules : tactic
| `(tactic| topo_auto $O:ident $hO:ident for $X:term := $T:term) => withMainContext do
    let XExpr ← elabTerm X none
    let topologyValue ← elabTerm T none
    let results ← findTaggedTopologyProofs XExpr topologyValue
    match results.reverse with
    | [] =>
        throwTopoAutoFailure T
    | [(_, proof)] =>
        let goal ← introduceNamedTopologyFromStx (← getMainGoal) O hO X topologyValue proof
        replaceMainGoal [goal]
    | many =>
        let names := many.map (fun (n, _) => m!"`{n}`")
        throwErrorAt T
          m!"`topo_auto` found multiple matching `@[topology]` theorems: {MessageData.andList names}"

/-- Introduce a named distance-induced topology and its topology proof. -/
syntax (name := topoDist) "topo_dist" ident ident "for" term : tactic

elab_rules : tactic
| `(tactic| topo_dist $O:ident $hO:ident for $X:term) => withMainContext do
    let XExpr ← elabTerm X none
    let distConst ← mkConstWithFreshMVarLevels ``DistanceSpace_1_12
    let some _ ← synthInstance? (mkApp distConst XExpr)
      | throwErrorAt X "`topo_dist` expects a type with a `DistanceSpace_1_12` instance"
    evalTactic (← `(tactic| topo_auto $O $hO for $X := @inducedTopology_1_17 $X inferInstance))

/--
`topo_euclid O hO for n` introduces a local name `O` for the Euclidean topology on `E n`
and a proof `hO : IsTopology_1_1 (E n) O`.
-/
syntax (name := topoEuclid) "topo_euclid" ident ident "for" term : tactic

elab_rules : tactic
| `(tactic| topo_euclid $O:ident $hO:ident for $n:term) => withMainContext do
    evalTactic (← `(tactic| topo_auto $O $hO for E $n := euclideanTopology_1_9 $n))

end LeanTopology
