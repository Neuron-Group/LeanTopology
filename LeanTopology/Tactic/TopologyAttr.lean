import Mathlib.Tactic

open Lean

namespace LeanTopology

initialize topologyAttr : TagAttribute ←
  registerTagAttribute `topology
    "Marks theorems that prove a named topology family satisfies `IsTopology_1_1`."

end LeanTopology
