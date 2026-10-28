module

public import ABG.ChapterII.Section1.CentricFusionRelation

/-!
# Reduction of element fusion to centric normalizer steps

ABG Chapter II §1 invokes Alperin fusion to detect fusion in a Sylow subgroup
through self-centralizing local subgroups. This module specializes
`centric_fusion_relation` to conjugacy inside the chosen Sylow subgroup.
The finite ambient group and prime Sylow hypotheses are essential for the
underlying Huppert X.4.7 decomposition. A local step is tested only at an
extremal subgroup `U` with `C_P(U) ≤ U`, and the conclusion is actual conjugacy
within `P`. Reflexivity and transitivity of conjugacy assemble the local steps.
-/

noncomputable section

namespace ABG

open BenderSuzuki BenderSuzuki.External PFchapter1section1 PFAppendixIII

universe u

/-- If the centric extremal normalizer steps introduce no element fusion in a
Sylow subgroup, then every ambient conjugacy between its elements is already
a conjugacy inside that Sylow subgroup. -/
public theorem centric_fusion_control
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hlocal : ∀ (U : Subgroup G), HuppertExtremal P U →
      subgroupCentralizerIn (P : Subgroup G) U ≤ U →
      ∀ g : G, g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x y : P, (x : G) ∈ U → g⁻¹ * (x : G) * g = (y : G) → IsConj x y)
    {x y : P} (hxy : IsConj (x : G) (y : G)) : IsConj x y := by
  exact centric_fusion_relation P IsConj (fun x => IsConj.refl x)
    (fun hxy hyz => hxy.trans hyz) hlocal hxy

end ABG
