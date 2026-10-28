module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.RegularBranches
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Mixed

/-!
# Orbit geometry for Goldschmidt–O'Nan pairs

This module proves the actual suborbit dichotomy
in Step 1 of GLS, Number 2, Chapter C, Proposition 14.2. The proof keeps the
fixed and moved spaces and their actual Y-suborbit unions explicit. The proof uses only Y-invariance of the moved space. Source:
`refs/KGroup/GLS2/ChapterC.tex`, Proposition 14.2, Steps 1–2.
-/

public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- Step 1: every nonfixed orbit member has one of the two actual suborbit
geometries. -/
theorem Input.suborbitGeometry [Finite X] [Finite V] (h : Input ρ Y) :
    SuborbitGeometry ρ Y := by
  intro W hW hne
  by_cases hle : W ≤ displacementSpan ρ Y ⊤
  · left
    exact ⟨hle, (h.suborbit_of_le_moved hW hle).1,
      (h.suborbit_of_le_moved hW hle).2⟩
  · by_cases hstab : ∃ y : Y, y ≠ 1 ∧ W.map (ρ y) = W
    · obtain ⟨y, hy, hyW⟩ := hstab
      left
      have hle' := h.orbit_le_moved_of_stabilizer_ne_one hW hne hy hyW
      exact ⟨hle', (h.suborbit_of_le_moved hW hle').1,
        (h.suborbit_of_le_moved hW hle').2⟩
    · have hstab' : ∀ y : Y, W.map (ρ y) = W → y = 1 := by
        intro y hy
        by_contra hy'
        exact hstab ⟨y, hy', hy⟩
      by_cases hdis : Disjoint W (displacementSpan ρ Y ⊤)
      · right
        exact ⟨hdis, hstab', h.suborbit_of_disjoint_moved hW hne hdis⟩
      · exact False.elim (h.mixed_intersection_contradiction hW hne hle hstab' hdis)

end Representation.GoldschmidtONan
