module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Placement
/-!
# The fixed pair for the literal D₁₀ action

The order-five matrix has no fixed vector on either of its two natural
summands. Transporting its two elementary equations through the injective
long-frame coordinates shows that the D₁₀ fixed space consists exactly of
coordinates (0,5). The source linear-centralizer argument uses this pair and
the complementary four coordinates; it still needs the actual A₅ action.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

local instance : CharP GoldenFour 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GoldenFour).injective 2

theorem dihedralModel_rotation : dihedralModel (.r 1) = rotation := by decide +kernel

theorem dihedralModel_reflection : dihedralModel (.sr 0) = flip := by decide +kernel

theorem slEquiv_rotation :
    (slEquiv rotation).val = !![0,1;1,fieldEquiv goldenFourTau] := by
  change (!![0,1;1,goldenFourTau] : Matrix (Fin 2) (Fin 2) GoldenFour).map fieldEquiv = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The D₁₀ fixed space is precisely the pair (0,5), in the literal
Leech coordinate map. In particular the remaining four coordinates are moved. -/
theorem dihedralLift_fixed_iff (L : LongFrame) (v : Fin 6 → F) :
    (∀ d, quotientModTwoRepresentation (dihedralLift L d) (L.coordinates v) =
      L.coordinates v) ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 := by
  constructor
  · intro h
    have hr := h (.r 1)
    rw [dihedralLift_action, dihedralModel_rotation] at hr
    have he := L.coordinates_injective hr
    have h1 : v 2 = v 1 := by
      simpa [blockAction, slEquiv_rotation] using congrFun he 1
    have h2 : v 1 + fieldEquiv goldenFourTau * v 2 = v 2 := by
      simpa [blockAction, slEquiv_rotation] using congrFun he 2
    have h3 : v 4 = v 3 := by
      simpa [blockAction, slEquiv_rotation] using congrFun he 3
    have h4 : v 3 + fieldEquiv goldenFourTau * v 4 = v 4 := by
      simpa [blockAction, slEquiv_rotation] using congrFun he 4
    have hn : fieldEquiv goldenFourTau ≠ 0 := by
      rw [map_ne_zero]
      decide +kernel
    have hz2 : v 2 = 0 := by
      apply (mul_eq_zero.mp (show fieldEquiv goldenFourTau * v 2 = 0 from ?_)).resolve_left hn
      rw [← h1] at h2
      exact add_left_cancel (h2.trans (add_zero _).symm)
    have hz4 : v 4 = 0 := by
      apply (mul_eq_zero.mp (show fieldEquiv goldenFourTau * v 4 = 0 from ?_)).resolve_left hn
      rw [← h3] at h4
      exact add_left_cancel (h4.trans (add_zero _).symm)
    exact ⟨h1.symm.trans hz2, hz2, h3.symm.trans hz4, hz4⟩
  · rintro ⟨h1,h2,h3,h4⟩ d
    rw [dihedralLift_action]
    congr 1
    funext i
    fin_cases i <;> simp [blockAction, h1,h2,h3,h4]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
