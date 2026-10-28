module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison

/-!
# The genuine odd-five reduction in A.2.17

A.2.17 (printed pp.38–39) eliminates the small orthogonal groups by actual
classical isomorphisms. This adapter composes the stored orthogonal model
with the proved exterior-square equivalence PΩ₅(F) ≃ PSp₄(F), preserving
its coefficient field and order. No additional image, order or simplicity
premise remains. The parent owns the dimension-reduction assembly.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
open ClassicalGroup ClassicalOrthogonal ClassicalOrthogonal.OddFiveComparison
variable {G : Type*} [Group G] {q : ℕ}

/-- The field stored by an odd-order model has nonzero two. -/
private theorem two_ne_zero_of_odd_card (F : Type) [Field F] [Finite F]
    (hc : Nat.card F = q) (ho : Odd q) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  have hnot : ¬ 2 ∣ Fintype.card F := by
    simpa only [← Nat.card_eq_fintype_card, hc] using ho.not_two_dvd_nat
  have hunit : IsUnit (2 : F) := (isUnit_iff_not_dvd_char F 2).mpr
    (fun h => hnot ((prime_dvd_char_iff_dvd_card 2).mp h))
  exact hunit.ne_zero

/-- The five-dimensional odd orthogonal model is the four-dimensional symplectic model. -/
theorem isPSp_two_of_isPOmegaOdd_two (ho : Odd q)
    (h : IsPOmegaOdd G 2 q) : IsPSp G 2 q := by
  rcases h with ⟨F, hF, hfin, hc, ⟨e⟩⟩
  have h2 := two_ne_zero_of_odd_card F hc ho
  exact ⟨F, hF, hfin, hc, ⟨e.trans (projectiveEquivPSp h2)⟩⟩

end CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
