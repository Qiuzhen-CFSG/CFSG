module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.PrimeSupport
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary.Lifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# Three-primary kernel exclusion for the actual Sp₄(3)

The explicit matrix embedding of C₃³ ⋊ C₃ has order 81 and index 640 in
Sp₄(3). Compatible cubic lifts give a section over its literal image in
every central extension. Transfer in a finite perfect cover then excludes
three from the kernel order. Neither the two-primary exclusion nor any
universal property is assumed.

This discharges the three-primary premise of
`TernarySection.exists_section_of_not_two_dvd_of_not_three_dvd`; the parent
assembly retains the independent two-primary calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.1.4(1), printed p.408, and GLS3 §6.1. The argument uses the actual
symplectic matrix carrier throughout, without assuming a unitary comparison.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary

/-- The coordinate semidirect product contains the whole three-part of |Sp₄(3)|. -/
theorem card_model : Nat.card Model = 81 := by
  rw [SemidirectProduct.card]
  change Nat.card (Fin 3 → ZMod 3) * Nat.card (ZMod 3) = 81
  rw [Nat.card_fun]
  norm_num

/-- Cardinality of the actual matrix subgroup, using the proved injection. -/
theorem card_range : Nat.card embedding.range = 81 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv]
  exact card_model

/-- The matrix subgroup has index prime to three. -/
theorem index_range : embedding.range.index = 640 := by
  have hi := embedding.range.card_mul_index
  rw [card_range, card_sp_three] at hi
  omega

/-- The section commutes with the literal inclusion of the matrix subgroup. -/
theorem exists_section_on_range {E : Type*} [Group E]
    (f : E →* OddPrime.Sp (ZMod 3)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : embedding.range →* E, f.comp s = embedding.range.subtype := by
  obtain ⟨s, hs⟩ := exists_embedding_lift f hf hk
  let e := MonoidHom.ofInjective embedding_injective
  refine ⟨s.comp e.symm.toMonoidHom, MonoidHom.ext fun x => ?_⟩
  change f (s (e.symm x)) = x
  exact (DFunLike.congr_fun hs (e.symm x)).trans
    (MonoidHom.apply_ofInjective_symm embedding_injective x)

/-- Three cannot divide the kernel of a finite perfect central cover of Sp₄(3). -/
theorem not_three_dvd_kernel {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3))) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := exists_section_on_range f.toMonoidHom f.surjective f.ker_le_center
  exact PerfectCentralCovering.not_dvd_card_kernel_of_section f embedding.range
    (by rw [index_range]; norm_num) s hs

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary
