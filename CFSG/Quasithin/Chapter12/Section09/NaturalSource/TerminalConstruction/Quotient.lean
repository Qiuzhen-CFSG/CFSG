module

public import Theory.GroupTheory.SymmetricThreeTwoCoreGeneration
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalGeometry

/-!
# The literal symmetric-three quotient in the terminal construction

An escaping two-subgroup A has image of order two in H/O₂(H), so A∩O₂(H)
is a hyperplane of A. Its H-conjugates cover the quotient. Since O₂(H)≤T
normalizes the plane, an H which moves the plane has a conjugate of A which
moves it. The proof keeps the given quotient map and right-conjugation convention.

Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {X : Type u} [Group X]

/-- The core intersection has index two and the conjugates cover the quotient. -/
theorem core_hyperplane_and_generation
    (H A : Subgroup X) (hAH : A ≤ H) (hp : IsPGroup 2 A)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ A ≤ H.pCoreIn 2) :
    (A ⊓ H.pCoreIn 2).relIndex A = 2 ∧
      conjugateSpanBy A H ⊔ H.pCoreIn 2 = H := by
  obtain ⟨e⟩ := he
  exact Subgroup.core_hyperplane_and_generation H A hAH hp hout e

/-- Quotient generation produces an actual moving conjugate inside H. -/
theorem exists_moving_conjugate_of_generation
    {T : Sylow 2 X} (H A P : Subgroup X)
    (ht : H.pCoreIn 2 ≤ (T : Subgroup X))
    (hTP : (T : Subgroup X) ≤ normalizer (P : Set X))
    (hgen : conjugateSpanBy A H ⊔ H.pCoreIn 2 = H)
    (hout : ¬ H ≤ normalizer (P : Set X)) :
    ∃ k ∈ H, ¬ conjugate A k ≤ normalizer (P : Set X) := by
  by_contra! hh
  apply hout
  rw [← hgen]
  apply sup_le ?_ (ht.trans hTP)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  simpa only [conjugate, inv_inv] using hh k⁻¹ (H.inv_mem k.property)
end CFSG.Quasithin.Chapter12.Section09.NaturalSource
