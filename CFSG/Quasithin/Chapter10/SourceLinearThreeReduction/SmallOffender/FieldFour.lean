module
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import BenderSuzuki.Converse.PSL2

/-!
# Excluding the actual field-four quotient in the Chapter 10 reduction

In characteristic two the canonical map SL₂(F) → PSL₂(F) is an
isomorphism. For a field of order four, its composition with the faithful
five-point projective action identifies the actual quotient with A₅.
Thus the non-A₅ hypothesis excludes this alternative by an isomorphism,
not by comparing family names or group orders.

Source: the exceptional isomorphism SL₂(4) = PSL₂(4) = A₅, used for the
non-A₅ implication of Aschbacher--Smith 10.2.12, printed pp.754--755.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SmallOffender

/-- The canonical projective map followed by the actual five-point action. -/
theorem exists_slTwo_equiv_alternatingFive
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* alternatingGroup (Fin 5)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨e.trans a⟩

/-- Apply the actual exceptional isomorphism to any given quotient marking. -/
theorem not_slTwo_of_not_alternatingFive {Q : Type*} [Group Q]
    (hQ : ¬ Nonempty (Q ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) :
    ¬ Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  rintro ⟨e⟩
  obtain ⟨a⟩ := exists_slTwo_equiv_alternatingFive hF
  exact hQ ⟨e.trans a⟩

end CFSG.Quasithin.Chapter10.SmallOffender
