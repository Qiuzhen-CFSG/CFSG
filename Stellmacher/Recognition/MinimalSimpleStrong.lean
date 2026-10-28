module

public import Stellmacher.Recognition.MinimalSimpleBasic
public import Stellmacher.Recognition.EvenUnitaryNotN

/-!
# The strongly embedded branch for minimal simple groups

A minimal simple group in the Bender--Suzuki catalogue is a binary PSL2 or a
Suzuki group. The even-unitary models fail the all-prime N condition by the
proved nonsolvable torus-centralizer obstruction. Minimal simplicity implies
that condition, and isomorphism transport transfers it to the concrete model.
Applying Bender--Suzuki therefore proves the same conclusion from an actual
strongly embedded subgroup.

These are actual group isomorphisms, with the existing lower parameter bounds.
Primality of the field exponent is a separate subsequent theorem, not an
assumption or a conclusion of this reduction.

Source: Bender--Suzuki, as exported by BenderSuzuki.FinalTheorem; the explicit
unitary obstruction in Stellmacher.Recognition.EvenUnitaryNotN.
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G]

/-- The unitary alternative of Bender--Suzuki is impossible for a minimal simple group. -/
public theorem minimalSimple_bender_recognition (hG : IsMinimalSimple G)
    (hB : IsSimpleBenderGroup G) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL2Model n)) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) := by
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e⟩⟩
  · exact (not_isNGroup_PSU3Model n hn
      ((isNGroup_iff_of_mulEquiv e).mp hG.isNGroup)).elim

/-- Strongly embedded minimal simple groups are binary PSL2 or Suzuki models. -/
public theorem minimalSimple_strong_recognition (hG : IsMinimalSimple G)
    (M : Subgroup G) (hM : IsStronglyEmbedded M) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL2Model n)) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) := by
  let _ := hG.isSimpleGroup
  exact minimalSimple_bender_recognition hG (bender_suzuki M hM)

end Stellmacher.Recognition
