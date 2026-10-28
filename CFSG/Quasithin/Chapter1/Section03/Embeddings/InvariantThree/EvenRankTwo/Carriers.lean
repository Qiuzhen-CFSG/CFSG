module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction

/-!
# Concrete carrier comparisons for the rank-two sieve

The existing six-letter polar representation identifies PSp4(2)' with A6.
Composing with it routes the small derived symplectic constructor to the
alternating-pair exclusion, which remains an independent proof obligation.

For the surviving case, characteristic two identifies PSp4 with the full
symplectic matrix group. If the multiplier argument has established Z(Q) = 1,
the given central-quotient isomorphism then identifies Q itself with Sp4.
The final helper inserts the even-degree and mod-three restrictions.
Neither triviality of Z(Q) nor the torus congruence is proved by this carrier
comparison, and no classification alternative follows without those inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
universe u
variable {Q : Type u} [Group Q]

-- This identifies a constructor using the already proved polar representation.
/-- Transport the derived symplectic constructor through the actual polar isomorphism. -/
theorem symplectic_derived_is_alternating_six
    (h : Nonempty ((Q ⧸ center Q) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    Section02.LocalModels.IsAlternating (Q ⧸ center Q) 6 := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

-- The multiplier calculation must establish hcenter before this is used.
/-- A centerless cover of the projective model is the full symplectic matrix carrier. -/
theorem full_symplectic_of_projective_quotient {n : ℕ}
    (hcenter : center Q = ⊥)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Q ≃* Matrix.symplecticGroup (Fin 2) F) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let _ := hF
  let _ := hfin
  let _ := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let q : Q ≃* (Q ⧸ center Q) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact ⟨F, hF, hfin, hcard, ⟨q.trans
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)⟩⟩

/-- Package the full carrier and both source parameter restrictions after their
multiplier and torus hypotheses have been established. -/
theorem symplectic_model_of_projective_quotient {n : ℕ}
    (hcenter : center Q = ⊥)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2 ^ n))
    (hmod : Nat.ModEq 3 (2 ^ n) 1) : SymplecticModel 3 Q :=
  ⟨n, (two_pow_modEq_one_iff_even n).mp hmod, hmod,
    full_symplectic_of_projective_quotient hcenter hmodel⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
