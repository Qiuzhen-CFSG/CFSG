module

public import Stellmacher.SectionEleven.UniqueMaximalSetup
public import Stellmacher.SectionEleven.UniquePairModel
public import Stellmacher.SectionEleven.UniqueNormalizer
public import Stellmacher.SectionEleven.UniqueDihedralTerminal
public import Stellmacher.SectionEleven.UniqueOrder32Terminal

/-!
# The unique-maximal branch of Theorem 2

The actual pair from (5.1) satisfies Hypothesis Two and has common subgroup
strictly smaller than the ambient Sylow subgroup. Its generated coset graph
has noncentral vertex centers and noncommuting critical endpoint centers, so
(8.2) gives the S4 or C2 × S4 model. The two-core normalizer theorem then
identifies the first member with its core normalizer, allowing the terminal
calculations to give precisely alternatives (b) or (c) of Theorem 2.

No model, normalizer equality, or graph hypothesis is assumed in the public
interface. Hypothesis Two remains on the original ambient group throughout.

Source: refs/latex/stellmacher-n-group.tex, Section 11, cases (I) and (II).
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

/-- A unique maximal two-local over the Sylow gives Theorem 2(b) or (c). -/
public theorem unique_maximal_branch
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
      (Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup H,
        IsMaximalTwoLocal U ∧
          Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) := by
  obtain ⟨S, P1, P2, hyp, hstrict⟩ := exists_unique_hypothesis_two S0 h hLocal M hM
  have hmodel := unique_pair_model hyp hstrict.ne
  have hnormalizer := unique_normalizer hyp hstrict.ne hmodel
  rcases hmodel with hdihedral | horder32
  · exact Or.inl (unique_dihedral_terminal hyp hstrict.ne hdihedral hnormalizer)
  · exact Or.inr
      (unique_order32_terminal S0 S P1 P2 hyp hstrict.ne horder32 hnormalizer)

end Stellmacher.SectionEleven
