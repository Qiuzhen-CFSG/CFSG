module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.RemainingRows
public import Theory.SpecificGroups.Alternating.PositiveLocalCubicRank
public import Theory.SpecificGroups.BinaryLinear.PositiveLocalCubicRank
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.Catalogue
public import Theory.Mathieu.PositiveLocalCubicRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.PositiveLocalCubicRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.PositiveLocalCubicRank
public import Theory.SpecificGroups.Rudvalis.PositiveLocalCubicRank
public import Theory.SpecificGroups.Held.PositiveLocalCubicRank
public import Theory.SpecificGroups.Janko4.PositiveLocalCubicRank
public import Theory.SpecificGroups.Classical.BinaryPositiveLocalCubicRank
public import Theory.SpecificGroups.G2.PositiveLocalCubicRank
public import Theory.SpecificGroups.Triality.PositiveLocalCubicRank
public import Theory.SpecificGroups.ReeF4.PositiveLocalCubicRank
public import Theory.SpecificGroups.Tits.PositiveLocalCubicRank

/-!
# Remaining model rows under the nonnormal-component rank budget

The budget for a merely-quasithin nonnormal component combines its ordinary
odd-prime rank and its two-local rank. Actual nontrivial two-subgroup
normalizers give positive local cubic rank in every remaining finite and
binary row. Combining this with the existing elementary-nine witnesses
excludes the alternating degrees at least six, binary linear degrees four
and five, and all remaining sporadic and exceptional binary rows. The
alternating-five survivor retains its literal PSL₂(4) marking. The binary
degree-three row is preserved for its separate field-size argument.

Source: Aschbacher–Smith, A.1.34 and A.3.8, printed pp.29–30 and45–46.
No strongly-quasithin ambient hypothesis is used in these model deductions.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.QTComponents.RemainingRows
open Chapter1.Section02
open SQTKStructure.NonnormalOuterSource
variable {S : Type*} [Group S] [Finite S]

/-- The actual alternating model contributes a genuine local cubic witness. -/
theorem alternating_local_rank {n : ℕ} (hn : 4 ≤ n)
    (he : LocalModels.IsAlternating S n) : 1 ≤ twoLocalPrimeRank 3 S := by
  obtain ⟨e⟩ := he
  exact (Theory.Quasithin.alternating_one_le_twoLocalPrimeRank hn).trans
    (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)

/-- The alternating source row under the actual combined budget is the A₅ alias. -/
theorem alternating_model
    (hb : twoLocalPrimeRank 3 S + primeRank 3 S ≤ 2)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (he : LocalModels.IsAlternating S n) :
    NonnormalCComponentModel S := by
  have hl := alternating_local_rank (by omega : 4 ≤ n) he
  exact FourModels.alternating_model (by omega) n hn he

/-- The literal binary linear model has positive local cubic rank. -/
theorem binary_linear_local_rank (n : ℕ) (hn : n = 4 ∨ n = 5)
    (he : ClassicalGroup.IsPSL S n 2) : 1 ≤ twoLocalPrimeRank 3 S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let j := e.trans (Atlas.fieldEquivPSL n eF)
  exact (BinaryLinear.PositiveLocalCubicRank.projectiveSpecialLinear (by omega : 4 ≤ n)).trans
    (twoLocalPrimeRank_le_of_injective 3 j.symm.toMonoidHom j.symm.injective)

/-- Binary PSL₄ and PSL₅ contradict the sum of local and ordinary cubic ranks. -/
theorem not_binary_linear_model
    (hb : twoLocalPrimeRank 3 S + primeRank 3 S ≤ 2)
    (n : ℕ) (hn : n = 4 ∨ n = 5) (he : ClassicalGroup.IsPSL S n 2) : False := by
  have hl := binary_linear_local_rank n hn he
  have hr := FourModels.binary_linear_three_rank n hn he
  omega

/-- Each finite sporadic row has an actual two-local subgroup whose order
is divisible by three. The retained J₁ row is a separate source constructor. -/
theorem sporadic_carrier_local_rank (name : ClassificationModels.SporadicName)
    (hne : name ≠ .j3) : 1 ≤ twoLocalPrimeRank 3 name.Carrier := by
  cases name with
  | m11 => exact Sporadic.Mathieu.m11_one_le_twoLocalPrimeRank_three
  | m12 => exact Sporadic.Mathieu.m12_one_le_twoLocalPrimeRank_three
  | m22 => exact Sporadic.Mathieu.m22_one_le_twoLocalPrimeRank_three
  | m23 => exact Sporadic.Mathieu.m23_one_le_twoLocalPrimeRank_three
  | m24 => exact Sporadic.Mathieu.m24_one_le_twoLocalPrimeRank_three
  | j2 => exact Sporadic.LeechRelated.J2.one_le_twoLocalPrimeRank_three
  | hs => exact Sporadic.LeechRelated.HS.one_le_twoLocalPrimeRank_three
  | ru => exact Rudvalis.one_le_twoLocalPrimeRank_three
  | j3 => exact (hne rfl).elim
  | he => exact Held.one_le_twoLocalPrimeRank_three
  | j4 => exact Janko4.one_le_twoLocalPrimeRank_three

/-- The sporadic local witness is transported through the literal source marking. -/
theorem sporadic_local_rank (name : ClassificationModels.SporadicName)
    (hne : name ≠ .j3) (he : Nonempty (S ≃* name.Carrier)) :
    1 ≤ twoLocalPrimeRank 3 S := by
  obtain ⟨e⟩ := he
  let : Finite name.Carrier := Finite.of_injective e.symm e.symm.injective
  exact (sporadic_carrier_local_rank name hne).trans
    (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)

/-- Each remaining rank-two source row has a local cubic witness, including
the literal small derived and exceptional fixed-group models. -/
theorem rank_two_local_rank (hmodel : LocalModels.RankTwoTheoremC S) :
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL S 3 (2 ^ n)) ∨
      1 ≤ twoLocalPrimeRank 3 S := by
  cases hmodel with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | symplectic n _ he =>
    right
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := he
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    exact (Theory.SpecificGroups.Classical.BinaryPositiveLocalCubicRank.symplectic_projective
      (F := F)).trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | g2 n _ he =>
    right
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact (Theory.SpecificGroups.G2.PositiveLocalCubicRank.model (F := F)).trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | triality n hn he =>
    right
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S n (by omega)).mp he
    exact (Triality.Standard.PositiveLocalCubicRank.binary n (by omega)).trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | ree _ _ he =>
    right
    obtain ⟨d,⟨e⟩⟩ := he
    exact (ReeF4.PositiveLocalCubicRank.fixedGroup d).trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | symplectic_derived he =>
    right
    obtain ⟨e⟩ := he
    exact Theory.SpecificGroups.Classical.BinaryPositiveLocalCubicRank.symplectic_projective_derived_two.trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | g2_derived he =>
    right
    obtain ⟨e⟩ := he
    exact Theory.SpecificGroups.G2.PositiveLocalCubicRank.derived.trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)
  | tits he =>
    right
    obtain ⟨e⟩ := he
    exact Tits.parrott_one_le_twoLocalPrimeRank_three.trans
      (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)

end CFSG.Quasithin.ChapterA.QTComponents.RemainingRows

namespace CFSG.Quasithin.ChapterA.QTComponents
variable {S : Type*} [Group S] [Finite S]

/-- The concrete local witnesses discharge every remaining row of the
merely-quasithin component shortlist, with no additional model premise. -/
theorem remainingLocalInput : RemainingLocalInput S where
  alternating n hn he := RemainingRows.alternating_local_rank (by omega) he
  binary_linear := RemainingRows.binary_linear_local_rank
  sporadic := RemainingRows.sporadic_local_rank
  rank_two := RemainingRows.rank_two_local_rank

end CFSG.Quasithin.ChapterA.QTComponents
