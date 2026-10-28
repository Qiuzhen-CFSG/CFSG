module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.FiniteModels.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Triality.ElementaryNine
public import Theory.SpecificGroups.ReeF4.CubicRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The finite and exceptional rows of the nonnormal-component inspection

The existing elementary-nine and noncyclic-three-subgroup certificates exclude
all sporadic rows except the separately retained J₁. Binary symplectic, G₂,
triality, Ree and Tits rows have the same obstruction. A₅ is preserved through
its actual PSL₂(4) comparison. These statements use literal model maps and
no recognition-by-order premise.

Source: Aschbacher–Smith A.1.34 and A.3.8(3), pp.29–30 and 45–46.
The imported concrete rank certificates retain their individual references.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
open Chapter1.Section02
variable {S : Type*} [Group S] [Finite S]

/-- The alternating source row of three-rank at most one is the A₅ alias. -/
theorem alternating_model (hr : primeRank 3 S ≤ 1)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (he : LocalModels.IsAlternating S n) :
    NonnormalCComponentModel S := by
  obtain ⟨e⟩ := he
  have hn6 : ¬ 6 ≤ n := by
    intro hh
    have hlow := alternatingGroup.TwoThreeCycles.two_le_primeRank hh
    rw [← primeRank_equiv 3 e] at hlow
    omega
  have hn5 : n = 5 := by omega
  subst n
  exact .linear_even 2 (by decide)
    ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩

/-- Every sporadic constructor in this source row has a concrete cubic rank witness. -/
theorem sporadic_three_rank (name : ClassificationModels.SporadicName) (hne : name ≠ .j3) :
    2 ≤ primeRank 3 name.Carrier := by
  open Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels in
    cases name with
    | m11 => exact m11_rank_ge_two
    | m12 => exact m12_rank_ge_two
    | m22 => exact m22_rank_ge_two
    | m23 => exact m23_rank_ge_two
    | m24 => exact m24_rank_ge_two
    | j2 => exact j2_rank_ge_two
    | hs => exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
    | ru => exact ru_rank_ge_two
    | j3 => exact (hne rfl).elim
    | he => exact held_rank_ge_two
    | j4 => exact j4_rank_ge_two

/-- The actual binary degree-four and degree-five projective rows contain an elementary nine. -/
theorem binary_linear_three_rank (n : ℕ) (hn : n = 4 ∨ n = 5)
    (he : ClassicalGroup.IsPSL S n 2) : 2 ≤ primeRank 3 S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let j := (e.trans (Atlas.fieldEquivPSL n eF)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n))
  rw [primeRank_equiv 3 j]
  exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by omega)

/-- Every rank-two source row other than binary PSL₃ has three-rank at least two. -/
theorem rank_two_rows (hmodel : LocalModels.RankTwoTheoremC S) :
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL S 3 (2 ^ n)) ∨ 2 ≤ primeRank 3 S := by
  cases hmodel with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | symplectic n _ he =>
    right
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := he
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    rw [primeRank_equiv 3 e,
      ← primeRank_equiv 3 (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F))]
    exact (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := F)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (symplecticGroup (Fin 2) F)).subtype Subtype.val_injective)
  | g2 n _ he =>
    right
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    rw [primeRank_equiv 3 e]
    exact (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype Subtype.val_injective)
  | triality n hn he =>
    right
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S n (by omega)).mp he
    rw [primeRank_equiv 3 e]
    obtain ⟨E,hE,hcard⟩ := Triality.Standard.exists_elementaryAbelian_three_card_nine n (by omega)
    let := hE
    exact IsElementaryAbelian.primeRank_ge_of_card E (by simpa using hcard)
  | ree _ _ he =>
    right
    obtain ⟨d,⟨e⟩⟩ := he
    rw [primeRank_equiv 3 e]
    exact ReeF4.CubicRank.fixedGroup d
  | symplectic_derived he =>
    right
    rw [primeRank_equiv 3 (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  | g2_derived he =>
    right
    rw [primeRank_equiv 3 he.some]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  | tits he =>
    right
    rw [primeRank_equiv 3 (he.some.trans Tits.parrottFiniteImageEquiv)]
    exact Tits.ThreeRank.rank_two_le

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
