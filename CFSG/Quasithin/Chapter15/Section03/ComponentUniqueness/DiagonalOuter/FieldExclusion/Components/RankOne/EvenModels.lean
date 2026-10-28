module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.OuterRank
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.UnitaryThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.G2Ranks
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels.TwistedRanks
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL2.OuterSolvable.Semilinear
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.PrimeRankZero
public import Mathlib.Algebra.CharP.CharAndCard


/-!
# Characteristic-two cases of the rank-one automorphism inspection

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, A.2.3--4,
printed p.33, and the proof of 15.3.38, printed p.1137. The automorphism
structure is GLS3, Theorem 2.5.12 and Section 2.7.

Binary PSL₂ and PSL₄(2), PSL₅(2) have cyclic actual outer groups, by the
proved semilinear and point-radical reconstruction theorems. Together with
the given three-rank bound, `OuterRank` makes every exponent-three
subgroup of Aut(S) abelian. Suzuki is excluded by its three-free order;
the symplectic families are excluded by actual embedded copies of A₆.

For PSU₃ and PSL₃, the rank hypothesis eliminates the parameters with an
elementary subgroup of order nine. Proved arbitrary-automorphism coverage
then bounds the actual outer three-rank. The exceptional families, including
G₂(2)′ and the actual Tits carrier, have intrinsic three-rank at least two.
The final `cubic_of_bender` and `cubic_of_rank_two` theorems discharge every
premise of the preserved conditional assemblies. Together with
`cubic_of_linear_binary`, they cover the three characteristic-two constructors
of Theorem C without additional model or automorphism assumptions.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

private theorem psl2_char_two_outer_cyclic {F : Type*} [Field F] [Finite F] [CharP F 2] :
    IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) := by
  let I := MulAut.innerSubgroup (Theory.PSL2.Group F)
  let f := (QuotientGroup.mk' I).comp
    (Theory.PSL2.OuterSolvable.projectiveFieldAutHom (K := F))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I q
    obtain ⟨g, σ, ha⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
    have hσ : BenderSuzuki.ZD.Linear.fieldAut σ =
        Theory.PSL2.OuterSolvable.projectiveFieldAutHom σ := by
      rw [Theory.PSL2.OuterSolvable.projectiveFieldAutHom_eq_fieldAut]
      rfl
    rw [hσ] at ha
    refine ⟨σ, ?_⟩
    have hg : QuotientGroup.mk' I (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change QuotientGroup.mk' I (Theory.PSL2.OuterSolvable.projectiveFieldAutHom σ) = _
    rw [ha, map_mul, hg, one_mul]
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  exact isCyclic_of_surjective f hf

variable {S : Type*} [Group S] [Finite S]

/-- Binary PSL₂ has the required property, using proved coverage of arbitrary
automorphisms and its actual field outer quotient. -/
theorem cubic_of_psl2_even {f : ℕ}
    (hmodel : ClassicalGroup.IsPSL S 2 (2 ^ f)) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have ho := psl2_char_two_outer_cyclic (F := F)
  exact cubic_of_cyclic_outer hr.le ((MulAut.outerCongr e).isCyclic.mpr ho)

/-- The entire linear-binary constructor of Theorem C. No independent
order or simplicity certification is needed. -/
theorem cubic_of_linear_binary {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL S n 2) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eS := e.trans (Atlas.fieldEquivPSL n eF)
  exact cubic_of_cyclic_outer hr.le ((MulAut.outerCongr eS).isCyclic.mpr
    (BinaryLinear.OuterCyclic.psl_outer_isCyclic hn))

/-- Suzuki has three-rank zero, so it cannot occur under rank one. -/
theorem rank_ne_one_of_suzuki {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    primeRank 3 S ≠ 1 := by
  obtain ⟨e⟩ := hmodel
  have hcard : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
  have hz : primeRank 3 S = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hcard
  omega

/-- Conditional Bender assembly separating the unitary outer-rank calculation.
The final `cubic_of_bender` supplies this premise from semilinear coverage. -/
theorem cubic_of_bender_of_unitary_outer_rank
    (hU : ∀ f : ℕ, 2 ≤ f → ClassicalGroup.IsPSU S 3 (2 ^ f) →
      primeRank 3 (MulAut.Outer S) ≤ 1)
    (hmodel : ClassificationModels.IsBenderModel S) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S := by
  cases hmodel with
  | linear f _ iso => exact cubic_of_psl2_even iso hr
  | unitary f hf iso => exact cubic_of_outer_three_rank_le_one hr.le (hU f hf iso)
  | suzuki m hm iso => exact False.elim (rank_ne_one_of_suzuki hm iso hr)

/-- Conditional assembly of all eight rank-two constructors. The final
`cubic_of_rank_two` supplies the intrinsic outer-rank and exclusion premises. -/
theorem cubic_of_rank_two_of_intrinsic_facts {f : ℕ}
    (hL : 1 ≤ f → ClassicalGroup.IsPSL S 3 (2 ^ f) →
      primeRank 3 (MulAut.Outer S) ≤ 1)
    (hG : 2 ≤ f → ClassificationModels.IsG2At S (2 ^ f) → primeRank 3 S ≠ 1)
    (hT : 1 ≤ f → Triality.Standard.IsTrialityGroupAt (2 ^ f) S → primeRank 3 S ≠ 1)
    (hR : ∀ m : ℕ, 1 ≤ m → f = 2 * m + 1 → Nonempty (S ≃* ReeF4.Model m) →
      primeRank 3 S ≠ 1)
    (hGD : f = 1 → Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2))) →
      primeRank 3 S ≠ 1)
    (hTi : f = 1 → Nonempty (S ≃* Tits.ParrottGroup) → primeRank 3 S ≠ 1)
    (hmodel : ChapterA.Section02.IsTheoremCRankTwoModel S f) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S := by
  cases hmodel with
  | linear hf iso => exact cubic_of_outer_three_rank_le_one hr.le (hL hf iso)
  | symplectic _ iso => exact False.elim (rank_ne_one_of_symplectic_even iso hr)
  | g2 hf iso => exact False.elim (hG hf iso hr)
  | triality hf iso => exact False.elim (hT hf iso hr)
  | ree_f4 m hm hf iso => exact False.elim (hR m hm hf iso hr)
  | symplectic_derived _ iso => exact False.elim (rank_ne_one_of_symplectic_derived iso hr)
  | g2_derived hf iso => exact False.elim (hGD hf iso hr)
  | tits hf iso => exact False.elim (hTi hf iso hr)

private theorem unitary_semilinear_coverage : UnitaryThree.SemilinearCoverage := by
  intro E _ _ J n hn hJ hcard hfixed a
  exact J.semilinear_coverage n hn hJ hcard hfixed a

/-- The Bender alternative of Theorem C: every exponent-three subgroup of
the actual automorphism group is abelian when the model has three-rank one.
The unitary coverage premise is discharged for every field and Hermitian form. -/
theorem cubic_of_bender
    (hmodel : ClassificationModels.IsBenderModel S) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S :=
  cubic_of_bender_of_unitary_outer_rank
    (fun _ hf iso => UnitaryThree.outer_three_rank_le_one_of_coverage
      unitary_semilinear_coverage hf iso hr) hmodel hr

/-- The entire rank-two alternative of Theorem C, including the two small
derived groups and Tits. Standard coverage for binary PSL₃ and every
exceptional rank obstruction are discharged through actual model equivalences. -/
theorem cubic_of_rank_two [IsSimpleGroup S] (hna : ¬ IsMulCommutative S) {f : ℕ}
    (hmodel : ChapterA.Section02.IsTheoremCRankTwoModel S f) (hr : primeRank 3 S = 1) :
    CubicAutomorphismsAbelian S := by
  refine cubic_of_rank_two_of_intrinsic_facts ?_
    (fun hf iso => rank_ne_one_of_g2_even hf iso)
    (fun hf iso => rank_ne_one_of_triality hf iso)
    (fun _ hm _ iso => rank_ne_one_of_ree_f4 hm iso)
    (fun _ iso => rank_ne_one_of_g2_derived iso)
    (fun _ iso => rank_ne_one_of_tits iso) hmodel hr
  intro hf iso
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := iso
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  have hnaF : ¬ IsMulCommutative PSL(3,F) := by
    intro hcomm
    let := hcomm
    exact hna (IsMulCommutative.of_comm fun x y =>
      e.injective (by simp only [map_mul, mul_comm]))
  have hrF : primeRank 3 PSL(3,F) = 1 := (primeRank_equiv 3 e).symm.trans hr
  rw [primeRank_equiv 3 (MulAut.outerCongr e)]
  exact outer_three_rank_le_one_of_psl3_even hf hcard hnaF hrF
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hcard)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
