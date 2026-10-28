module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The quasisimple rows on a binary six-space with Sylow order at most sixteen

The original opposite-plane normalizer acts faithfully on its elementary
subgroup of order 64. Its Sylow quotient has order sixteen, rather than the
elementary order-eight bound used in the earlier even-affine exclusion.
Here the genuine B.5 source models are reduced using that larger bound.
The additional rank-one candidate SL₂(16) is excluded by its element of
order seventeen: a faithful binary representation has dimension at least
eight. The alternating-five, alternating-six, alternating-seven and cubic
alternating-six markings are retained, including the actual cubic center.

This is a row sieve for the original 12.7.7 normalizer comparison, not an
identification of the whole ambient normalizer or of its full centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem two_power_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16)
    {n : ℕ} (hd : 2 ^ n ∣ Nat.card D) : n ≤ 4 := by
  let S : Sylow 2 D := default
  have h := S.pow_dvd_card_of_pow_dvd_card hd
  have hb : 2 ^ n ≤ 2 ^ 4 :=
    (Nat.le_of_dvd (Nat.card_pos (α := S)) h).trans (small S)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

private def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq, h]
    simp)

private theorem no_seventeen (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 6)
    (hp : 17 ∣ Nat.card D) : False := by
  have h := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 17) (by decide) hp
  rw [BinaryPrimeDegree.orderOf_two_mod_seventeen] at h
  omega

/-- The marked small B.5 models retain exactly these four possibilities
under the actual six-space, Sylow-sixteen and five-divisibility bounds. -/
theorem smallModel_rows (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16) (hfive : 5 ∣ Nat.card D)
    (m : ChapterC.C27Source.SmallModels.Model D) :
    Nonempty (D ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (center D ≃* Multiplicative (ZMod 3)) ∧
        Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 6)) := by
  cases m with
  | linearTwo F lower _ e =>
    have upper : F.degree ≤ 4 := by
      apply two_power_le small
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
      exact dvd_mul_right _ _
    have hcases : F.degree = 2 ∨ F.degree = 3 ∨ F.degree = 4 := by omega
    rcases hcases with hF | hF | hF
    · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (K := F.Carrier) (by rw [F.card_eq, hF]; decide)
      exact Or.inl ⟨e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans a)⟩
    · rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula,
        F.card_eq, hF] at hfive
      norm_num at hfive
    · exact (no_seventeen ρ hf hd (by
        rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq, hF]
        decide)).elim
  | linearThree F _ e =>
    have hu := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul] at hu
    have hb := two_power_le small (by
      rw [Nat.card_congr e.toEquiv]
      exact hu)
    have hF : F.degree = 1 := by have := F.degree_pos; omega
    let a := e.trans (Atlas.fieldEquivSL 3 (fieldTwoEquiv F hF))
    rw [Nat.card_congr a.toEquiv, Matrix.PSL3Two.card_SL] at hfive
    norm_num at hfive
  | alternatingSix e => exact Or.inr (Or.inl ⟨e⟩)
  | alternatingSeven e => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | tripleSix ec eq => exact Or.inr (Or.inr (Or.inr ⟨⟨ec⟩, ⟨eq⟩⟩))
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hfive
    norm_num at hfive
  | linearFourTwo e =>
    have hb := two_power_le small (n := 6) (by
      rw [Nat.card_congr e.toEquiv, Atlas.Order20160A8.sl4Two_card]
      decide)
    omega

variable {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]

/-- Apply the sieve directly to a genuine marked B.5 moved-section source.
The independent faithful six-space can be the restriction of the whole
normalizer action; it need not equal the moved-section quotient. -/
theorem quasisimple_source_rows (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16) (hfive : 5 ∣ Nat.card D)
    (hq : IsQuasisimple D) (σ : Representation (ZMod 2) A X)
    (L : Subgroup A) (e : D ≃* L)
    (source : ProjectiveLine.QuasisimpleSourceConclusion σ L) :
    Nonempty (D ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (center D ≃* Multiplicative (ZMod 3)) ∧
        Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 6)) := by
  exact smallModel_rows ρ hf hd small hfive
    (ChapterC.C27Source.SmallModels.model_of_source σ
      (fun S => (small S).trans (by decide)) hq e source)

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
