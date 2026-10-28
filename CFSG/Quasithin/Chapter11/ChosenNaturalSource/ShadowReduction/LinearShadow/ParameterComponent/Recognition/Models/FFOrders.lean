module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRankOne

/-!
# Root orders in the nonlinear source rows

The full root groups have orders q² for Suzuki, q³ for the signed three-space
groups and q⁴ for Sp₄. Thus every nonlinear source model at its literal field
exponent has order divisible by 64. Intrinsic two-core quotient orders divide
along subgroup inclusions, via the image in the larger two-core quotient.
This argument never assumes that the smaller two-core lies in the larger one.

FFSource carries the divisibility through the original star projection and
uses it to exclude every finite exceptional FF container.
Source: Aschbacher--Smith, E.2.2 and 11.3.5, printed pp.215--216,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

private theorem quotient_order_dvd {X : Type*} [Group X] [Finite X]
    (A : Subgroup X) : Nat.card (A ⧸ pCore 2 A) ∣ Nat.card (X ⧸ pCore 2 X) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := (q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk
  rw [Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card _).trans (A.map q).card_subgroup_dvd_card

/-- Intrinsic quotient orders divide along the actual inclusion, even
though the smaller two-core need not lie in the larger two-core. -/
theorem quotient_order_dvd_of_le {G : Type*} [Group G] [Finite G]
    {K J : Subgroup G} (hKJ : K ≤ J) :
    Nat.card (K ⧸ pCore 2 K) ∣ Nat.card (J ⧸ pCore 2 J) := by
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))
  rw [← Nat.card_congr e.toEquiv]
  exact quotient_order_dvd (K.subgroupOf J)

/-- The whole Suzuki root group, rather than only its elementary center,
supplies the factor 64 for every surviving source exponent. -/
theorem sixtyFour_dvd_suzuki {X : Type*} [Group X] [Finite X] {m : ℕ}
    (hm : 1 ≤ m) (e : X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    64 ∣ Nat.card X := by
  rw [Nat.card_congr e.toEquiv]
  have hd := (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m).card_subgroup_dvd_card
  rw [BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card m (by omega), ← pow_mul] at hd
  exact (Nat.pow_dvd_pow 2 (by omega : 6 ≤ (2*m+1)*2)).trans hd

/-- Each nonlinear normal source image has a two-subgroup of order at
least 64. These are literal star images, with no assumed cover splitting. -/
theorem sixtyFour_dvd_higher_rank {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL X 3 (2 ^ n) ∨ ClassicalGroup.IsPSp X 2 (2 ^ n)) :
    64 ∣ Nat.card X := by
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
    obtain ⟨a⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2 ^ n) hF hfixed
    let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    have hd := (BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup J₀ rfl).card_subgroup_dvd_card
    rw [BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J₀ rfl
      (2 ^ n) hF hfixed, ← pow_mul] at hd
    rw [Nat.card_congr (e.trans a).toEquiv]
    exact (Nat.pow_dvd_pow 2 (by omega : 6 ≤ n*3)).trans hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hd := card_dvd_of_injective (Matrix.PSL3Even.UnipotentGeometry.projective F)
      (Matrix.PSL3Even.UnipotentGeometry.projective_injective (F := F))
    rw [Matrix.PSL3Even.UnipotentGeometry.card_U,hF,← pow_mul] at hd
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.pow_dvd_pow 2 (by omega : 6 ≤ n*3)).trans hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,← pow_mul] at hd
    rw [Nat.card_congr a.toEquiv]
    exact (Nat.pow_dvd_pow 2 (by omega : 6 ≤ n*4)).trans hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
