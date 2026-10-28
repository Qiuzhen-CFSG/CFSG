module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.Orders
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Models
public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.ElementaryAbelian.Quotient

/-!
# Separating odd linear-three groups from even-field models

Every elementary abelian two-subgroup of (S)L₃(p), for an odd prime p,
has order at most four, by the actual semidihedral or wreathed Sylow
presentations. In L₂(2ⁿ), the root group has order 2ⁿ; in L₃(2ⁿ),
a root plane has order 2²ⁿ. These injective matrix realizations force
field orders at most four and two respectively. Their remaining group
orders are too small for p ≥ 5.

The comparison for L₃ is projective. The caller must first pass to the
actual central quotients when its model is SL₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.21,
printed p.55, and proof of 1.3.8, p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion

variable {Q : Type*} [Group Q] [Finite Q]

private theorem linearThree_sylow_shape {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : XiEmbedding.LinearThreeModel p Q) (S : Sylow 2 Q) :
    Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S := by
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | hm
  · let _ : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hF)
    let f : Q ≃* SL(3,ZMod p) := e.trans (Atlas.fieldEquivSL 3 eF)
    let U := S.mapSurjective (f := f.toMonoidHom) f.surjective
    let eS : S ≃* U := f.subgroupMap (S : Subgroup Q)
    rcases ChapterA.Section03.sl3_sylow_shape p hp U with h | ⟨n, h⟩
    · exact Or.inl (ABG.semidihedral_equiv eS.symm h)
    · exact Or.inr ⟨n, ABG.wreathed_equiv eS.symm h⟩
  · exact XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_shape hp hm S

private theorem elementary_card_le_four {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : XiEmbedding.LinearThreeModel p Q) (E : Subgroup Q)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hES
  have h := (ABG.rank_two_and_cyclic_center_of_sylow_shape
    (linearThree_sylow_shape hp hm S)).2.1 (E.subgroupOf S) inferInstance
  rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at h

private theorem elementary_card_le_four_of_injective {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : XiEmbedding.LinearThreeModel p Q) {E : Type*} [Group E]
    [IsElementaryAbelian 2 E] (f : E →* Q) (hf : Function.Injective f) :
    Nat.card E ≤ 4 := by
  let _ := IsElementaryAbelian.of_surjective (p := 2) f.rangeRestrict f.rangeRestrict_surjective
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact elementary_card_le_four hp hm f.range

private theorem even_rankOne_field_bound {p n : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : XiEmbedding.LinearThreeModel p Q)
    (he : ClassicalGroup.IsPSL Q 2 (2 ^ n)) : 2 ^ n ≤ 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let _ : IsElementaryAbelian 2 (Multiplicative F) :=
    { exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro a
        rw [pow_two]
        change a.toAdd + a.toAdd = 0
        exact CharTwo.add_self_eq_zero _ }
  let f := (QuotientGroup.mk' (center SL(2,F))).comp
    (Matrix.SpecialLinearGroup.upperUnipotentHom F)
  have h := elementary_card_le_four_of_injective hp hm (e.symm.toMonoidHom.comp f)
    (e.symm.injective.comp (Matrix.SpecialLinearGroup.projectiveUpperUnipotentHom_injective F))
  change Nat.card F ≤ 4 at h
  rwa [hF] at h

private theorem even_linearThree_field_bound {p n : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL Q 3 p)
    (he : ClassicalGroup.IsPSL Q 3 (2 ^ n)) : (2 ^ n) ^ 2 ≤ 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := (Matrix.PSL3Even.UnipotentGeometry.projective F).comp
    (Matrix.PSL3Even.UnipotentGeometry.V₁ F).subtype
  have h := elementary_card_le_four_of_injective hp (Or.inr hm)
    (e.symm.toMonoidHom.comp f)
    (e.symm.injective.comp ((Matrix.PSL3Even.UnipotentGeometry.projective_injective F).comp
      (Matrix.PSL3Even.UnipotentGeometry.V₁ F).subtype_injective))
  rwa [Matrix.PSL3Even.UnipotentGeometry.card_V₁, hF] at h

/-- Neither odd-prime linear-three cover is an even-field rank-one group. -/
theorem not_even_rankOne_model {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (ho : Odd p) (hm : XiEmbedding.LinearThreeModel p Q) :
    ¬ ClassicalGroup.IsPSL Q 2 (2 ^ n) := by
  intro he
  have hbound := even_rankOne_field_bound ho hm he
  have hc := Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.even_psl_order he
  have hu := Nat.mul_le_mul hbound
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hbound 2) 1)
  norm_num at hu
  exact not_linearThree_of_small_order hp (by omega) hm

/-- Odd-prime PSL₃ cannot be identified with any even-field PSL₃. -/
theorem not_even_projective_model {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (ho : Odd p) (hm : ClassicalGroup.IsPSL Q 3 p) :
    ¬ ClassicalGroup.IsPSL Q 3 (2 ^ n) := by
  intro he
  have hbound := even_linearThree_field_bound ho hm he
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
  have hq : 1 < 2 ^ n := hF ▸ Finite.one_lt_card (α := F)
  have hq2 : 2 ^ n = 2 := by nlinarith
  have hc := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [← Nat.card_congr e.toEquiv, hF, hq2] at hc
  norm_num at hc
  exact not_linearThree_of_small_order hp (by omega) (Or.inr hm)

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
