module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction

/-!
# Marked root fusion for coefficient automorphisms of G₂(4)

The highest root A(1) lies in the center of the standard Sylow subgroup.
Inside the actual fixed subgroup, the square of a commutator of the cubic
F(1)s with B(1)E(1) equals A(1); the cubic's odd order places this element
in the two-residual. Choosing a field parameter of trace one then gives
an explicit displacement A(t), with σ(A(t)) A(t)⁻¹ = A(1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the G₂(4)
case of 16.4.9 on printed p.1191 and I.2.2(5a), p.409. The root-coordinate
formulas are those of the imported licensed ATLAS port. This calculation
uses the full fixed subgroup, without identifying it with its two-residual.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked
open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.LieAutomorphismExtensions
open CFSG.Quasithin.Chapter16.LiePreliminaries
open Theory.GroupTheory.DoubleCoverCentralizer
set_option linter.unusedSimpArgs false
open scoped commutatorElement CharTwo
variable {F : Type*} [Field F] [CharP F 2]

private theorem cubic_cube : (rootF (1 : F) * weylS)^3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [pow_succ, rootF, rootFEquiv, rootFLinear, rootFApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, CharTwo.neg_eq, add_assoc,
    CharTwo.add_self_eq_zero] <;> ring_nf <;> simp


set_option maxHeartbeats 800000 in
private theorem commutator_square : ⁅rootF (1 : F) * weylS, rootB (1 : F) * rootE 1⁆ ^ 2 = rootA (1 : F) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [commutatorElement_def, pow_two, mul_inv_rev,

    rootA, rootAEquiv, rootALinear, rootAApply,
    rootB, rootBEquiv, rootBLinear, rootBApply,
    rootE, rootEEquiv, rootELinear, rootEApply,
    rootF, rootFEquiv, rootFLinear, rootFApply,
    weylS, weylSEquiv, weylSLinear, weylSApply,
    CharTwo.neg_eq, sub_eq_add_neg, add_assoc, CharTwo.add_self_eq_zero] <;> ring_nf <;> simp

private theorem field_rootF_one (σ : F ≃+* F) : fieldAction σ (rootF (1 : F)) = rootF 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
    mapCoefficients, rootF, rootFEquiv, rootFLinear, rootFApply]

private theorem field_rootE_one (σ : F ≃+* F) : fieldAction σ (rootE (1 : F)) = rootE 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
    mapCoefficients, rootE, rootEEquiv, rootELinear, rootEApply]

private theorem field_weylS (σ : F ≃+* F) : fieldAction σ (weylS : Model F) = weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
    mapCoefficients, weylS, weylSEquiv, weylSLinear, weylSApply]

theorem rootA_one_twoCentral [Finite F] : TwoCentral (rootA (1 : F)) := by
  have hm : rootA (1 : F) ∈ (center (unipotent (K := F))).map unipotent.subtype := by
    rw [LieParabolicSetup.unipotent_center]
    exact ⟨Multiplicative.ofAdd 1, rfl⟩
  obtain ⟨v,hv,he⟩ := hm
  refine ⟨LieParabolicSetup.sylow, he ▸ v.property, ?_⟩
  change (⟨rootA (1 : F), _⟩ : unipotent) ∈ center unipotent
  have he' : (⟨rootA (1 : F), he ▸ v.property⟩ : unipotent) = v := Subtype.ext he.symm
  exact he'.symm ▸ hv

private theorem exists_displacement_one [Finite F] (hF : Nat.card F = 4) (σ : F ≃+* F) (hσ : σ ≠ 1) :
    ∃ t : F, σ t - t = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨t, ht⟩ : ∃ t : F, σ t ≠ t := by
    by_contra! h
    apply hσ
    ext x
    exact h x
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  have hs0 : σ t ≠ 0 := by simpa using ht0
  have hs1 : σ t ≠ 1 := by simpa using ht1
  have hall : ({0, 1, t, σ t} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hF]
    simp [ht0, ht1, hs0, hs1, ht, Ne.symm ht0, Ne.symm ht1,
      Ne.symm hs0, Ne.symm hs1, Ne.symm ht]
  have hh : t + 1 ∈ ({0, 1, t, σ t} : Finset F) := by rw [hall]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h | h
  · exact (ht1 (by have hh := eq_neg_of_add_eq_zero_left h; simpa using hh)).elim
  · exact (ht0 (add_right_cancel (h.trans (zero_add 1).symm))).elim
  · exact (one_ne_zero (add_left_cancel (h.trans (add_zero t).symm))).elim
  · refine ⟨t, ?_⟩
    rw [← h]
    simp [sub_eq_add_neg, add_comm t 1, add_assoc]

/-- The marked long-root involution is in the actual fixed-group two-residual. -/
theorem rootA_one_mem_fixedTwoResidual (σ : F ≃+* F) :
    rootA (1 : F) ∈ fixedTwoResidual (Model F) (fieldAction σ) := by
  let C := (fieldAction σ).fixedSubgroup
  have hc : rootF (1 : F) * weylS ∈ C := by
    rw [MulAut.mem_fixedSubgroup, map_mul, field_rootF_one, field_weylS]
  have hq : rootB (1 : F) * rootE 1 ∈ C := by
    rw [MulAut.mem_fixedSubgroup, map_mul, field_rootE_one]
    change fieldEquiv σ (rootB 1) * rootE 1 = _
    rw [fieldEquiv_rootB, map_one]
  let c : C := ⟨rootF 1 * weylS, hc⟩
  let q : C := ⟨rootB 1 * rootE 1, hq⟩
  have hc3 : c ^ 3 = 1 := Subtype.ext cubic_cube
  have hcr : c ∈ pResidual 2 C := mem_pResidual_of_orderOf_coprime
    (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hc3) (by decide : Nat.Coprime 2 3))
  have hcomm : ⁅c, q⁆ ∈ pResidual 2 C :=
    Subgroup.commutator_le_left _ _
      (Subgroup.commutator_mem_commutator hcr (Subgroup.mem_top _))
  exact ⟨⁅c, q⁆ ^ 2, pow_mem hcomm 2, commutator_square⟩

/-- The pure coefficient involution has the required marked residual fusion. -/
theorem field_twoCentralResidualFusion [Finite F]
    (hF : Nat.card F = 4) (σ : F ≃+* F) (hσ : σ ≠ 1) :
    TwoCentralResidualFusion (fieldAction σ) := by
  obtain ⟨t, ht⟩ := exists_displacement_one hF σ hσ
  refine ⟨rootA t, rootA 1, rootA_one_mem_fixedTwoResidual σ, ?_,
    rootA_one_twoCentral, ?_⟩
  · apply orderOf_eq_prime
    · rw [pow_two, Atlas.G2.rootA_add, CharTwo.add_self_eq_zero, rootA_zero]
    · intro h
      have he : rootA (1 : F) = rootA 0 := h.trans rootA_zero.symm
      exact one_ne_zero (rootA_injective he)
  · change fieldEquiv σ (rootA t) * (rootA t)⁻¹ = rootA 1
    have hinv : rootA (-t) = (rootA t)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [Atlas.G2.rootA_add, neg_add_cancel, rootA_zero]
    rw [fieldEquiv_rootA, ← hinv, Atlas.G2.rootA_add, ← sub_eq_add_neg, ht]

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked
