module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.QuotientCoverage
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Theory.Mathieu.M22.TripleCover
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The covering extension in the first J₄ centralizer

The two matrix generators generate a quotient of order two over their actual
perfect derived subgroup. The marked odd generator inverts the scalar of order
three. Conjugation on the native M₂₂ quotient is onto and has exactly this scalar
kernel. Thus the full matrix group retains the triple covering kernel.

Source: Aschbacher–Smith 16.1.5(9), printed p.1172, interpreted by the explicit
covering extension in GLS3 Table 5.3i. No splitting is inferred from dot notation.
The underlying ATLAS matrix certificates retain their attribution in LinearModel.
-/

@[expose] public section

namespace Janko4.InvolutionCentralizers.First.QuotientExtension

open Subgroup
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu

/-- The genuine inclusion of the concrete triple cover into the full action group. -/
def coverInclusion : M22TripleCover →* actionGroup :=
  Subgroup.inclusion derivedGroup_le_actionGroup

/-- The actual derived subgroup, now a subgroup of the action group. -/
def coverSubgroup : Subgroup actionGroup := derivedGroup.subgroupOf actionGroup

instance coverSubgroup_normal : coverSubgroup.Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (actionGroup.le_normalizer.trans normalizer_actionGroup_le_normalizer_derivedGroup)

theorem coverInclusion_range : coverInclusion.range = coverSubgroup := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩

/-- The marked original generator outside the perfect core. -/
def outerElement : actionGroup := ⟨unitC, unitC_mem_actionGroup⟩

/-- The scalar, embedded in the full group without taking a central quotient. -/
def scalarElement : actionGroup := coverInclusion M22TripleCover.scalar

theorem outerElement_sq : outerElement ^ 2 = 1 := Subtype.ext unitC_pow_two

theorem scalarElement_order : orderOf scalarElement = 3 := by
  rw [scalarElement, orderOf_injective coverInclusion (Subgroup.inclusion_injective _),
    M22TripleCover.scalar_order]

/-- The marked outer element inverts the central scalar of the cover. -/
theorem outerElement_conj_scalar :
    outerElement * scalarElement * outerElement⁻¹ = scalarElement⁻¹ := by
  have hi : scalarUnit ^ 2 = scalarUnit⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using scalarUnit_pow_three
  exact Subtype.ext (unitC_conj_scalarUnit.trans hi)

theorem outerElement_moves_scalar :
    outerElement * scalarElement * outerElement⁻¹ ≠ scalarElement := by
  intro h
  have hs : scalarElement ^ 2 = 1 := by
    rw [outerElement_conj_scalar] at h
    calc
      scalarElement ^ 2 = scalarElement * scalarElement := pow_two _
      _ = scalarElement⁻¹ * scalarElement := congrArg (fun z => z * scalarElement) h.symm
      _ = 1 := inv_mul_cancel _
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [scalarElement_order] at hd
  norm_num at hd

theorem outerElement_not_mem_cover : outerElement ∉ coverSubgroup := by
  intro h
  have hz := Subgroup.mem_center_iff.mp M22TripleCover.scalar_mem_center
    (⟨unitC, h⟩ : M22TripleCover)
  apply outerElement_moves_scalar
  apply Subtype.ext
  change unitC * scalarUnit * unitC⁻¹ = scalarUnit
  have hc := congrArg (fun x : M22TripleCover => (x : Matrix12ˣ)) hz
  change unitC * scalarUnit = scalarUnit * unitC at hc
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem coverQuotient_generated (x : actionGroup ⧸ coverSubgroup) :
    x ∈ Subgroup.zpowers (QuotientGroup.mk' coverSubgroup outerElement) := by
  let f := QuotientGroup.mk' coverSubgroup
  let P := (Subgroup.zpowers (f outerElement)).comap f
  have h : actionGroup ≤ P.map actionGroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro y (rfl | rfl)
    · exact ⟨outerElement, Subgroup.mem_zpowers _, rfl⟩
    · let d : actionGroup := ⟨unitD, unitD_mem_actionGroup⟩
      have hcd : f (outerElement * d) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr coreA_mem_derivedGroup
      have hc2 : f outerElement * f outerElement = 1 := by
        rw [← map_mul]
        exact (congrArg f (by simpa only [pow_two] using outerElement_sq)).trans (map_one f)
      have hd : f d = f outerElement := by
        apply mul_left_cancel (a := f outerElement)
        rw [← map_mul, hcd, hc2]
      exact ⟨d, by change f d ∈ Subgroup.zpowers (f outerElement); rw [hd]; exact Subgroup.mem_zpowers _, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective coverSubgroup x
  obtain ⟨y, hy, he⟩ := h g.property
  exact (Subtype.ext he : y = g) ▸ hy

theorem coverSubgroup_index : coverSubgroup.index = 2 := by
  rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers coverQuotient_generated]
  apply orderOf_eq_prime
  · rw [← map_pow, outerElement_sq, map_one]
  · intro h
    exact outerElement_not_mem_cover ((QuotientGroup.eq_one_iff _).mp h)

/-- The index-two quotient, with its generator marked by the original matrix C. -/
noncomputable def coverQuotientEquiv :
    (actionGroup ⧸ coverSubgroup) ≃* Multiplicative (ZMod 2) :=
  (zmodMulEquivOfGenerator coverQuotient_generated coverSubgroup_index).symm

/-- The concrete quotient character of the full matrix group. -/
noncomputable def outerCharacter : actionGroup →* Multiplicative (ZMod 2) :=
  coverQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' coverSubgroup)

theorem outerCharacter_ker : outerCharacter.ker = coverSubgroup := by
  rw [outerCharacter, MonoidHom.ker_comp_of_injective (QuotientGroup.mk' coverSubgroup)
    coverQuotientEquiv.toMonoidHom coverQuotientEquiv.injective,
    QuotientGroup.ker_mk']

theorem outerCharacter_surjective : Function.Surjective outerCharacter :=
  coverQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem outerCharacter_outerElement :
    outerCharacter outerElement = Multiplicative.ofAdd (1 : ZMod 2) := by
  change (zmodMulEquivOfGenerator coverQuotient_generated coverSubgroup_index).symm
    (QuotientGroup.mk' coverSubgroup outerElement) = _
  simpa only [zpow_one, Int.cast_one] using
    zmodMulEquivOfGenerator_symm_apply_zpow coverQuotient_generated coverSubgroup_index (1 : ℤ)

/-- The actual covering extension 3.M₂₂.2. Its left map is the derived inclusion. -/
noncomputable def coveringExtension :
    GroupExtension M22TripleCover actionGroup (Multiplicative (ZMod 2)) where
  inl := coverInclusion
  rightHom := outerCharacter
  inl_injective := Subgroup.inclusion_injective _
  range_inl_eq_ker_rightHom := coverInclusion_range.trans outerCharacter_ker.symm
  rightHom_surjective := outerCharacter_surjective

theorem coveringExtension_inl (x : M22TripleCover) :
    coveringExtension.inl x = coverInclusion x := rfl

theorem coveringExtension_rightHom (x : actionGroup) :
    coveringExtension.rightHom x = outerCharacter x := rfl

/-- The actual conjugation action, transported along the proved cover quotient. -/
noncomputable def quotientConjugation : actionGroup →* MulAut M22 :=
  (MulAut.centralQuotientAction M22TripleCover.centralQuotientEquiv).comp derivedConjugation

theorem quotientConjugation_surjective : Function.Surjective quotientConjugation :=
  (MulAut.congr M22TripleCover.centralQuotientEquiv).surjective.comp
    (derivedQuotientConjugation_surjective_of_equiv
      derivedGroup_eq_closure M22TripleCover.centralQuotientEquiv)

/-- The scalar subgroup is an actual subgroup of the full action group. -/
def scalarSubgroup : Subgroup actionGroup :=
  (Subgroup.center M22TripleCover).map coverInclusion

theorem scalarSubgroup_eq_zpowers : scalarSubgroup = Subgroup.zpowers scalarElement := by
  rw [scalarSubgroup, M22TripleCover.center_eq_zpowers, MonoidHom.map_zpowers]
  rfl

theorem coverInclusion_mem_scalar (x : M22TripleCover) :
    coverInclusion x ∈ scalarSubgroup ↔ x ∈ Subgroup.center M22TripleCover := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subgroup.inclusion_injective derivedGroup_le_actionGroup he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The marked scalar as an element of the scalar subgroup. -/
def scalarGenerator : scalarSubgroup :=
  ⟨scalarElement, ⟨M22TripleCover.scalar, M22TripleCover.scalar_mem_center, rfl⟩⟩

theorem scalarGenerator_order : orderOf scalarGenerator = 3 := by
  rw [← orderOf_injective scalarSubgroup.subtype Subtype.val_injective]
  exact scalarElement_order

theorem scalarSubgroup_generated (x : scalarSubgroup) :
    x ∈ Subgroup.zpowers scalarGenerator := by
  have hx := x.property
  have hx' : x.val ∈ Subgroup.zpowers scalarElement :=
    (congrArg (fun S : Subgroup actionGroup => x.val ∈ S) scalarSubgroup_eq_zpowers).mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

theorem scalarSubgroup_card : Nat.card scalarSubgroup = 3 := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers scalarSubgroup_generated, scalarGenerator_order]

/-- The scalar section, with its specified generator, is the cyclic group of order three. -/
noncomputable def scalarSubgroupEquivC3 : scalarSubgroup ≃* Multiplicative (ZMod 3) :=
  (zmodMulEquivOfGenerator scalarSubgroup_generated scalarSubgroup_card).symm

theorem scalarSubgroup_le_cover : scalarSubgroup ≤ coverSubgroup := by
  rw [scalarSubgroup, ← coverInclusion_range]
  exact Subgroup.map_le_range coverInclusion (Subgroup.center M22TripleCover)

private theorem centralizing_mem_derived (g : actionGroup)
    (hg : derivedConjugation g = 1) : (g : Matrix12ˣ) ∈ derivedGroup := by
  have commute_core (x : derivedGroup) :
      (x : Matrix12ˣ) * g.val = g.val * (x : Matrix12ˣ) := by
    have hx := congrArg (fun x : derivedGroup => (x : Matrix12ˣ))
      (DFunLike.congr_fun hg x)
    change g.val * x.val * g.val⁻¹ = x.val at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hA : Commute (g.val : Matrix12) matrixA := by
    change (g.val : Matrix12) * matrixA = matrixA * (g.val : Matrix12)
    have h := congrArg Units.val (commute_core coreGeneratorA)
    simpa only [Units.val_mul, coreGeneratorA, coe_coreA] using h.symm
  have hB : Commute (g.val : Matrix12) matrixB := by
    change (g.val : Matrix12) * matrixB = matrixB * (g.val : Matrix12)
    have h := congrArg Units.val (commute_core coreGeneratorB)
    simpa only [Units.val_mul, coreGeneratorB, coe_coreB] using h.symm
  rcases commuting_matrix_cases hA hB with h | h | h | h
  · exact (Units.ne_zero g.val h).elim
  · exact (Units.ext h : g.val = 1).symm ▸ derivedGroup.one_mem
  · exact (Units.ext (h.trans coe_scalarUnit_sq.symm) : g.val = scalarUnit ^ 2).symm ▸
      derivedGroup.pow_mem scalarUnit_mem_derivedGroup 2
  · exact (Units.ext (h.trans coe_scalarUnit.symm) : g.val = scalarUnit).symm ▸
      scalarUnit_mem_derivedGroup

/-- Perfectness and the matrix commutant determine the exact covering kernel. -/
theorem quotientConjugation_ker : quotientConjugation.ker = scalarSubgroup := by
  ext g
  constructor
  · intro hg
    have h : derivedConjugation g = 1 :=
      MulAut.centralQuotientAction_injective M22TripleCover.centralQuotientEquiv
        ((show quotientConjugation g = 1 from hg).trans
          (map_one (MulAut.centralQuotientAction M22TripleCover.centralQuotientEquiv)).symm)
    let x : M22TripleCover := ⟨g.val, centralizing_mem_derived g h⟩
    refine ⟨x, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro y
    apply Subtype.ext
    have hy := congrArg (fun x : derivedGroup => (x : Matrix12ˣ))
      (DFunLike.congr_fun h y)
    change g.val * y.val * g.val⁻¹ = y.val at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  · rintro ⟨x, hx, rfl⟩
    have h : derivedConjugation (coverInclusion x) = 1 := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      change x.val * y.val * x.val⁻¹ = y.val
      have hc := congrArg (fun x : derivedGroup => (x : Matrix12ˣ))
        (Subgroup.mem_center_iff.mp hx y)
      change y.val * x.val = x.val * y.val at hc
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    change MulAut.centralQuotientAction _ (derivedConjugation (coverInclusion x)) = 1
    rw [h, map_one]

instance scalarSubgroup_normal : scalarSubgroup.Normal :=
  quotientConjugation_ker ▸ quotientConjugation.normal_ker

/-- Quotienting only the three-element covering kernel gives the native Aut(M₂₂). -/
noncomputable def scalarQuotientEquiv :
    (actionGroup ⧸ scalarSubgroup) ≃* MulAut M22 :=
  (QuotientGroup.quotientMulEquivOfEq quotientConjugation_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective quotientConjugation
      quotientConjugation_surjective)

theorem scalarQuotientEquiv_mk (g : actionGroup) :
    scalarQuotientEquiv (QuotientGroup.mk' scalarSubgroup g) = quotientConjugation g := rfl

theorem quotientConjugation_apply (g : actionGroup) (x : M22TripleCover) :
    quotientConjugation g
      (M22TripleCover.centralQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center M22TripleCover) x)) =
      M22TripleCover.centralQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center M22TripleCover) (derivedConjugation g x)) :=
  MulAut.centralQuotientAction_apply _ _ _

theorem quotientConjugation_outer :
    ¬ ∃ x : M22, quotientConjugation outerElement = MulAut.conj x := by
  intro h
  obtain ⟨x, hx⟩ := (MulAut.centralQuotientAction_inner_iff
    M22TripleCover.centralQuotientEquiv (derivedConjugation outerElement)).mp h
  have hz : derivedConjugation outerElement M22TripleCover.scalar =
      M22TripleCover.scalar := by
    rw [hx]
    change x * M22TripleCover.scalar * x⁻¹ = M22TripleCover.scalar
    rw [Subgroup.mem_center_iff.mp M22TripleCover.scalar_mem_center x,
      mul_assoc, mul_inv_cancel, mul_one]
  apply outerElement_moves_scalar
  apply Subtype.ext
  exact congrArg (fun x : derivedGroup => (x : Matrix12ˣ)) hz

end Janko4.InvolutionCentralizers.First.QuotientExtension
