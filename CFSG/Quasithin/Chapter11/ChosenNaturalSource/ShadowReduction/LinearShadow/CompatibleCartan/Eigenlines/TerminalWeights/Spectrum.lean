module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Linear
public import Mathlib.LinearAlgebra.Prod
/-!
# Selecting the complementary plane from a split action

In split coordinates an operator has two distinct scalar planes. A scalar
plane of dimension two must be one of them. A disjoint invariant line must
lie in the other, so its eigenvalue and the complementary plane are constructed.
The source consumer uses this to select the primitive coefficient of W2.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
section Spectrum
variable {F M N : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N]
    (e : M ≃ₗ[F] (N × N)) (t : Module.End F M) (a b : F)
    (ht : ∀ v, e (t v) = (a • (e v).1, b • (e v).2))

private def firstPlane : Submodule F M := (LinearMap.range (LinearMap.inl F N N)).map e.symm.toLinearMap
private def secondPlane : Submodule F M := (LinearMap.range (LinearMap.inr F N N)).map e.symm.toLinearMap

private theorem mem_firstPlane (v : M) : v ∈ firstPlane e ↔ (e v).2 = 0 := by
  simp only [firstPlane, Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_,⟨u,rfl⟩,rfl⟩
    simp
  · intro hv
    exact ⟨((e v).1,0),⟨(e v).1,rfl⟩,by
      apply e.injective
      simpa using (Prod.ext rfl hv.symm : ((e v).1,0) = e v)⟩

private theorem mem_secondPlane (v : M) : v ∈ secondPlane e ↔ (e v).1 = 0 := by
  simp only [secondPlane, Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_,⟨u,rfl⟩,rfl⟩
    simp
  · intro hv
    exact ⟨(0,(e v).2),⟨(e v).2,rfl⟩,by
      apply e.injective
      simpa using (Prod.ext hv.symm rfl : (0,(e v).2) = e v)⟩

private theorem plane_complements : IsCompl (firstPlane e) (secondPlane e) :=
  (Submodule.orderIsoMapComap e.symm).isCompl_iff.mp LinearMap.isCompl_range_inl_inr

private theorem firstPlane_finrank : Module.finrank F (firstPlane e) = Module.finrank F N := by
  rw [firstPlane,LinearEquiv.finrank_map_eq]
  exact (LinearEquiv.ofInjective (LinearMap.inl F N N) (by
    intro u v h
    exact congrArg Prod.fst h)).finrank_eq.symm

private theorem secondPlane_finrank : Module.finrank F (secondPlane e) = Module.finrank F N := by
  rw [secondPlane,LinearEquiv.finrank_map_eq]
  exact (LinearEquiv.ofInjective (LinearMap.inr F N N) (by
    intro u v h
    exact congrArg Prod.snd h)).finrank_eq.symm

include ht in
private theorem eigenvalue_cases (v : M) (hv : v ≠ 0) (c : F) (hc : t v = c • v) :
    c = a ∨ c = b := by
  have hh := (ht v).symm.trans (congrArg e hc)
  rw [map_smul] at hh
  by_cases h₁ : (e v).1 = 0
  · right
    have h₂ : (e v).2 ≠ 0 := by
      intro h₂
      apply hv
      apply e.injective
      simpa using (Prod.ext h₁ h₂ : e v = 0)
    exact (smul_left_injective F h₂ (congrArg Prod.snd hh)).symm
  · left
    exact (smul_left_injective F h₁ (congrArg Prod.fst hh)).symm

include ht in
private theorem scalar_first (v : M) (hv : v ∈ firstPlane e) : t v = a • v := by
  apply e.injective
  rw [ht,map_smul]
  apply Prod.ext
  · rfl
  · simp [(mem_firstPlane e v).mp hv]

include ht in
private theorem scalar_second (v : M) (hv : v ∈ secondPlane e) : t v = b • v := by
  apply e.injective
  rw [ht,map_smul]
  apply Prod.ext
  · simp [(mem_secondPlane e v).mp hv]
  · rfl

include ht in
private theorem scalar_le_first (hab : a ≠ b) (U : Submodule F M)
    (hU : ∀ u ∈ U, t u = a • u) : U ≤ firstPlane e := by
  intro u hu
  apply (mem_firstPlane e u).mpr
  by_contra hh
  have h := congrArg Prod.snd ((ht u).symm.trans (congrArg e (hU u hu)))
  rw [map_smul] at h
  exact hab (smul_left_injective F hh h).symm

include ht in
private theorem scalar_le_second (hab : a ≠ b) (U : Submodule F M)
    (hU : ∀ u ∈ U, t u = b • u) : U ≤ secondPlane e := by
  intro u hu
  apply (mem_secondPlane e u).mpr
  by_contra hh
  have h := congrArg Prod.fst ((ht u).symm.trans (congrArg e (hU u hu)))
  rw [map_smul] at h
  exact hab (smul_left_injective F hh h)

variable [Module.Finite F N]
include ht in
/-- Identify the two scalar planes from an actual split operator, a scalar
plane and a disjoint invariant line. Neither complementary plane nor the
line's eigenvalue is assumed. -/
theorem complementary_spectrum (hN : Module.finrank F N = 2) (hab : a ≠ b)
    (U W : Submodule F M) (hUdim : Module.finrank F U = 2)
    (hWdim : Module.finrank F W = 1) (hUW : Disjoint U W)
    (c : F) (hU : ∀ u ∈ U, t u = c • u) (hW : ∀ w ∈ W, t w ∈ W) :
    ∃ Q : Submodule F M, ∃ d : F,
      IsCompl U Q ∧ W ≤ Q ∧ Module.finrank F Q = 2 ∧
      ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) ∧
      (∀ q ∈ Q, t q = d • q) := by
  let : Module.Finite F (N × N) := inferInstance
  let : Module.Finite F M := Module.Finite.equiv e.symm
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show U ≠ ⊥ from fun h => by rw [h,finrank_bot] at hUdim; omega)
  let tw : Module.End F W := t.restrict hW
  obtain ⟨d,hd,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hWdim tw
  have hwd (w : M) (hw : w ∈ W) : t w = d • w :=
    congrArg Subtype.val (LinearMap.congr_fun hd ⟨w,hw⟩)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show W ≠ ⊥ from fun h => by rw [h,finrank_bot] at hWdim; omega)
  have hcases := eigenvalue_cases e t a b ht w hw0 d (hwd w hw)
  rcases eigenvalue_cases e t a b ht u hu0 c (hU u hu) with hca | hcb
  · subst c
    have heU : U = firstPlane e := Submodule.eq_of_le_of_finrank_eq
      (scalar_le_first e t a b ht hab U hU) (hUdim.trans ((firstPlane_finrank e).trans hN).symm)
    have hdne : d ≠ a := by
      intro hd'
      have hwU : w ∈ U := heU ▸ scalar_le_first e t a b ht hab W (hd' ▸ hwd) hw
      exact hw0 (Submodule.disjoint_def.mp hUW w hwU hw)
    have hdb : d = b := hcases.resolve_left hdne
    refine ⟨secondPlane e,b,?_,?_,(secondPlane_finrank e).trans hN,Or.inl ⟨rfl,rfl⟩,
      scalar_second e t a b ht⟩
    · rw [heU]
      exact plane_complements e
    · exact scalar_le_second e t a b ht hab W (hdb ▸ hwd)
  · subst c
    have heU : U = secondPlane e := Submodule.eq_of_le_of_finrank_eq
      (scalar_le_second e t a b ht hab U hU) (hUdim.trans ((secondPlane_finrank e).trans hN).symm)
    have hdne : d ≠ b := by
      intro hd'
      have hwU : w ∈ U := heU ▸ scalar_le_second e t a b ht hab W (hd' ▸ hwd) hw
      exact hw0 (Submodule.disjoint_def.mp hUW w hwU hw)
    have hda : d = a := hcases.resolve_right hdne
    refine ⟨firstPlane e,a,?_,?_,(firstPlane_finrank e).trans hN,Or.inr ⟨rfl,rfl⟩,
      scalar_first e t a b ht⟩
    · rw [heU]
      exact (plane_complements e).symm
    · exact scalar_le_first e t a b ht hab W (hda ▸ hwd)
end Spectrum
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
