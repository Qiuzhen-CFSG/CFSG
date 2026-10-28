/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryHexadProjection.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolaySupports
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# TernaryHexadProjection

Restriction to a hexad has a one-dimensional kernel and the orthogonal phase space as image.
Minimum distance bounds the kernel and rank-nullity proves surjectivity onto the hyperplane.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryHexadProjection.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def ternaryRestriction (S : Finset (Fin 12)) : ternaryGolay →ₗ[ZMod 3] (S → ZMod 3) where
  toFun w i := w.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ternaryRestriction_kernel_support (S : Finset (Fin 12)) (hS : S.card=6)
    (w : (ternaryRestriction S).ker) (hw : w≠0) :
    ternarySupport w.val.val=Sᶜ := by
  have hsub : ternarySupport w.val.val ⊆ Sᶜ := by
    intro i hi
    have hn : w.val.val i ≠ 0 := (Finset.mem_filter.mp hi).2
    apply Finset.mem_compl.mpr
    intro his
    have he := LinearMap.mem_ker.mp w.prop
    exact hn (congrFun he ⟨i,his⟩)
  have hn : w.val.val ≠ 0 := fun h => hw (Subtype.ext (Subtype.ext h))
  have hm := ternaryGolay_minimum _ w.val.prop hn
  have hc : Sᶜ.card=6 := by rw [Finset.card_compl,Fintype.card_fin,hS]
  apply Finset.eq_of_subset_of_card_le hsub
  simpa only [hc,ternarySupport_card] using hm

theorem ternaryRestriction_kernel_finrank_le (S : Finset (Fin 12)) (hS : S.card=6) :
    Module.finrank (ZMod 3) (ternaryRestriction S).ker ≤ 1 := by
  classical
  by_cases hz : ∀ w : (ternaryRestriction S).ker,w=0
  · apply finrank_le_one (0 : (ternaryRestriction S).ker)
    intro w
    exact ⟨0,by rw [hz w,smul_zero]⟩
  obtain ⟨v,hv⟩ := not_forall.mp hz
  apply finrank_le_one v
  intro w
  by_cases hw : w=0
  · exact ⟨0,by rw [hw,zero_smul]⟩
  have hs := ternaryRestriction_kernel_support S hS v hv
  have ht := ternaryRestriction_kernel_support S hS w hw
  have hcard : Sᶜ.card=6 := by rw [Finset.card_compl,Fintype.card_fin,hS]
  have hvs : ternaryWeight v.val.val=6 := by rw [← ternarySupport_card,hs,hcard]
  have hws : ternaryWeight w.val.val=6 := by rw [← ternarySupport_card,ht,hcard]
  have hi : 5 ≤ (ternarySupport v.val.val ∩ ternarySupport w.val.val).card := by
    rw [hs,ht,Finset.inter_self,hcard]; decide
  rcases ternaryGolay_hexad_intersection _ _ v.val.prop w.val.prop hvs hws hi with he | he
  · exact ⟨1,by simpa only [one_smul] using (Subtype.ext (Subtype.ext he)).symm⟩
  · exact ⟨-1,by simpa only [neg_one_smul] using (Subtype.ext (Subtype.ext he)).symm⟩

def ternaryHexadFunctional (c : TernarySixWords) :
    (ternarySupport c.val.val → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun a := ∑ i,c.val.val i.val*a i
  map_add' a b := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.mul_sum,mul_comm,mul_assoc]

theorem ternaryHexadFunctional_surjective (c : TernarySixWords) :
    Function.Surjective (ternaryHexadFunctional c) := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro h
  have hc : (ternarySupport c.val.val).Nonempty := by
    apply Finset.card_pos.mp
    rw [ternarySupport_card,c.prop]; decide
  obtain ⟨i,hi⟩ := hc
  have hn := (Finset.mem_filter.mp hi).2
  have he := LinearMap.congr_fun h (Pi.single (⟨i,hi⟩ : ternarySupport c.val.val) 1)
  apply hn
  simpa [ternaryHexadFunctional,Pi.single_apply,mul_ite] using he

theorem ternaryHexadFunctional_kernel_finrank (c : TernarySixWords) :
    Module.finrank (ZMod 3) (ternaryHexadFunctional c).ker = 5 := by
  have h := (ternaryHexadFunctional c).finrank_range_add_finrank_ker
  have hr := LinearMap.range_eq_top.mpr (ternaryHexadFunctional_surjective c)
  rw [hr] at h
  have hs : Fintype.card (ternarySupport c.val.val)=6 := by
    rw [Fintype.card_coe,ternarySupport_card,c.prop]
  simp only [finrank_top,Module.finrank_self,Module.finrank_pi,hs] at h
  omega

theorem ternaryHexadRestriction_le (c : TernarySixWords) :
    (ternaryRestriction (ternarySupport c.val.val)).range ≤ (ternaryHexadFunctional c).ker := by
  rintro _ ⟨w,rfl⟩
  apply LinearMap.mem_ker.mpr
  change (∑ i : ternarySupport c.val.val,c.val.val i.val*w.val i.val)=0
  have h := ternaryGolay_selfOrthogonal w.prop c.val.val c.val.prop
  change (∑ i,c.val.val i*w.val i)=0 at h
  rw [Finset.sum_coe_sort _ (fun i => c.val.val i*w.val i)]
  have he : (∑ i ∈ ternarySupport c.val.val,c.val.val i*w.val i) =
      ∑ i,c.val.val i*w.val i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    have hz : c.val.val i=0 := by simpa [ternarySupport] using hn
    rw [hz,zero_mul]
  rw [he,h]

/-- Every phase assignment orthogonal to a hexad word is the restriction of an
actual codeword. The proof uses minimum six and rank-nullity, uniformly in the hexad. -/
theorem ternaryHexadRestriction_range (c : TernarySixWords) :
    (ternaryRestriction (ternarySupport c.val.val)).range = (ternaryHexadFunctional c).ker := by
  apply Submodule.eq_of_le_of_finrank_eq (ternaryHexadRestriction_le c)
  have hk := ternaryRestriction_kernel_finrank_le (ternarySupport c.val.val) c.prop
  have h := (ternaryRestriction (ternarySupport c.val.val)).finrank_range_add_finrank_ker
  rw [ternaryGolay_finrank] at h
  have hr := Submodule.finrank_mono (ternaryHexadRestriction_le c)
  rw [ternaryHexadFunctional_kernel_finrank] at hr ⊢
  omega

theorem ternaryHexadPhase_card (c : TernarySixWords) :
    Nat.card (ternaryHexadFunctional c).ker = 243 := by
  classical
  let := Fintype.ofFinite (ternaryHexadFunctional c).ker
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 3),
    ternaryHexadFunctional_kernel_finrank]
  norm_num

theorem ternaryHexadPhase_lift (c : TernarySixWords)
    (a : ternarySupport c.val.val → ZMod 3)
    (ha : ∑ i,c.val.val i.val*a i=0) :
    ∃ w : ternaryGolay, ∀ i : ternarySupport c.val.val,w.val i.val=a i := by
  have hm : a ∈ (ternaryRestriction (ternarySupport c.val.val)).range := by
    rw [ternaryHexadRestriction_range]
    exact ha
  obtain ⟨w,hw⟩ := hm
  exact ⟨w,fun i => congrFun hw i⟩

theorem ternaryHexadRestriction_kernel_finrank (c : TernarySixWords) :
    Module.finrank (ZMod 3) (ternaryRestriction (ternarySupport c.val.val)).ker=1 := by
  have h := (ternaryRestriction (ternarySupport c.val.val)).finrank_range_add_finrank_ker
  rw [ternaryHexadRestriction_range,ternaryHexadFunctional_kernel_finrank,
    ternaryGolay_finrank] at h
  omega

theorem ternaryHexadRestriction_kernel_card (c : TernarySixWords) :
    Nat.card (ternaryRestriction (ternarySupport c.val.val)).ker=3 := by
  classical
  let := Fintype.ofFinite (ternaryRestriction (ternarySupport c.val.val)).ker
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 3),
    ternaryHexadRestriction_kernel_finrank]
  norm_num

end Atlas.Codes
