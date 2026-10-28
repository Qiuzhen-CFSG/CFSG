module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/LongRootNormalGeneration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.LongRootLocal
public import Theory.AtlasPort.LinearGroups.G2.Generation
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Weyl conjugation and rank-one words show that the long-root local subgroup normally generates G₂ when the field has more than two elements. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

theorem weylR_inverse : (weylR : Model F)⁻¹ = weylR :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_two] using weylR_sq (K := F))
theorem weylS_inverse : (weylS : Model F)⁻¹ = weylS :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_two] using weylS_sq (K := F))

theorem weylR_rootA (a : F) : weylR * rootA a * weylR⁻¹ = rootB a := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [weylR,weylREquiv,weylRLinear,weylRApply,
    rootA,rootAEquiv,rootALinear,rootAApply,rootB,rootBEquiv,rootBLinear,rootBApply]
  all_goals ring

theorem weylS_rootB (a : F) : weylS * rootB a * weylS⁻¹ = rootE a := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [weylS,weylSEquiv,weylSLinear,weylSApply,
    rootB,rootBEquiv,rootBLinear,rootBApply,rootE,rootEEquiv,rootELinear,rootEApply]
  all_goals ring

theorem weylR_rootD (a : F) : weylR * rootD a * weylR⁻¹ = rootF a := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [weylR,weylREquiv,weylRLinear,weylRApply,
    rootD,rootDEquiv,rootDLinear,rootDApply,rootF,rootFEquiv,rootFLinear,rootFApply]
  all_goals ring

theorem rootF_neg (a : F) : rootF (-a) = (rootF a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rootF_add,neg_add_cancel,rootF_zero]

theorem rootD_neg (a : F) : rootD (-a) = (rootD a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rootD_add,neg_add_cancel,rootD_zero]

/-- A short-root conjugation of E, verified in the unique six-parameter chart. -/
theorem rootF_conjugate_rootE (a t : F) :
    rootF t * rootE a * rootF (-t) =
      rootA (-a^2*t^3) * rootB (-a*t^3) * rootC (a*t^2) * rootD (-a*t) * rootE a := by
  calc
    _ = unipotentProduct ![0,0,0,0,0,t] * unipotentProduct ![0,0,0,0,a,0] *
        unipotentProduct ![0,0,0,0,0,-t] := by simp [unipotentProduct]
    _ = unipotentProduct ![-a^2*t^3,-a*t^3,a*t^2,-a*t,a,0] := by
      rw [unipotentProduct_mul,unipotentProduct_mul]
      apply congrArg unipotentProduct
      funext i; fin_cases i <;> simp [unipotentProductParameters]
    _ = _ := by simp [unipotentProduct]

/-- Any normal subgroup containing A contains U once the field has a third element. -/
theorem unipotent_le_normal_of_rootA (H : Subgroup (Model F)) [H.Normal]
    (hA : ∀ a : F, rootA a ∈ H) (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    unipotent (K := F) ≤ H := by
  have hB (a : F) : rootB a ∈ H := by
    rw [← weylR_rootA]
    exact (inferInstance : H.Normal).conj_mem _ (hA a) _
  have hE (a : F) : rootE a ∈ H := by
    rw [← weylS_rootB]
    exact (inferInstance : H.Normal).conj_mem _ (hB a) _
  let π : Model F →* Model F ⧸ H := QuotientGroup.mk' H
  have hqA (a : F) : π (rootA a) = 1 := (QuotientGroup.eq_one_iff _).mpr (hA a)
  have hqB (a : F) : π (rootB a) = 1 := (QuotientGroup.eq_one_iff _).mpr (hB a)
  have hqE (a : F) : π (rootE a) = 1 := (QuotientGroup.eq_one_iff _).mpr (hE a)
  have hrel (a s : F) : π (rootC (a*s^2)) * π (rootD (-a*s)) = 1 := by
    have hc : rootF s * rootE a * rootF (-s) ∈ H := by
      rw [rootF_neg]
      exact (inferInstance : H.Normal).conj_mem _ (hE a) _
    have hq : π (rootF s * rootE a * rootF (-s)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    rw [rootF_conjugate_rootE] at hq
    simpa only [map_mul,hqA,hqB,hqE,one_mul,mul_one] using hq
  have hCD (a : F) : π (rootC a) = π (rootD a) := by
    have h := hrel a 1
    simp only [one_pow,mul_one,rootD_neg,map_inv] at h
    exact mul_inv_eq_one.mp h
  have hC (a : F) : rootC a ∈ H := by
    have ht : t^2-t ≠ 0 := by
      rw [show t^2-t = t*(t-1) by ring]
      exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
    have h := hrel (a/(t^2-t)) t
    rw [← hCD, ← map_mul,rootC_add] at h
    have he : a/(t^2-t)*t^2 + -(a/(t^2-t))*t = a := by field_simp; ring
    rw [he] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  have hD (a : F) : rootD a ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (rootD a) = 1
    rw [← hCD]
    exact (QuotientGroup.eq_one_iff _).mpr (hC a)
  have hF (a : F) : rootF a ∈ H := by
    rw [← weylR_rootD]
    exact (inferInstance : H.Normal).conj_mem _ (hD a) _
  apply (Subgroup.closure_le H).mpr
  intro g hg
  rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
  all_goals obtain ⟨a,rfl⟩ := hg
  · exact hA a
  · exact hB a
  · exact hC a
  · exact hD a
  · exact hE a
  · exact hF a

/-- Normal closure of the actual two-dimensional long-root local subgroup. -/
def longRootNormalClosure : Subgroup (Model F) :=
  Subgroup.normalClosure (longRootLocal (F := F) : Set (Model F))

instance longRootNormalClosure_normal : (longRootNormalClosure (F := F)).Normal := by
  unfold longRootNormalClosure
  infer_instance

theorem unipotent_le_longRootNormalClosure [Finite F] (hq : 2 < Nat.card F) :
    unipotent (K := F) ≤ longRootNormalClosure := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  apply unipotent_le_normal_of_rootA longRootNormalClosure
    (fun a => Subgroup.subset_normalClosure (rootA_mem_longRootLocal a)) t ht'.1 ht'.2

end Atlas.G2

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

 theorem long_rank_one_word (a : Fˣ) :
    rootE (a:F) * (weylR * rootE (-(a⁻¹:Fˣ):F) * weylR⁻¹) * rootE (a:F) =
      torus (-1) a * weylR := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [rootE,rootEEquiv,rootELinear,rootEApply,
    weylR,weylREquiv,weylRLinear,weylRApply,torus,torusEquiv,torusLinear,torusWeights]
  all_goals field_simp
  all_goals ring

 theorem short_rank_one_word (a : Fˣ) :
    rootF (a:F) * (weylS * rootF (-(a⁻¹:Fˣ):F) * weylS⁻¹) * rootF (a:F) =
      torus a (-a⁻¹) * weylS := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply,
    weylS,weylSEquiv,weylSLinear,weylSApply,torus,torusEquiv,torusLinear,torusWeights]
  all_goals field_simp
  all_goals ring
end Atlas.G2

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

 theorem torus_product (l m a b : Fˣ) : torus l m * torus a b = torus (l*a) (m*b) :=
  (torusHom (K := F)).map_mul (l,m) (a,b) |>.symm
 theorem torus_inverse (l m : Fˣ) : (torus l m)⁻¹ = torus l⁻¹ m⁻¹ :=
  (torusHom (K := F)).map_inv (l,m) |>.symm
 theorem torus_identity : torus (1:Fˣ) 1 = 1 := (torusHom (K := F)).map_one

 theorem normal_eq_top_of_unipotent (H : Subgroup (Model F)) [H.Normal]
    (hU : unipotent (K := F) ≤ H) : H = ⊤ := by
  have hE (a:F) : rootE a ∈ H :=
    hU (Subgroup.subset_closure (by simp))
  have hF (a:F) : rootF a ∈ H :=
    hU (Subgroup.subset_closure (by simp))
  have hlong (a:Fˣ) : torus (-1) a * weylR ∈ H := by
    rw [← long_rank_one_word]
    exact H.mul_mem (H.mul_mem (hE _) ((inferInstance : H.Normal).conj_mem _ (hE _) _)) (hE _)
  have hshort (a:Fˣ) : torus a (-a⁻¹) * weylS ∈ H := by
    rw [← short_rank_one_word]
    exact H.mul_mem (H.mul_mem (hF _) ((inferInstance : H.Normal).conj_mem _ (hF _) _)) (hF _)
  have htm (a:Fˣ) : torus 1 a ∈ H := by
    have h := H.mul_mem (hlong a) (H.inv_mem (hlong 1))
    rw [mul_inv_rev,← mul_assoc,mul_assoc (torus (-1) a),mul_inv_cancel,mul_one,
      torus_inverse,torus_product] at h
    simpa using h
  have htd (a:Fˣ) : torus a a⁻¹ ∈ H := by
    have h := H.mul_mem (hshort a) (H.inv_mem (hshort 1))
    rw [mul_inv_rev,← mul_assoc,mul_assoc (torus a (-a⁻¹)),mul_inv_cancel,mul_one,
      torus_inverse,torus_product] at h
    simpa using h
  have ht (a b:Fˣ) : torus a b ∈ H := by
    have h := H.mul_mem (htd a) (htm (a*b))
    rw [torus_product] at h
    simpa using h
  have hr : (weylR : Model F) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht (-1) 1)) (hlong 1)
    simpa only [inv_mul_cancel_left] using h
  have hs : (weylS : Model F) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht 1 (-1))) (hshort 1)
    simpa only [inv_one,inv_mul_cancel_left] using h
  apply top_unique
  rw [← generated_eq_top]
  apply sup_le
  · apply (Subgroup.closure_le H).mpr
    intro g hg
    rcases hg with hg | hg
    · exact hU hg
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hr
      · exact hs
  · rintro g ⟨⟨a,b⟩,rfl⟩
    exact ht a b

 theorem longRootNormalClosure_eq_top [Finite F] (hq : 2 < Nat.card F) :
    longRootNormalClosure (F := F) = ⊤ :=
  normal_eq_top_of_unipotent _ (unipotent_le_longRootNormalClosure hq)
end Atlas.G2
