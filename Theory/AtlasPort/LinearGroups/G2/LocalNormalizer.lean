module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/LocalNormalizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.Parabolic

/-! The long-root local subgroup is normal in the point stabilizer, by checking its parabolic generators. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

theorem unipotent_conjugate_longRoot (t : Fin 6 → F) (a b : F) :
    unipotentProduct t * (rootA a * rootB b) * (unipotentProduct t)⁻¹ =
      rootA (a-b*t 4) * rootB b := by
  apply mul_inv_eq_of_eq_mul
  calc
    _ = unipotentProduct t * unipotentProduct ![a,b,0,0,0,0] := by simp [unipotentProduct]
    _ = unipotentProduct ![a-b*t 4,b,0,0,0,0] * unipotentProduct t := by
      rw [unipotentProduct_mul,unipotentProduct_mul]
      apply congrArg unipotentProduct
      funext i; fin_cases i <;> simp [unipotentProductParameters]
      all_goals ring
    _ = _ := by simp [unipotentProduct]

theorem unipotent_le_longRootNormalizer :
    unipotent (K := F) ≤ Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg k hk
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨p,rfl⟩ := hk
  change unipotentProduct t * (rootA p.toAdd.1 * rootB p.toAdd.2) * _ ∈ longRootLocal
  rw [unipotent_conjugate_longRoot]
  exact ⟨Multiplicative.ofAdd (_, _),rfl⟩

theorem torus_le_longRootNormalizer :
    splitTorus (K := F) ≤ Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro g ⟨⟨l,m⟩,rfl⟩ k ⟨p,rfl⟩
  change torus l m * (rootA p.toAdd.1 * rootB p.toAdd.2) * (torus l m)⁻¹ ∈ longRootLocal
  have he : torus l m * (rootA p.toAdd.1 * rootB p.toAdd.2) * (torus l m)⁻¹ =
      (torus l m * rootA p.toAdd.1 * (torus l m)⁻¹) *
      (torus l m * rootB p.toAdd.2 * (torus l m)⁻¹) := by group
  rw [he,torus_rootA,torus_rootB]
  exact ⟨Multiplicative.ofAdd (_, _),rfl⟩

theorem weylR_conjugate_longRoot (a b:F) :
    weylR * (rootA a * rootB b) * (weylR : Model F)⁻¹ = rootA b * rootB a := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [weylR,weylREquiv,weylRLinear,weylRApply,
    rootA,rootAEquiv,rootALinear,rootAApply,rootB,rootBEquiv,rootBLinear,rootBApply]
  all_goals ring

theorem weylR_mem_longRootNormalizer :
    (weylR : Model F) ∈ Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro k
  have hc (x : Model F) (hx : x ∈ longRootLocal) : weylR*x*weylR⁻¹ ∈ longRootLocal := by
    obtain ⟨p,rfl⟩ := hx
    change weylR * (rootA p.toAdd.1 * rootB p.toAdd.2) * _ ∈ longRootLocal
    rw [weylR_conjugate_longRoot]
    exact ⟨Multiplicative.ofAdd (_, _),rfl⟩
  constructor
  · exact hc k
  · intro h
    have h' := hc _ h
    have he : weylR * (weylR*k*weylR⁻¹) * (weylR : Model F)⁻¹ = k := by
      rw [weylR_inverse]
      have hh : (weylR:Model F)*weylR=1 := by simpa [pow_two] using weylR_sq (K := F)
      calc
        _ = (weylR*weylR)*k*(weylR*weylR) := by group
        _ = k := by rw [hh,one_mul,mul_one]
    exact he ▸ h'

theorem pointStabilizer_le_longRootNormalizer :
    pointStabilizer (K := F) ≤ Subgroup.normalizer (longRootLocal (F := F) : Set (Model F)) := by
  rw [← parabolic_eq_pointStabilizer]
  apply sup_le
  · exact sup_le unipotent_le_longRootNormalizer torus_le_longRootNormalizer
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g = weylR)
    exact weylR_mem_longRootNormalizer

theorem longRootLocal_le_unipotent : longRootLocal (F := F) ≤ unipotent := by
  rintro g ⟨p,rfl⟩
  exact unipotent.mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

theorem longRootLocal_le_pointStabilizer :
    longRootLocal (F := F) ≤ pointStabilizer :=
  le_trans longRootLocal_le_unipotent (le_trans unipotent_le_fixingFirstVector
    fixingFirstVector_le_pointStabilizer)

instance longRootLocal_normal_in_pointStabilizer :
    ((longRootLocal (F := F)).subgroupOf pointStabilizer).Normal where
  conj_mem n hn g := (Subgroup.mem_normalizer_iff.mp
    (pointStabilizer_le_longRootNormalizer g.prop) n.val).mp hn

end Atlas.G2
