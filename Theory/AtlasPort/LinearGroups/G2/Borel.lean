module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Borel.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization
public import Mathlib.Tactic.Group

/-! The positive root group and split torus form the Borel subgroup; torus normalization proves closure. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {K : Type*} [Field K]

private theorem unipotentProduct_diagonal (t : Fin 6 → K) (i : Fin 8) :
    (unipotentProduct t).val (basisVector i) i = 1 := by
  fin_cases i <;> simp [unipotentProduct,basisVector,
    rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
    rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
    rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
    rootDApply,rootEApply,rootFApply]

theorem unipotent_disjoint_torus : Disjoint (unipotent (K := K)) splitTorus := by
  apply Subgroup.disjoint_def.mpr
  intro g hu ht
  rw [unipotent_eq_range] at hu
  obtain ⟨v,hv⟩ := hu
  obtain ⟨p,rfl⟩ := ht
  have h0 := congrArg (fun g : Model K => g.val (basisVector 0) 0) hv
  have h1 := congrArg (fun g : Model K => g.val (basisVector 1) 1) hv
  rw [unipotentProduct_diagonal] at h0 h1
  have hl : p.1 = 1 := by
    apply Units.ext
    simpa [torusHom,torus,torusEquiv,torusLinear,torusWeights,basisVector] using h0.symm
  have hm : p.2 = 1 := by
    apply Units.ext
    simpa [torusHom,torus,torusEquiv,torusLinear,torusWeights,basisVector] using h1.symm
  have hp : p = 1 := Prod.ext hl hm
  rw [hp,map_one]

theorem torus_normalizes_unipotent {t u : Model K}
    (ht : t ∈ splitTorus) (hu : u ∈ unipotent) : t*u*t⁻¹ ∈ unipotent := by
  obtain ⟨p,rfl⟩ := ht
  rw [unipotent_eq_range] at hu
  obtain ⟨v,rfl⟩ := hu
  change torus p.1 p.2 * unipotentProduct v * (torus p.1 p.2)⁻¹ ∈ unipotent
  rw [torus_unipotentProduct]
  exact unipotentProduct_mem _

private def borelRange : Subgroup (Model K) where
  carrier := {g | ∃ u ∈ unipotent, ∃ t ∈ splitTorus, g = u*t}
  one_mem' := ⟨1,unipotent.one_mem,1,splitTorus.one_mem,by simp⟩
  mul_mem' := by
    rintro x y ⟨u,hu,t,ht,rfl⟩ ⟨v,hv,s,hs,rfl⟩
    refine ⟨u*(t*v*t⁻¹), unipotent.mul_mem hu (torus_normalizes_unipotent ht hv),
      t*s,splitTorus.mul_mem ht hs,?_⟩
    group
  inv_mem' := by
    rintro x ⟨u,hu,t,ht,rfl⟩
    refine ⟨t⁻¹*u⁻¹*(t⁻¹)⁻¹,
      torus_normalizes_unipotent (splitTorus.inv_mem ht) (unipotent.inv_mem hu),
      t⁻¹,splitTorus.inv_mem ht,?_⟩
    group

def borel : Subgroup (Model K) := unipotent ⊔ splitTorus

private theorem borel_eq_range : (borel : Subgroup (Model K)) = borelRange := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      exact ⟨u,hu,1,splitTorus.one_mem,by simp⟩
    · intro t ht
      exact ⟨1,unipotent.one_mem,t,ht,by simp⟩
  · rintro g ⟨u,hu,t,ht,rfl⟩
    exact borel.mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ht)

noncomputable def borelProductEquiv :
    (unipotent (K := K) × splitTorus (K := K)) ≃ borel (K := K) :=
  Equiv.ofBijective (fun p => ⟨p.1.val*p.2.val,
    borel.mul_mem (Subgroup.mem_sup_left p.1.prop) (Subgroup.mem_sup_right p.2.prop)⟩) ⟨
      fun _ _ h => Subgroup.mul_injective_of_disjoint unipotent_disjoint_torus
        (congrArg Subtype.val h), by
      intro ⟨g,hg⟩
      rw [borel_eq_range] at hg
      obtain ⟨u,hu,t,ht,h⟩ := hg
      exact ⟨(⟨u,hu⟩,⟨t,ht⟩),Subtype.ext h.symm⟩⟩

theorem card_borel [Finite K] : Nat.card (borel (K := K)) =
    Nat.card K ^ 6 * (Nat.card K-1)^2 := by
  rw [← Nat.card_congr borelProductEquiv,Nat.card_prod,card_unipotent,card_splitTorus]
end Atlas.G2
