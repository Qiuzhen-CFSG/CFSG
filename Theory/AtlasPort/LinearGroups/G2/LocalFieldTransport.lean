module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/LocalFieldTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration

/-!
Coefficientwise field transport carries the long-root generators and their
normal closure to the corresponding generators and closure over the target
field, yielding a multiplicative equivalence of the closures.
-/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F K : Type*} [Field F] [Field K]

theorem fieldEquiv_rootA (e : F ≃+* K) (a:F) : fieldEquiv e (rootA a)=rootA (e a) := by
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [fieldEquiv,transportAutomorphism,transportLinear,
    mapCoefficients,rootA,rootAEquiv,rootALinear,rootAApply]

theorem fieldEquiv_rootB (e : F ≃+* K) (a:F) : fieldEquiv e (rootB a)=rootB (e a) := by
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;> simp [fieldEquiv,transportAutomorphism,transportLinear,
    mapCoefficients,rootB,rootBEquiv,rootBLinear,rootBApply]

theorem fieldEquiv_longRootLocal_image (e : F ≃+* K) :
    fieldEquiv e '' (longRootLocal (F := F) : Set (Model F)) = longRootLocal (F := K) := by
  ext g
  constructor
  · rintro ⟨h,⟨p,rfl⟩,rfl⟩
    change fieldEquiv e (rootA p.toAdd.1*rootB p.toAdd.2) ∈ longRootLocal
    rw [map_mul,fieldEquiv_rootA,fieldEquiv_rootB]
    exact ⟨Multiplicative.ofAdd (_, _),rfl⟩
  · rintro ⟨p,rfl⟩
    refine ⟨rootA (e.symm p.toAdd.1)*rootB (e.symm p.toAdd.2),?_,?_⟩
    · exact ⟨Multiplicative.ofAdd (_, _),rfl⟩
    · simp only [map_mul,fieldEquiv_rootA,fieldEquiv_rootB,RingEquiv.apply_symm_apply]
      rfl

theorem fieldEquiv_longRootNormalClosure_map (e : F ≃+* K) :
    (longRootNormalClosure (F := F)).map (fieldEquiv e).toMonoidHom =
      longRootNormalClosure (F := K) := by
  rw [longRootNormalClosure,Subgroup.map_normalClosure _ _ (fieldEquiv e).surjective]
  change Subgroup.normalClosure (fieldEquiv e '' (longRootLocal (F := F) : Set (Model F))) = _
  rw [fieldEquiv_longRootLocal_image]
  rfl

def longRootNormalClosureFieldEquiv (e : F ≃+* K) :
    longRootNormalClosure (F := F) ≃* longRootNormalClosure (F := K) :=
  ((fieldEquiv e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (fieldEquiv_longRootNormalClosure_map e))

end Atlas.G2
