module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/LongRootLocal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

/-! The two commuting long-root groups form the abelian local subgroup used in the singular-point stabilizer. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

theorem rootA_commute_rootB (a b : F) : Commute (rootA a) (rootB b) := by
  change rootA a * rootB b = rootB b * rootA a
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i
  fin_cases i <;> simp [rootA,rootB,rootAEquiv,rootBEquiv,rootALinear,rootBLinear,
    rootAApply,rootBApply]
  all_goals ring

/-- The two long-root parameters as an actual additive homomorphism. -/
def longRootHom : Multiplicative (F × F) →* Model F where
  toFun p := rootA p.toAdd.1 * rootB p.toAdd.2
  map_one' := by simp
  map_mul' p q := by
    change rootA (p.toAdd.1+q.toAdd.1) * rootB (p.toAdd.2+q.toAdd.2) = _
    rw [← rootA_add, ← rootB_add]
    exact ((rootA_commute_rootB q.toAdd.1 p.toAdd.2).symm.mul_mul_mul_comm _ _).symm

def longRootLocal : Subgroup (Model F) := longRootHom.range

instance longRootLocal_commutative : IsMulCommutative (longRootLocal (F := F)) := by
  refine .of_setLike_mul_comm ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem longRootHom_injective : Function.Injective (longRootHom (F := F)) := by
  intro p q h
  have ha := congrArg (fun g : Model F => g.val (basisVector 7) 1) h
  have hb := congrArg (fun g : Model F => g.val (basisVector 7) 2) h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · simpa [longRootHom,rootA,rootB,rootAEquiv,rootBEquiv,rootALinear,rootBLinear,
      rootAApply,rootBApply,basisVector] using ha
  · simpa [longRootHom,rootA,rootB,rootAEquiv,rootBEquiv,rootALinear,rootBLinear,
      rootAApply,rootBApply,basisVector] using hb

noncomputable def longRootParameterEquiv : Multiplicative (F × F) ≃* longRootLocal (F := F) :=
  MulEquiv.ofBijective (longRootHom (F := F)).rangeRestrict
    ⟨fun _ _ h => longRootHom_injective (congrArg Subtype.val h),
      (longRootHom (F := F)).rangeRestrict_surjective⟩

theorem card_longRootLocal [Finite F] : Nat.card (longRootLocal (F := F)) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr longRootParameterEquiv.toEquiv]
  change Nat.card (F × F) = _
  rw [Nat.card_prod,pow_two]

theorem rootA_mem_longRootLocal (a : F) : rootA a ∈ longRootLocal :=
  ⟨Multiplicative.ofAdd (a,0),by simp [longRootHom]⟩
theorem rootB_mem_longRootLocal (a : F) : rootB a ∈ longRootLocal :=
  ⟨Multiplicative.ofAdd (0,a),by simp [longRootHom]⟩

end Atlas.G2
