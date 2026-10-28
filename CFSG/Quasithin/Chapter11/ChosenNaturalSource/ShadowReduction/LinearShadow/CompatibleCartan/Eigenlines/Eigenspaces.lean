module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Fields
/-!
# Eigenspaces inherited by the commutator

An actor centralizing W commutes with every displacement ρ(w) − 1.
Consequently the commutator of W with an a-eigenspace lies in the same
a-eigenspace. The inherited subgroup scalars give the literal
ScalarConjugation assertion consumed by the existing bilinear obstruction.
Scalar agreement on P ∩ V also identifies the inherited P-scalars with V.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
11.3.9, printed p.775. Constructing the actual Cartan actors remains separate.
-/

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
variable {G F : Type*} [Group G] [Field F] {P Y W : Subgroup G}
  [IsMulCommutative P] [Module F (Additive P)]

/-- A commuting actor preserves the scalar on every displacement image. -/
theorem scalar_on_commutatorFieldSpace (ρ : Representation F Y (Additive P))
    (hW : W ≤ Y) (U : Submodule F (Additive P)) (x : Y) (a : F)
    (hx : ∀ w : W, Commute (x : G) (w : G))
    (hU : ∀ u ∈ U, ρ x u = a • u) :
    ∀ v ∈ commutatorFieldSpace ρ hW U, ρ x v = a • v := by
  have hcomm (w : W) : Commute x (⟨w, hW w.property⟩ : Y) := Subtype.ext (hx w)
  intro v hv
  refine Submodule.iSup_induction (motive := fun v => ρ x v = a • v) _ hv ?_ ?_ ?_
  · intro w u hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [show ρ x (ρ ⟨w, hW w.property⟩ v) = ρ ⟨w, hW w.property⟩ (ρ x v) from
      congrArg (fun f : Module.End F (Additive P) => f v) ((hcomm w).map ρ).eq]
    rw [hU v hv, map_smul, smul_sub]
  · simp only [map_zero, smul_zero]
  · intro u v hu hv
    rw [map_add, hu, hv, smul_add]

/-- Eigenspace inheritance gives the actual ambient scalar-conjugation statement. -/
theorem scalarConjugation_commutatorFieldSpace
    (ρ : Representation F Y (Additive P))
    (hρ : ∀ (y : Y) (p : Additive P),
      ((ρ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G))
    (hW : W ≤ Y) (U : Submodule F (Additive P)) (x : Y) (a : F)
    (hx : ∀ w : W, Commute (x : G) (w : G))
    (hU : ∀ u ∈ U, ρ x u = a • u) :
    let C := commutatorFieldSpace ρ hW U
    letI := subgroupFieldModule C rfl
    ScalarConjugation (ambientSubgroup C) (x : G) a := by
  apply (scalarConjugation_iff _ rfl _ _).mpr
  intro u hu
  rw [← hρ, scalar_on_commutatorFieldSpace ρ hW U x a hx hU u hu]

variable {V Z : Subgroup G} [IsMulCommutative V] [IsMulCommutative Z]
  [Module F (Additive V)]
/-- The inherited commutator scalars agree with the V-scalars as well. -/
theorem subgroupFieldModule_smul_common (hcommon : ∀ (a : F) (b : Additive (P ⊓ V : Subgroup G)),
  ((a • (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
    ((a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (U : Submodule F (Additive P)) (hU : ambientSubgroup U = Z) (hZV : Z ≤ V)
    (a : F) (z : Additive Z) :
    letI := subgroupFieldModule U hU
    ((a • z).toMul : G) =
      ((a • (Subgroup.inclusion hZV).toAdditive z).toMul : G) := by
  let := subgroupFieldModule U hU
  rw [subgroupFieldModule_smul U hU]
  let b : Additive (P ⊓ V : Subgroup G) := Additive.ofMul
    ⟨z.toMul, (hU ▸ (show ambientSubgroup U ≤ P from map_subtype_le _)) z.toMul.property,
      hZV z.toMul.property⟩
  exact hcommon a b
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
