module
public import Theory.GroupAction.FixedQuotientMap
public import Theory.GroupTheory.EmbeddedCenterMap
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels

/-!
# Return the original MS source model from the join

The component used by the MS reduction is the original K restricted to
J=K∨T. Injective ambient maps preserve the literal center commutator
U=[Z(O₂(K)),K]: transport the two-core through the subgroup-image
equivalence, then its embedded center, then its commutator with K.

The model transport therefore returns a quotient model on the actual K and U
from the model constructed inside J. Its actor stays surjective and has
exactly O₂(K) as kernel. This neither replaces K by its simple quotient nor
changes the supplied binary representation.

Source: Aschbacher–Smith, C.1.34 and 13.6.22, printed pp.136–137 and 932–933.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
variable {G H A V : Type*} [Group G] [Group H] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) A V}

/-- The source center commutator commutes with an injective ambient map. -/
theorem sourceU_map_injective (K : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    (sourceU K).map f = sourceU (K.map f) := by
  let e := K.equivMapOfInjective f hf
  have he : f.comp K.subtype = (K.map f).subtype.comp e.toMonoidHom := rfl
  rw [sourceU, sourceU, map_commutator]
  congr 1
  rw [map_map, he, ← map_map, map_embeddedCenter _ _ e.injective, pCore_map_iso]

/-- Restriction to an overgroup followed by its inclusion recovers the actual U. -/
theorem sourceU_subgroupOf_map (K J : Subgroup G) (hK : K ≤ J) :
    (sourceU (K.subgroupOf J)).map J.subtype = sourceU K := by
  rw [sourceU_map_injective _ _ J.subtype_injective, map_subgroupOf_eq_of_le hK]

/-- A model on the restricted component gives a model on the original
component, retaining a surjective actor with exactly its intrinsic two-core kernel. -/
theorem source_model_of_subgroupOf (K J : Subgroup G) (hK : K ≤ J)
    (hm : ∃ m : ConjugationQuotientModel (K.subgroupOf J)
        (sourceU (K.subgroupOf J)) ρ,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 (K.subgroupOf J)) :
    ∃ m : ConjugationQuotientModel K (sourceU K) ρ,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K := by
  obtain ⟨m, ha, hk⟩ := hm
  have he : ∃ n : ConjugationQuotientModel ((K.subgroupOf J).map J.subtype)
      ((sourceU (K.subgroupOf J)).map J.subtype) ρ,
      Function.Surjective n.actor ∧ n.actor.ker = pCore 2 ((K.subgroupOf J).map J.subtype) :=
    ⟨m.mapInjective J.subtype J.subtype_injective,
      m.mapInjective_actor_surjective J.subtype J.subtype_injective ha,
      m.mapInjective_actor_kernel_pCore J.subtype J.subtype_injective hk⟩
  rwa [sourceU_subgroupOf_map K J hK, map_subgroupOf_eq_of_le hK] at he

/-- The literal join K∨T used by the original MS-pair transports its source
model to K; no identification of K with its action quotient is used. -/
theorem source_model_of_join (K T : Subgroup G)
    (hm : ∃ m : ConjugationQuotientModel (K.subgroupOf (K ⊔ T))
        (sourceU (K.subgroupOf (K ⊔ T))) ρ,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 (K.subgroupOf (K ⊔ T))) :
    ∃ m : ConjugationQuotientModel K (sourceU K) ρ,
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K :=
  source_model_of_subgroupOf K (K ⊔ T) le_sup_left hm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
