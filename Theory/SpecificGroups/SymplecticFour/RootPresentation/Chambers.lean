module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Presentation

/-!
# Faithful positive chambers in the C₂ presentation

For every permutation in the specified Weyl subgroup, the chamber relations
construct a map from concrete U to its four-root subgroup in the presentation.
Matrix evaluation of this map is an actual matrix automorphism followed by
the U inclusion. This proves both that the chamber map is injective and that
matrix evaluation is faithful on every such chamber, including all subgroups
of these chambers. This is the local injectivity needed in the proof of the
opposite-root Weyl conjugation formulas; those formulas are not assumed here.

Source: Steinberg §6, Lemma 36 and the first step of Lemma 37, pp.69–70.
-/

@[expose] public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
open PositiveRelations
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl)
include hσ

/-- The concrete U maps onto the positive subgroup of the specified chamber. -/
def chamberMap : unipotent (F := F) →* SteinbergGroup F :=
  (generator_relations σ hσ).unipotentMap

theorem chamberMap_range : (chamberMap (F := F) σ hσ).range =
    positiveSubgroup (fun r t => generator (σ r) t) :=
  (generator_relations σ hσ).unipotentMap_range

/-- Evaluation agrees with the realized Weyl automorphism on the whole U. -/
theorem matrixMap_chamberMap (a : MulAut (Sp F))
    (ha : ∀ r t, a (rootElement r t) = rootElement (σ r) t) :
    matrixMap.comp (chamberMap σ hσ) = a.toMonoidHom.comp (unipotent (F := F)).subtype := by
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := CentralRootGeometry.element_surjective g
  change matrixMap ((generator_relations σ hσ).unipotentMap
    (CentralRootGeometry.element b u w v)) = a (CentralRootGeometry.element b u w v).val
  rw [PositiveRelations.unipotentMap_element]
  simp only [product, map_mul, matrixMap_generator, CentralRootGeometry.element, ha]

/-- Every chamber has the same faithful four-parameter matrix coordinates. -/
theorem chamberMap_injective : Function.Injective (chamberMap (F := F) σ hσ) := by
  obtain ⟨a,ha⟩ := exists_weyl_automorphism (F := F) σ hσ
  intro u v he
  apply Subtype.ext
  apply a.injective
  have h := congrArg matrixMap he
  have hf := matrixMap_chamberMap σ hσ a ha
  exact (DFunLike.congr_fun hf u).symm.trans (h.trans (DFunLike.congr_fun hf v))

/-- Matrix evaluation is faithful on each positive chamber, not just the
original positive order. No global presentation faithfulness is assumed. -/
theorem matrixMap_injective_on_chamber : Set.InjOn (matrixMap (F := F))
    (positiveSubgroup (fun r t => generator (F := F) (σ r) t) : Set (SteinbergGroup F)) := by
  intro u hu v hv he
  rw [← chamberMap_range σ hσ] at hu hv
  obtain ⟨u,rfl⟩ := hu
  obtain ⟨v,rfl⟩ := hv
  obtain ⟨a,ha⟩ := exists_weyl_automorphism (F := F) σ hσ
  have hf := matrixMap_chamberMap σ hσ a ha
  have hav : a (u : Sp F) = a (v : Sp F) :=
    (DFunLike.congr_fun hf u).symm.trans (he.trans (DFunLike.congr_fun hf v))
  exact congrArg (chamberMap σ hσ) (Subtype.ext (a.injective hav))

/-- Any subgroup of a positive chamber inherits faithful matrix evaluation. -/
theorem matrixMap_injective_on_subgroup (H : Subgroup (SteinbergGroup F))
    (hH : H ≤ positiveSubgroup (fun r t => generator (σ r) t)) :
    Function.Injective (matrixMap.comp H.subtype) := by
  intro u v he
  exact Subtype.ext (matrixMap_injective_on_chamber σ hσ
    (hH u.property) (hH v.property) he)
end Theory.SpecificGroups.SymplecticFour.RootPresentation
