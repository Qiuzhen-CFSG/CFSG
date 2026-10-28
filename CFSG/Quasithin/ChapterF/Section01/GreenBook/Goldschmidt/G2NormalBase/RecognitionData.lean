module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.G2NormalBase.Overlap

/-!
# Normal-product data for the binary G₂ extension

The marked residual equivalence gives both normal endpoint maps. The exact
full-Borel action supplies their conjugation compatibility and agreement
on the residual overlap. The model intersections identify the inverse
image needed for injective gluing. Source: Goldschmidt (1980), §3.7.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SourceAssembly.Goldschmidt ExceptionalModels.G2
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

def ambientOverlapHom (e : Iso (baseAmalgam F) simpleAmalgam) :
    ↥(F false ⊓ F true) →* Full := fullB.subtype.comp (overlapHom e)

theorem ambientOverlapHom_injective (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) : Function.Injective (ambientOverlapHom e) :=
  fullB.subtype_injective.comp (overlapHom_injective h e)

def leftCoreEquiv (e : Iso (baseAmalgam F) simpleAmalgam) :
    residualFamily F false ≃* Model.innerP0 :=
  e.left.trans (derivedL₁.equivMapOfInjective Derived.subtype Derived.subtype_injective)

def rightCoreEquiv (e : Iso (baseAmalgam F) simpleAmalgam) :
    residualFamily F true ≃* Model.innerP1 :=
  e.right.trans (derivedL₂.equivMapOfInjective Derived.subtype Derived.subtype_injective)

theorem innerB_mem_iff (b : fullB) :
    (b : Full) ∈ Model.innerB ↔ b ∈ Model.innerBEmbedding.range := by
  rw [← Model.innerBEmbedding_range_image]
  constructor
  · rintro ⟨x, hx, he⟩
    have he' : x = b := Subtype.ext he
    exact he' ▸ hx
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem ambientOverlapHom_mem_inner_iff (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) (R : Subgroup Full)
    (hR : R ⊓ fullB = Model.innerB) (t : ↥(F false ⊓ F true)) :
    ambientOverlapHom e t ∈ R ↔ (t : G) ∈ pResidual 2 G := by
  have hb : ambientOverlapHom e t ∈ fullB := (overlapHom e t).property
  have hi : ambientOverlapHom e t ∈ R ↔ ambientOverlapHom e t ∈ Model.innerB := by
    rw [← hR]
    exact ⟨fun ha => ⟨ha, hb⟩, And.left⟩
  rw [hi]
  exact (innerB_mem_iff (overlapHom e t)).trans (overlapHom_mem_inner_iff h e t)

theorem ambientOverlapHom_base_left (e : Iso (baseAmalgam F) simpleAmalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    ambientOverlapHom e (baseOverlapEmbedding F s) =
      (leftCoreEquiv e ((baseAmalgam F).left s) : Full) := by
  change (overlapHom e (baseOverlapEmbedding F s) : Full) =
    (e.left ((baseAmalgam F).left s)).val.val
  rw [overlapHom_base, Model.innerBEmbedding_apply, e.left_commutes]
  rfl

theorem ambientOverlapHom_base_right (e : Iso (baseAmalgam F) simpleAmalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    ambientOverlapHom e (baseOverlapEmbedding F s) =
      (rightCoreEquiv e ((baseAmalgam F).right s) : Full) := by
  change (overlapHom e (baseOverlapEmbedding F s) : Full) =
    (e.right ((baseAmalgam F).right s)).val.val
  rw [overlapHom_base, Model.innerBEmbedding_apply, e.right_commutes]
  rfl

theorem leftCoreEquiv_conj (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F false) :
    (leftCoreEquiv e ((residualAmalgamAction F t).left n) : Full) =
      ambientOverlapHom e t * leftCoreEquiv e n * (ambientOverlapHom e t)⁻¹ :=
  (overlapHom_left e t n).symm

theorem rightCoreEquiv_conj (e : Iso (baseAmalgam F) simpleAmalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F true) :
    (rightCoreEquiv e ((residualAmalgamAction F t).right n) : Full) =
      ambientOverlapHom e t * rightCoreEquiv e n * (ambientOverlapHom e t)⁻¹ :=
  (overlapHom_right e t n).symm

theorem ambient_overlap_range_cases (e : Iso (baseAmalgam F) simpleAmalgam) :
    (ambientOverlapHom e).range = Model.innerB ∨ (ambientOverlapHom e).range = fullB := by
  have hr : (ambientOverlapHom e).range = (overlapHom e).range.map fullB.subtype :=
    MonoidHom.range_comp _ _
  rcases overlap_range_cases e with he | he
  · exact Or.inl (hr.trans (he ▸ Model.innerBEmbedding_range_image))
  · right
    rw [hr, he, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
