module
public import CFSG.Quasithin.ChapterD.Section03.SourceFitting
public import Theory.Representation.BinaryOffender.IrrPlusFitting
public import Theory.Representation.BinaryOffender.RestrictionImage
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The seed-stabilizer generalized Fitting assertion

For the local group X T, the action on the actual Irr⁺ seed has F*
precisely equal to its actor image. Restriction from the full faithful
orbit image preserves the actor's semisimple or odd-prime shape. The
seed-image theorem then proves the F* identity on the original seed.

This is the second assertion of D.3.4(5), alongside SourceFitting's
separate local-orbit assertion. Both original actor alternatives apply.
Source: Aschbacher–Smith, D.3.3–4, printed pp.193–194.
-/

public section
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
    {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

theorem SourceHypotheses.seed_fitting_structure
    (h : SourceHypotheses K ρ T X I) (hgen : X ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting (subspaceActionImage ρ I) = restrictedSubgroup ρ I X ∧
      (componentLayer (restrictedSubgroup ρ I X) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup ρ I X)) := by
  let := h.finiteModule
  let := h.normal
  let A := subspaceStabilizer ρ I
  let L := subspaceActionImage ρ I
  let f : A →* L := subspaceActionHom ρ I
  have hf : Function.Surjective f :=
    (stabilizerRepresentation ρ I).asGroupHom.rangeRestrict_surjective
  let : Finite L := Finite.of_surjective f hf
  let Xbar := restrictedSubgroup ρ I X
  let : Xbar.Normal := Normal.map inferInstance f hf
  have hXI : X ≤ A := h.seed.choose
  let q := restrictedActionSurjection ρ I X hXI
  have hq := restrictedActionSurjection_surjective ρ I X hXI
  have hshape : componentLayer Xbar = ⊤ ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p Xbar := by
    rcases h.cases.layer_or_prime_group with he | ⟨p, hp, ho, hP⟩
    · exact Or.inl (componentLayer_eq_top_of_surjective q hq he)
    · exact Or.inr ⟨p, hp, ho, hP.of_surjective q hq⟩
  exact ⟨seed_image_fitting_of_shape ρ X I h.seed hshape
    (isPGroup_quotient_of_sup_eq_top X T T.isPGroup' hgen), hshape⟩
end CFSG.Quasithin.ChapterD.Section03

namespace CFSG.Quasithin.ChapterD.Section03
universe u
variable {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
    {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

theorem InternalModuleHypotheses.seed_fitting_structure
    (h : InternalModuleHypotheses K ρ T X I) (hgen : X ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting (subspaceActionImage ρ I) = restrictedSubgroup ρ I X ∧
      (componentLayer (restrictedSubgroup ρ I X) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup ρ I X)) := by
  let := h.finiteModule
  let := h.normal
  let W := orbitSpan ρ ⊤ I
  obtain ⟨f, hf, _⟩ := exists_restricted_image_surjection ρ X I W
    h.seed.choose (le_top.trans (orbitSpan_invariant ρ ⊤ I)) (le_orbitSpan ρ ⊤ I)
  have hshape : componentLayer (restrictedSubgroup ρ I X) = ⊤ ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup ρ I X) := by
    rcases h.faithfulOrbit_source.cases.layer_or_prime_group with he | ⟨p, hp, ho, hP⟩
    · exact Or.inl (componentLayer_eq_top_of_surjective f hf he)
    · exact Or.inr ⟨p, hp, ho, hP.of_surjective f hf⟩
  exact ⟨seed_image_fitting_of_shape ρ X I h.seed hshape
    (isPGroup_quotient_of_sup_eq_top X T T.isPGroup' hgen), hshape⟩
end CFSG.Quasithin.ChapterD.Section03

namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
    {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

theorem SourceHypotheses.local_seed_fitting_structure
    (h : SourceHypotheses K ρ T X I) :
    let A := X ⊔ (T : Subgroup G)
    let σ := ρ.comp A.subtype
    generalizedFitting (subspaceActionImage σ I) = restrictedSubgroup σ I (X.subgroupOf A) ∧
      (componentLayer (restrictedSubgroup σ I (X.subgroupOf A)) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup σ I (X.subgroupOf A))) := by
  let := h.finiteModule
  let := h.normal
  let A := X ⊔ (T : Subgroup G)
  let σ := ρ.comp A.subtype
  let e := subgroupOfEquivOfLe (show X ≤ A from le_sup_left)
  have hi : IsIrrPlus σ (X.subgroupOf A) I := by
    apply h.seed.of_intertwining ρ σ e.symm.toMonoidHom e.symm.surjective
      LinearMap.id Function.injective_id
    · intro x v
      rfl
    · exact Submodule.map_id _
  let f := (restrictedActionSurjection σ I (X.subgroupOf A) hi.choose).comp e.symm.toMonoidHom
  have hf : Function.Surjective f :=
    (restrictedActionSurjection_surjective σ I (X.subgroupOf A) hi.choose).comp e.symm.surjective
  have hshape : componentLayer (restrictedSubgroup σ I (X.subgroupOf A)) = ⊤ ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup σ I (X.subgroupOf A)) := by
    rcases h.cases.layer_or_prime_group with he | ⟨p, hp, ho, hP⟩
    · exact Or.inl (componentLayer_eq_top_of_surjective f hf he)
    · exact Or.inr ⟨p, hp, ho, hP.of_surjective f hf⟩
  refine ⟨seed_image_fitting_of_shape σ (X.subgroupOf A) I hi hshape ?_, hshape⟩
  apply isPGroup_quotient_of_sup_eq_top _ ((T : Subgroup G).subgroupOf A) T.isPGroup'.comap_subtype
  change X.subgroupOf (X ⊔ (T : Subgroup G)) ⊔
    (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G)) = ⊤
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
end CFSG.Quasithin.ChapterD.Section03
