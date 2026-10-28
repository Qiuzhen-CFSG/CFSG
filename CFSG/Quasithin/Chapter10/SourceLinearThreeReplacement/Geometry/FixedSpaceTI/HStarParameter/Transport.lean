module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# Passing a faithful marked action to the literal induced automizer

The actual conjugation map onto Aut_H(I) is surjective. Faithful linear
coordinates identify its kernel with that of the marked actor map. Descending
the latter map gives an injection of the actual automizer and transports the
fixed-space-family parameter. The same coordinates detect every element of H
which moves the marked module; there is no passage to a section quotient.

Source application: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open ChapterE
variable {G X V : Type*} [Group G] [Group X]
  [AddCommGroup V] [Module (ZMod 2) V]
  (I H : Subgroup G) (hHI : H ≤ normalizer (I : Set G))

/-- Conjugation by the original H, with image exactly Aut_H(I). -/
def actionMap : H →* inducedAutomizer I H where
  toFun h := ⟨I.normalizerMonoidHom.rangeRestrict ⟨h,hHI h.property⟩,
    ⟨⟨h,hHI h.property⟩,h.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one I.normalizerMonoidHom.rangeRestrict
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul I.normalizerMonoidHom.rangeRestrict ⟨a,hHI a.property⟩ ⟨b,hHI b.property⟩

theorem actionMap_surjective : Function.Surjective (actionMap I H hHI) := by
  rintro ⟨a,n,hn,rfl⟩
  exact ⟨⟨n,hn⟩,rfl⟩

theorem actionMap_eq_one_iff (h : H) :
    actionMap I H hHI h = 1 ↔ (h : G) ∈ centralizer (I : Set G) := by
  exact localNormalizerAction_eq_one_iff I H ⟨h,h.property,hHI h.property⟩

variable [IsElementaryAbelian 2 I]

/-- Faithful full-module coordinates transfer a bound to the exact local action. -/
theorem moduleA_le_of_faithful_coordinates
    (σ : Representation (ZMod 2) X V) (hσ : Function.Injective σ)
    (q : H →* X) (E : Additive I ≃ₗ[ZMod 2] V)
    (hact : ∀ h v,
      E (((automizerRepresentation I).comp (inducedAutomizer I H).subtype)
        (actionMap I H hHI h) v) = σ (q h) (E v)) :
    moduleA ((automizerRepresentation I).comp (inducedAutomizer I H).subtype) ≤ moduleA σ := by
  let α := actionMap I H hHI
  have hα := actionMap_surjective I H hHI
  let ρ := (automizerRepresentation I).comp (inducedAutomizer I H).subtype
  have hk : α.ker ≤ q.ker := by
    intro h hh
    apply (injective_iff_map_eq_one σ).mp hσ
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    have he := hact h w
    change E (ρ (α h) w) = σ (q h) (E w) at he
    rw [show α h = 1 from hh,map_one] at he
    exact he.symm
  let f : inducedAutomizer I H →* X := α.liftOfSurjective hα ⟨q,hk⟩
  have hfα (h : H) : f (α h) = q h := α.liftOfRightInverse_comp_apply _ _ _ h
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    obtain ⟨h,rfl⟩ := hα a
    have hq : q h = 1 := (hfα h).symm.trans ha
    apply Subtype.ext
    apply (automizerRepresentation_injective I)
    apply LinearMap.ext
    intro v
    apply E.injective
    have he := hact h v
    rw [hq,map_one] at he
    exact he
  apply moduleA_le_of_equivariant_injective ρ σ f hf E
  intro a v
  obtain ⟨h,rfl⟩ := hα a
  rw [hfα]
  exact hact h v

/-- The same marked coordinates identify the pointwise kernel in H. -/
theorem centralizes_iff_marked_eq_one
    (σ : Representation (ZMod 2) X V) (hσ : Function.Injective σ)
    (q : H →* X) (E : Additive I ≃ₗ[ZMod 2] V)
    (hact : ∀ h v,
      E (((automizerRepresentation I).comp (inducedAutomizer I H).subtype)
        (actionMap I H hHI h) v) = σ (q h) (E v)) (h : H) :
    (h : G) ∈ centralizer (I : Set G) ↔ q h = 1 := by
  rw [← actionMap_eq_one_iff I H hHI]
  constructor
  · intro hh
    apply (injective_iff_map_eq_one σ).mp hσ
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    have he := hact h w
    rw [hh,map_one] at he
    exact he.symm
  · intro hh
    apply Subtype.ext
    apply (automizerRepresentation_injective I)
    apply LinearMap.ext
    intro v
    apply E.injective
    have he := hact h v
    rw [hh,map_one] at he
    exact he

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
