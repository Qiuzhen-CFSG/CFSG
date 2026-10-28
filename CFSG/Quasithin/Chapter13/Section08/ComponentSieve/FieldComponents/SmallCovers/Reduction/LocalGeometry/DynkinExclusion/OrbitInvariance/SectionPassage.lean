module

public import Theory.Representation.CubicComponentFaithfulness
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.HexacodeAction.Cover
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections

/-!
# The literal cubic section and its faithful action image

The cubic polynomial kills component-fixed vectors. Consequently an Irr⁺
member is already irreducible before quotienting by those vectors. For a
faithful action we lift an actual elementary quadratic subgroup from the
action image, preserving its rank and fixed codimension. This is the ratio
transport needed after F.9.18(3), not an application of B.4.5 to a reducible
module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(3),
printed pp.325–326, and the cubic-cover branch of 13.8.21(2), printed p.956.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

theorem fixedSpace_eq_bot (L : Subgroup D) (z : D) (hz : z ∈ L)
    (hp : CubicPolynomial ρ z) : fixedSpace ρ L = ⊥ := by
  apply bot_unique
  intro v hv
  exact hp.fixed_eq_zero (hv ⟨z, hz⟩)

theorem irreducible_of_cubic (L : Subgroup D) (z : D) (hz : z ∈ L)
    (hp : CubicPolynomial ρ z) (I : Submodule (ZMod 2) V)
    (hI : IsIrrPlus ρ L I) :
    IsIrreducible (invariantSubspace ρ L I hI.choose).toRepresentation := by
  let S := invariantSubspace ρ L I hI.choose
  let C := centralSubspace ρ L I hI.choose
  let : IsIrreducible C.quotientRepresentation := hI.choose_spec.2
  have hc : C = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    change (fixedSpace ρ L).comap I.subtype = ⊥
    rw [fixedSpace_eq_bot ρ L z hz hp, Submodule.comap_bot, Submodule.ker_subtype]
  let : Nontrivial (invariantSubspace ρ L I hI.choose).toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr (hI.ne_bot ρ)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun W => ?_⟩
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient C W with h | h
  · exact Or.inl (le_bot_iff.mp (hc ▸ h))
  · apply Or.inr
    apply Subrepresentation.toSubmodule_injective
    change W.toSubmodule = ⊤
    simpa only [hc, show (⊥ : Subrepresentation S.toRepresentation).toSubmodule = ⊥ from rfl, bot_sup_eq] using h

theorem ratio_of_image [Finite D] (hf : Function.Injective ρ)
    (hq : quadraticRatio (imageRepresentation ρ) ≤ 2) : quadraticRatio ρ ≤ 2 := by
  have hi : Function.Injective (actionHom ρ) := by
    intro x y h
    exact hf (congrArg (imageRepresentation ρ) h)
  let e : D ≃* actionImage ρ := MulEquiv.ofBijective (actionHom ρ)
    ⟨hi, ρ.asGroupHom.rangeRestrict_surjective⟩
  obtain ⟨A, hA, hquad, hbound⟩ := (quadraticRatio_le_two_iff _).mp hq
  let B := A.map e.symm.toMonoidHom
  have hb : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro h
    apply hA.1
    apply bot_unique
    intro a ha
    have hm : e.symm a ∈ B := mem_map_of_mem _ ha
    rw [h, mem_bot] at hm
    exact e.symm.injective (hm.trans (map_one e.symm).symm)
  have hmap : actionSubgroup ρ B = A := by
    ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      change e (e.symm c) ∈ A
      rw [e.apply_symm_apply]
      exact hc
    · intro ha
      exact ⟨e.symm a, mem_map_of_mem _ ha, e.apply_symm_apply a⟩
  have hr : rank B = rank A := by
    exact congrArg (Nat.log 2) (Nat.card_congr (e.symm.subgroupMap A).toEquiv).symm
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨B, hb, ?_, ?_⟩
  · intro a ha b hb v
    exact hquad (actionHom ρ a) (hmap ▸ mem_map_of_mem _ ha)
      (actionHom ρ b) (hmap ▸ mem_map_of_mem _ hb) v
  · rw [← fixedCodim_actionSubgroup ρ B, hmap, hr]
    exact hbound
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
