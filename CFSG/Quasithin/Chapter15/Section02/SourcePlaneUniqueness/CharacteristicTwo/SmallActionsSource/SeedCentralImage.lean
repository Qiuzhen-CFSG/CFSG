module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CubicSeeds
public import Theory.SpecificGroups.SymmetricThree.CubicSelection

/-!
# A central-image obstruction for the corrected source seed

A two-group kernel lies in the two-core of the seed's product with S.
If the seed became central in that image, its image in the original S₃
core quotient would be central as well. This is impossible because that
image is the nontrivial cubic two-residual of S₃.

Source application: the final extraspecial contradiction of
Aschbacher--Smith15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G D : Type*} [Group G] [Finite G] [Group D]
variable {M I S Y : Subgroup G}

private theorem symmetricThree_center : center (Equiv.Perm (Fin 3)) = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  have hf : ∀ z : Equiv.Perm (Fin 3), (∀ x, x*z=z*x) → z=1 := by decide +kernel
  intro z hz
  exact hf z (mem_center_iff.mp hz)

/-- A corrected seed cannot become central modulo a two-group kernel:
its original S₃ core quotient has a noncentral cubic residual. -/
theorem Seed.not_central_image (s : Seed M I S Y) (hS : IsPGroup 2 S)
    (f : (Y ⊔ S : Subgroup G) →* D) (hk : IsPGroup 2 f.ker)
    (hc : ∀ y : (Y ⊔ S : Subgroup G), (y : G) ∈ Y →
      ∀ x : (Y ⊔ S : Subgroup G), f x * f y = f y * f x) : False := by
  let L := Y ⊔ S
  let A := Y.subgroupOf L
  obtain ⟨e⟩ := s.quotient
  let q := QuotientGroup.mk' (pCore 2 L)
  let g := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcomm : ⁅A,(⊤ : Subgroup L)⁆ ≤ pCore 2 L := by
    apply le_trans ?_ (show f.ker ≤ pCore 2 L from le_sSup ⟨inferInstance,hk⟩)
    apply commutator_le.mpr
    intro y hy x _
    change f ⁅y,x⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc y hy x).symm
  have hgcore : (pCore 2 L).map g = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    change e (q x) = 1
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx,map_one]
  have hcentral : A.map g ≤ center (Equiv.Perm (Fin 3)) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    have hh := map_mono (f := g) hcomm
    rw [map_commutator,map_top_of_surjective g hg,hgcore] at hh
    exact bot_unique hh
  rw [symmetricThree_center] at hcentral
  have hRA : pResidual 2 L ≤ A := by
    intro x hx
    have hh := mem_map_of_mem L.subtype hx
    rw [s.join_residual hS] at hh
    exact hh
  have hzero : (pResidual 2 L).map g = ⊥ := bot_unique ((map_mono hRA).trans hcentral)
  rw [map_pResidual_of_surjective 2 g hg] at hzero
  have hcard := Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card
  rw [hzero,card_bot] at hcard
  contradiction
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
