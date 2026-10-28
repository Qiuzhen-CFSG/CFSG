module
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# Faithful images of reduced binary sections

A quotient of the original actor with kernel Z identifies the full action
kernel on U/Z with the preimage of the centralizer of the U-image. If that
image is two-reduced, the faithful representation image has trivial two-core.
The proof uses both literal quotient maps and the first isomorphism theorem;
it does not assert that the original actor quotient acts faithfully.

Source application: Aschbacher--Smith G.2.2 and 8.3.12, printed pp.332,726.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G J W : Type*} [Group G] [Group J]
  {H U Z : Subgroup G} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (c : BinaryConjugationSection H U Z ρ)
  (f : H →* J) (hk : f.ker = Z.subgroupOf H)

include c hk in
/-- The full kernel is the literal centralizer preimage in the point quotient. -/
theorem actionImage_kernel_eq_centralizer_comap :
    (actionHom ρ).ker = (centralizer (((U.subgroupOf H).map f) : Set J)).comap f := by
  ext a
  have hker : a ∈ (actionHom ρ).ker ↔ a ∈ ρ.ker := by
    change actionHom ρ a = 1 ↔ ρ a = 1
    rw [actionHom_eq_one_iff]
    exact ⟨fun h => LinearMap.ext h, fun h w => LinearMap.congr_fun h w⟩
  rw [hker,c.action_mem_ker_iff]
  constructor
  · intro ha y hy
    obtain ⟨u,hu,rfl⟩ := hy
    have hm : ⁅a,u⁆ ∈ f.ker := by
      rw [hk]
      exact ha u hu
    have he : ⁅f a,f u⁆ = 1 := by
      rw [←map_commutatorElement]
      exact hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · intro ha u hu
    let uH : H := ⟨u,c.section_le hu⟩
    have he : f ⁅a,uH⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (ha (f uH) (mem_map_of_mem f hu)).symm
    have hm : ⁅a,uH⁆ ∈ f.ker := he
    rw [hk] at hm
    exact hm

include c hk in
/-- Reducedness of the actual section gives a trivial two-core in its faithful image. -/
theorem actionImage_twoCore_eq_bot_of_reduced_image
    (hf : Function.Surjective f)
    (hr : IsPReduced 2 ((U.subgroupOf H).map f)) :
    pCore 2 (actionImage ρ) = ⊥ := by
  let R := (U.subgroupOf H).map f
  let := hr.normal
  let C := centralizer (R : Set J)
  let g := (QuotientGroup.mk' C).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective C).comp hf
  have he : (actionHom ρ).ker = g.ker := by
    change (actionHom ρ).ker = ((QuotientGroup.mk' C).comp f).ker
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact c.actionImage_kernel_eq_centralizer_comap f hk
  let e : actionImage ρ ≃* (J ⧸ C) :=
    (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq he).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg))
  rw [←pCore_map_iso 2 e.symm,hr.quotient_pCore_eq_bot,Subgroup.map_bot]
end Representation.BinaryConjugationSection
