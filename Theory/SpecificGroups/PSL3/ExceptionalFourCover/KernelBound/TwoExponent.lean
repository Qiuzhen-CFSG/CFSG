module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Basic
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoExponent.Commutator
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# Exponent four for the two-primary universal kernel of PSL₃(4)

The faithful projective image of UT₃(F₄) has order 64, hence is a Sylow
two-subgroup of PSL₃(4). Lift it to a Sylow subgroup S of the actual
canonical universal cover. The literal two-primary kernel is central,
so it lies in S, and perfectness and central Sylow transfer place it in S′.

The restricted projection S → UT₃(F₄) has central kernel. Coordinates
show that UT₃(F₄) has class at most two and every element is a product of
two involutions. Consequently S has class at most three and every element
is a product of two elements with central squares. The commutator lemma
then gives exponent dividing four in S′ and in the two-primary kernel.

This proves the two-primary exponent bound needed for Aschbacher--Smith
I.1.3(6), printed p.407 (PDF p.418), and GLS3 §6.1. The generator bound
and the full multiplier identification are separate results. No multiplier
table or kernel realization is used here.
-/

open Subgroup
open scoped commutatorElement
open Matrix.PSL3Four.SylowModel
open Matrix.PSL3Four.SylowModel.MatrixRealization

namespace Matrix.PSL3.ExceptionalFourCover
noncomputable section

private theorem unipotent_class_two :
    _root_.commutator U ≤ center U := by
  apply commutator_le.mpr
  intro a _ b _
  apply (mem_center_U _).mpr
  change ((a * b * a⁻¹ * b⁻¹).x = 0) ∧ ((a * b * a⁻¹ * b⁻¹).y = 0)
  constructor <;> simp only [mul_x, mul_y]
  · change a.x + b.x + -a.x + -b.x = 0
    abel
  · change a.y + b.y + -a.y + -b.y = 0
    abel

private theorem unipotent_two_involution_factors (x : U) :
    ∃ a b : U, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ x = a * b := by
  refine ⟨⟨x.x, 0, x.c⟩, ⟨0, x.y, -x.x * x.y⟩, ?_, ?_, ?_⟩
  · apply U.ext <;> simp [pow_two, CharTwo.add_self_eq_zero]
  · apply U.ext <;> simp [pow_two, CharTwo.add_self_eq_zero]
  · apply U.ext <;> simp

variable {G : Type*} [Group G]
private theorem central_extension_class_three (f : G →* U)
    (hf : f.ker ≤ center G) :
    ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G := by
  apply le_trans _ hf
  apply commutator_le.mpr
  intro a ha b _
  change f ⁅a, b⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  apply (mem_center_iff.mp _ (f b)).symm
  apply unipotent_class_two
  have hmap : (_root_.commutator G).map f ≤ _root_.commutator U := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  exact hmap ⟨a, ha, rfl⟩

private theorem central_extension_square_factors (f : G →* U)
    (hfs : Function.Surjective f) (hf : f.ker ≤ center G) (x : G) :
    ∃ a b : G, a ^ 2 ∈ center G ∧ b ^ 2 ∈ center G ∧ x = a * b := by
  obtain ⟨u, v, hu, hv, he⟩ := unipotent_two_involution_factors (f x)
  obtain ⟨a, ha⟩ := hfs u
  refine ⟨a, a⁻¹ * x, ?_, ?_, by simp⟩
  · apply hf
    change f (a ^ 2) = 1
    rwa [map_pow, ha]
  · apply hf
    change f ((a⁻¹ * x) ^ 2) = 1
    rw [map_pow, map_mul, map_inv, ha, he, inv_mul_cancel_left, hv]

private def unipotentSylow : Sylow 2 PSL3Four.PSL :=
  Sylow.ofCard projective.range (by
    rw [← Nat.card_congr (MonoidHom.ofInjective projective_injective).toEquiv,
      card_U, PSL3Four.card_PSL]
    decide +kernel)

/-- Every element of the two-primary part of the actual canonical universal
kernel of PSL₃(4) has fourth power one. -/
public theorem two_sylow_pow_four
    (P : Sylow 2 cover.toMonoidHom.ker) (x : P) : x ^ 4= 1 := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective cover_surjective 2 unipotentSylow
  have hmap : (S : Subgroup CoverGroup).map cover.toMonoidHom = projective.range :=
    congrArg Sylow.toSubgroup hS
  let e : U ≃* projective.range := MonoidHom.ofInjective projective_injective
  let r : S →* projective.range :=
    (cover.toMonoidHom.comp (S : Subgroup CoverGroup).subtype).codRestrict
      projective.range (fun s => hmap ▸ ⟨s, s.property, rfl⟩)
  let f : S →* U := e.symm.toMonoidHom.comp r
  have hf : Function.Surjective f := by
    intro u
    have hm : projective u ∈ (S : Subgroup CoverGroup).map cover.toMonoidHom :=
      hmap.symm ▸ ⟨u, rfl⟩
    obtain ⟨s, hs, hsu⟩ := hm
    refine ⟨⟨s, hs⟩, ?_⟩
    change e.symm (r ⟨s, hs⟩) = u
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext hsu
  have hc : f.ker ≤ center S := by
    intro s hs
    have hfs : f s = 1 := hs
    have hrs : r s = 1 := by
      apply e.symm.injective
      exact hfs.trans (map_one e.symm).symm
    have hks : (s : CoverGroup) ∈ cover.toMonoidHom.ker :=
      congrArg Subtype.val hrs
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (mem_center_iff.mp (cover.ker_le_center hks) t)
  let N : Subgroup CoverGroup := (P : Subgroup cover.toMonoidHom.ker).map
    cover.toMonoidHom.ker.subtype
  have hNc : N ≤ center CoverGroup := by
    rintro a ⟨b, _, rfl⟩
    exact cover.ker_le_center b.property
  let : N.Normal := {
    conj_mem := fun a ha b => by
      rw [mem_center_iff.mp (hNc ha) b, mul_inv_cancel_right]
      exact ha }
  have hNS : N ≤ (S : Subgroup CoverGroup) :=
    (P.isPGroup'.map cover.toMonoidHom.ker.subtype).le_sylow_of_normal S
  have hxS : ((x : cover.toMonoidHom.ker) : CoverGroup) ∈ (S : Subgroup CoverGroup) :=
    hNS ⟨(x : cover.toMonoidHom.ker), x.property, rfl⟩
  have hxD : ((x : cover.toMonoidHom.ker) : CoverGroup) ∈
      ⁅(S : Subgroup CoverGroup), (S : Subgroup CoverGroup)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator S
      ⟨⟨cover.ker_le_center (x : cover.toMonoidHom.ker).property,
        Group.IsPerfect.mem_commutator⟩, hxS⟩
  rw [← map_subtype_commutator] at hxD
  obtain ⟨y, hy, he⟩ := hxD
  have hy4 := derived_pow_four_of_central_square_factors
    (central_extension_class_three f hc) (central_extension_square_factors f hf hc) y hy
  apply Subtype.ext
  apply Subtype.ext
  change ((x : cover.toMonoidHom.ker) : CoverGroup) ^ 4 = 1
  rw [← he]
  exact congrArg (fun t : S => (t : CoverGroup)) hy4

end
end Matrix.PSL3.ExceptionalFourCover
