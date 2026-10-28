module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Centralizer indices on literal conjugation sections

The composite of section coordinates with the quotient by the actor's
fixed space kills the original centralizer. The first isomorphism theorem
therefore bounds the fixed-space quotient order by the original relative
centralizer index. Separately, the actual actor image has order equal to
the relative index of the kernel of its specified homomorphism.

These two comparisons retain both the section denominator and the actor
kernel in the reciprocal estimates of DGS, *Groups and Graphs* (1985),7.1,
printed p.126.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- Fixed points in a literal section can only decrease the original
centralizer index, even when the section has a nontrivial kernel. -/
theorem fixed_quotient_card_le_centralizer_index
    {H U Z : Subgroup G} [Finite U]
    (σ : Representation (ZMod 2) D W) (π : H →* D)
    (d : BinaryConjugationSection H U Z (σ.comp π)) (A : Subgroup G) :
    Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf H).map π)) ≤
      (centralizer (A : Set G)).relIndex U := by
  let F := fixedSpace σ ((A.subgroupOf H).map π)
  let f : U →* Multiplicative (W ⧸ F) :=
    F.mkQ.toAddMonoidHom.toMultiplicative.comp d.coordinates
  have hf : Function.Surjective f := F.mkQ_surjective.comp d.onto
  have hker : (centralizer (A : Set G)).subgroupOf U ≤ f.ker := by
    intro u hu
    change F.mkQ (d.coordinates u).toAdd = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro a
    obtain ⟨h, hh, he⟩ := a.property
    change σ (a : D) (d.coordinates u).toAdd = _
    rw [← he]
    have hc : (⟨(h : G) * (u : G) * (h : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized h.property) u).mp u.property⟩ : U) = u := by
      apply Subtype.ext
      change (h : G) * (u : G) * (h : G)⁻¹ = (u : G)
      have hcomm : (h : G) * (u : G) = (u : G) * (h : G) := hu h hh
      rw [hcomm, mul_inv_cancel_right]
    have hd := d.equivariant h u
    rw [hc] at hd
    exact hd.symm
  have hcard : f.ker.index = Nat.card (W ⧸ F) := by
    rw [index_eq_card, Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    rfl
  rw [← hcard]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
    (index_dvd_of_le hker)

/-- The order of the actual actor image is the index of its actual kernel. -/
theorem actor_image_card_eq_relIndex
    (H K A : Subgroup G) (π : H →* D)
    (hK : π.ker = K.subgroupOf H) (hAH : A ≤ H) :
    Nat.card ((A.subgroupOf H).map π) = K.relIndex A := by
  rw [← relIndex_ker, hK]
  change (K.comap H.subtype).relIndex (A.subgroupOf H) = _
  rw [relIndex_comap, map_subgroupOf_eq_of_le hAH]

end Representation.BinaryConjugationSection
