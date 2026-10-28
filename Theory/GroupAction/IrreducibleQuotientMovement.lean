module
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.ElementaryAbelian.Quotient

/-!
# Commutator movement through an irreducible quotient action

A faithful nontrivial irreducible binary action is spanned by its
linear displacements. When its module is the literal Q/(Q ∩ N), the
specified conjugation formula lifts each displacement into [Q,A].
Surjectivity of the original actor marking then gives Q = [Q,A](Q ∩ N).
The original actor need not surject onto A; it need only realize all
actors of the quotient representation. N need not lie in Q.

This bridge supplies reciprocal movement for the second-kernel section
in DGS85 (12.6), printed p.183. Its literal source application is
CommutingThreeProfile.SuzukiCenterFixed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G X J : Type*} [Group G] [Group X] [Group J]

/-- Lift movement of a literal quotient through an arbitrary original actor map. -/
theorem le_commutator_sup_of_irreducible_quotient
    (A Q N : Subgroup G) [(N.subgroupOf Q).Normal]
    [IsElementaryAbelian 2 (Q ⧸ N.subgroupOf Q)] [Nontrivial J]
    (hAQ : A ≤ normalizer (Q : Set G))
    (actor : X →* A) (π : X →* J) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) J (Additive (Q ⧸ N.subgroupOf Q)))
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hρ : ∀ a : X, ∀ x : Q,
      (ρ (π a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
        QuotientGroup.mk ⟨(actor a : G) * x * (actor a : G)⁻¹,
          (mem_normalizer_iff.mp (hAQ (actor a).property) x).mp x.property⟩) :
    Q ≤ ⁅Q,A⁆ ⊔ (Q ⊓ N) := by
  let q := QuotientGroup.mk' (N.subgroupOf Q)
  let D := (⁅Q,A⁆.subgroupOf Q).map q
  let W : Submodule (ZMod 2) (Additive (Q ⧸ N.subgroupOf Q)) :=
    AddSubgroup.toZModSubmodule 2 D.toAddSubgroup
  have hspan : Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,_,v,_,rfl⟩
    obtain ⟨a,rfl⟩ := hπ j
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) v.toMul
    have hv : Additive.ofMul (q x) = v := congrArg Additive.ofMul hx
    rw [←hv]
    change (ρ (π a) (Additive.ofMul (q x))).toMul / q x ∈ D
    have hr := hρ a x
    change (ρ (π a) (Additive.ofMul (q x))).toMul = q _ at hr
    rw [div_eq_mul_inv,hr]
    change q _ * (q x)⁻¹ ∈ D
    rw [←map_inv,←map_mul]
    apply mem_map_of_mem
    change ⁅(actor a : G),(x : G)⁆ ∈ ⁅Q,A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator (actor a).property x.property
  have hW : W = ⊤ := top_unique ((Representation.BinaryOffender.subspaceCommutator_top_eq_top_of_faithful_irreducible ρ hf hi).symm ▸ hspan)
  intro x hx
  have hm : q ⟨x,hx⟩ ∈ D := show Additive.ofMul (q ⟨x,hx⟩) ∈ W from hW.ge (Submodule.mem_top)
  obtain ⟨y,hy,he⟩ := hm
  have hk : x * (y : G)⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N.subgroupOf Q) (⟨x,hx⟩ * y⁻¹ : Q)).mp
    change q (⟨x,hx⟩ * y⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hh := (⁅Q,A⁆ ⊔ (Q ⊓ N)).mul_mem
    (mem_sup_right ⟨Q.mul_mem hx (Q.inv_mem y.property),hk⟩) (mem_sup_left hy)
  change x * (y : G)⁻¹ * (y : G) ∈ _ at hh
  simpa only [inv_mul_cancel_right] using hh

end Subgroup
