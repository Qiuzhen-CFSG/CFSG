module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Involution ranks in the orthogonal binary A5 module

The module is the even-weight core of the five-point binary permutation
module. It has dimension four and is the orthogonal A5 module, as opposed to
the restriction of scalars of the natural SL2(4) module. We count displacement
images in the actual sixteen-element space. The finite checks are evaluated
by the Lean kernel. A four-element image has binary dimension two.

Faithfulness is checked on the same coordinates. For two copies, an involution
commuting with the swapping operator has equal block actions. Its displacement
rank is therefore zero or four, never two. The commutation condition is
necessary: an involution acting in just one factor has rank two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3.1,
G.11.2(12) (printed p.364), and the proof of 6.2.19 (printed p.691).
-/

@[expose] public section

open scoped BigOperators
namespace Representation.RankTwo.Imprimitive.OrthogonalA5
private abbrev F := Fin 5 → ZMod 2

private def imageSet (p : Equiv.Perm (Fin 5)) : Finset F :=
  (Finset.univ.filter (fun v : F => ∑ i, v i = 0)).image
    (fun v i => v (p.symm i) - v i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private lemma card_image : ∀ p : Equiv.Perm (Fin 5),
    p.sign = 1 → p * p = 1 → p ≠ 1 → (imageSet p).card = 4 := by
  decide +kernel
private noncomputable def coreImageEquiv (p : Equiv.Perm (Fin 5)) :
    LinearMap.range (BinaryPermutation.coreRepresentation (Fin 5) p - 1) ≃
      ↥(imageSet p) := by
  let f : LinearMap.range (BinaryPermutation.coreRepresentation (Fin 5) p - 1) →
      ↥(imageSet p) := fun z => ⟨z.val.val, by
    obtain ⟨v, hv⟩ := z.property
    apply Finset.mem_image.mpr
    refine ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.property⟩, ?_⟩
    exact congrArg Subtype.val hv⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : ↥(imageSet p) => u.val) h
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    let z : BinaryPermutation.core (Fin 5) := ⟨v, (Finset.mem_filter.mp hv).2⟩
    refine ⟨⟨(BinaryPermutation.coreRepresentation (Fin 5) p - 1) z, ⟨z, rfl⟩⟩, ?_⟩
    exact Subtype.ext hvw

private lemma rank_core (p : Equiv.Perm (Fin 5))
    (hp : p.sign = 1) (h2 : p * p = 1) (hne : p ≠ 1) :
    Module.finrank (ZMod 2)
      (LinearMap.range (BinaryPermutation.coreRepresentation (Fin 5) p - 1)) = 2 := by
  have hc : Nat.card (LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) p - 1)) = 4 := by
    rw [Nat.card_congr (coreImageEquiv p), Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_image p hp h2 hne
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have he : 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (BinaryPermutation.coreRepresentation (Fin 5) p - 1)) = 2 ^ 2 := hc
  exact (Nat.pow_right_injective (by decide : 1 < 2)) he
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private lemma detects_permutation : ∀ p : Equiv.Perm (Fin 5),
    (∀ v : F, (∑ i, v i) = 0 → ∀ i, v (p.symm i) = v i) → p = 1 := by
  decide +kernel

private lemma eq_one_of_core (p : Equiv.Perm (Fin 5))
    (hp : BinaryPermutation.coreRepresentation (Fin 5) p = 1) : p = 1 := by
  apply detects_permutation p
  intro v hv i
  exact congrArg (fun f : Module.End (ZMod 2) (BinaryPermutation.core (Fin 5)) =>
    (f ⟨v, hv⟩).val i) hp
abbrev Space := BinaryPermutation.core (Fin 5)
abbrev Alternating := alternatingGroup (Fin 5)

def representation : Representation (ZMod 2) Alternating Space :=
  (BinaryPermutation.coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype

lemma finrank_space : Module.finrank (ZMod 2) Space = 4 := by
  simpa using BinaryPermutation.finrank_core (Fin 5)

lemma representation_injective : Function.Injective representation := by
  intro p q hpq
  have hh : representation (p * q⁻¹) = 1 := by
    rw [map_mul, hpq, ← map_mul, mul_inv_cancel, map_one]
  have he : p * q⁻¹ = 1 := Subtype.ext (eq_one_of_core (p * q⁻¹).val hh)
  exact mul_inv_eq_one.mp he

lemma finrank_displacement (p : Alternating) (hp : p * p = 1) (hne : p ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation p - 1)) = 2 := by
  apply rank_core p.val ((Equiv.Perm.mem_alternatingGroup).mp p.property)
  · exact congrArg Subtype.val hp
  · intro h
    exact hne (Subtype.ext h)

open Representation.RankTwo.Imprimitive in
lemma finrank_commuting_block (p : Alternating) (b : Module.End (ZMod 2) Space)
    (hc : Commute ((representation p).prodMap b) (swap (LinearEquiv.refl (ZMod 2) Space)))
    (h2 : ((representation p).prodMap b) * ((representation p).prodMap b) = 1) :
    Module.finrank (ZMod 2) (LinearMap.range ((representation p).prodMap b - 1)) = 0 ∨
    Module.finrank (ZMod 2) (LinearMap.range ((representation p).prodMap b - 1)) = 4 := by
  have hp2 : representation p * representation p = 1 := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) (Space × Space) => (f (v,0)).1) h2
  have hp : p * p = 1 := representation_injective (by simpa only [map_mul, map_one] using hp2)
  rw [Representation.RankTwo.Imprimitive.finrank_commuting_block
    (LinearEquiv.refl (ZMod 2) Space) (representation p) b hc]
  by_cases he : p = 1
  · left
    simp [he]
  · right
    rw [finrank_displacement p hp he]

end Representation.RankTwo.Imprimitive.OrthogonalA5
