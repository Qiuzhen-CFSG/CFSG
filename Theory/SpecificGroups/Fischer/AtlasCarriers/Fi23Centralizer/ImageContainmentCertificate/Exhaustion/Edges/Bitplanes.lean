module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.Certificate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork

/-!
# Bit-mask equality certificates for Fi23 edges

A bit action pulls back subsets along an actual permutation. Its action on
fifteen separating coordinate masks determines that permutation. The already
proved bit-network semantics can therefore check a whole permutation equality
using large-integer shifts and Boolean operations, rather than evaluating the
same word separately at all 31671 coordinates. Network routes and the masks'
coordinate meaning remain explicit certificate obligations.

The consumer below concludes membership of the literal exhaustion edge in
the unchanged eight-generator group. Source: ATLAS F23G1-p31671B0 and GLS3
Table 5.3u; the bit-network proof is reused from the Fi22 graph certificate.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
open Fi22.KernelCertificate

/-- Pullback of bit masks along a fixed, genuine permutation. -/
structure BitAction (p : Equiv.Perm (Fin 31671)) where
  transform : Nat → Nat
  sound : ∀ (v : Nat) (x : Fin 31671),
    (transform v).testBit x.val = v.testBit (p x).val

/-- A checked network route supplies the semantics for every input bit mask. -/
def BitAction.ofNetwork (p : Equiv.Perm (Fin 31671)) (ss : List BitNetwork.Stage)
    (h : ∀ x : Fin 31671, BitNetwork.route ss x.val = some (p x).val) : BitAction p :=
  ⟨BitNetwork.apply ss, fun v x => BitNetwork.sound ss x.val (p x).val v (h x)⟩

def BitAction.one : BitAction (1 : Equiv.Perm (Fin 31671)) := ⟨id, fun _ _ => rfl⟩

/-- Pullback reverses the order of composition. -/
def BitAction.mul {p q : Equiv.Perm (Fin 31671)} (a : BitAction p) (b : BitAction q) :
    BitAction (p * q) :=
  ⟨fun v => b.transform (a.transform v), fun v x => by
    rw [b.sound, a.sound]
    rfl⟩

/-- Fifteen masks encode all the bits of an original coordinate. -/
def SeparatingMasks (planes : Fin 15 → Nat) : Prop :=
  ∀ (k : Fin 15) (x : Fin 31671), (planes k).testBit x.val = x.val.testBit k.val

/-- Equality on the separating masks implies equality on every coordinate. -/
theorem BitAction.eq_of_planes {p q : Equiv.Perm (Fin 31671)}
    (a : BitAction p) (b : BitAction q) (planes : Fin 15 → Nat)
    (hplanes : SeparatingMasks planes)
    (h : ∀ k, a.transform (planes k) = b.transform (planes k)) : p = q := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 15
  · have he := congrArg (fun v : Nat => v.testBit x.val) (h ⟨k, hk⟩)
    rw [a.sound, b.sound, hplanes, hplanes] at he
    exact he
  · have hlarge (z : Fin 31671) : z.val.testBit k = false := by
      have hz : z.val < 2 ^ k :=
        lt_of_lt_of_le (lt_trans z.isLt (by decide : 31671 < 2 ^ 15))
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 15 ≤ k))
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hz]
    rw [hlarge, hlarge]

private theorem edge_cancel {G : Type*} [Group G] (r s t p : G)
    (h : s * t = r * p) : r⁻¹ * s * t = p := by
  rw [mul_assoc, h, inv_mul_cancel_left]

/-- Actual consumer of the bit-mask certificates, at the prescribed edge and
literal witness group. This leaves only finite equalities, not a subgroup
membership surrogate, to the residual-family producers. -/
theorem edge_mem_of_bitplanes
    (b : Bool) (x : Fin 31671) (p : Equiv.Perm (Fin 31671)) (hp : p ∈ witnessGroup)
    (a : BitAction (inclusion (letter b)))
    (r : BitAction (inclusion (representative x)))
    (s : BitAction (inclusion (representative (inclusion (letter b) x))))
    (w : BitAction p) (planes : Fin 15 → Nat) (hplanes : SeparatingMasks planes)
    (h : ∀ k, (a.mul r).transform (planes k) = (s.mul w).transform (planes k)) :
    inclusion (edge b x) ∈ witnessGroup := by
  have he := BitAction.eq_of_planes (a.mul r) (s.mul w) planes hplanes h
  have he' := edge_cancel _ _ _ _ he
  simpa only [edge, map_mul, map_inv] using he' ▸ hp

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
