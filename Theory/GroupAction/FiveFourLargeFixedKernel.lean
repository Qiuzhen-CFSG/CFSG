module

public import Theory.GroupAction.FiveFourInvolutionFixed

/-!
# Detecting the kernel from a large fixed subgroup

In a faithful five-four action on elementary sixteen, every nonidentity
element whose square is one fixes exactly four vectors. Consequently an
involution in a group mapping to the five-four group lies in the kernel
if it fixes more than four vectors. A subgroup of order at least sixteen
mapping to fixed vectors through a homomorphism with kernel of order at
most two supplies this bound.

This is the action-theoretic inference used in Thompson VI, printed p.630:
the fixed subgroup on the derived quotient has order at least eight.
-/

namespace Theory.GroupAction
open Subgroup

/-- An element of square one fixing more than four vectors has trivial
image in a faithful five-four action on elementary sixteen. -/
public theorem mem_ker_of_five_four_large_fixed
    {H V : Type*} [Group H] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (π : H →* SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (y : H) (hy : y ^ 2 = 1)
    (hfixed : 4 < Nat.card (FixedPoints.subgroup (zpowers (f (π y))) V)) :
    y ∈ π.ker := by
  apply MonoidHom.mem_ker.mpr
  by_contra hne
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf (π y) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hy, map_one]) hne
  have hc := (five_four_involution_fixed_displacement hV φ hφ f hf (π y) horder).1
  omega

/-- A large subgroup fixed modulo a kernel of order at most two gives
enough fixed vectors to detect the five-four kernel. -/
public theorem mem_ker_of_five_four_fixed_layer
    {H U V : Type*} [Group H] [Group U] [Finite U]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (π : H →* SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (q : U →* V) (hq : Nat.card q.ker ≤ 2)
    (E : Subgroup U) (hE : 16 ≤ Nat.card E)
    (y : H) (hy : y ^ 2 = 1)
    (hfixed : ∀ e : E, f (π y) (q e) = q e) :
    y ∈ π.ker := by
  let F := FixedPoints.subgroup (zpowers (f (π y))) V
  let r : E →* V := q.comp E.subtype
  have hker : Nat.card r.ker ≤ 2 := by
    let i : r.ker → q.ker := fun e => ⟨e.val.val, e.property⟩
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun v : q.ker => (v : U)) hab))
    exact (Nat.card_le_card_of_injective i hi).trans hq
  have hrange : r.range ≤ F := by
    rintro v ⟨e, rfl⟩
    exact (MulAut.mem_fixed_zpowers_iff _ _).mpr (hfixed e)
  have hcard := r.ker.card_mul_index
  rw [index_ker] at hcard
  have hbound : Nat.card E ≤ 2 * Nat.card F := by
    rw [← hcard]
    exact Nat.mul_le_mul hker (card_le_of_le hrange)
  apply mem_ker_of_five_four_large_fixed hV φ hφ π f hf y hy
  change 4 < Nat.card F
  omega

end Theory.GroupAction
