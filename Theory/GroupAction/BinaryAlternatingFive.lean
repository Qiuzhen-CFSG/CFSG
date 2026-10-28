module
public import Theory.GroupAction.Invariant
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# No one-dimensional image for an alternating pairing under a five-action

Let an order-five group act on both arguments and the target of a symmetric
alternating group pairing. Suppose the target has no nonidentity fixed point
and the orbit of v generates the domain. The image of the pairing at v
cannot have order two.

If that image were a line, each nonidentity actor would move its unique
nonidentity element. Symmetry puts the value on v and a translate of v in
both the line and its translate, so it vanishes. Generation makes the whole
image trivial. This is a source-neutral form of the commutator-line argument
for Parrott's two-core centralizer bound (1972), pp.673–674.
-/

namespace Theory.GroupAction
open Subgroup
open scoped IsMulCommutative

/-- A symmetric alternating pairing has no two-element image at a vector
whose five-orbit generates the domain, if the target action is fixed-free. -/
public theorem alternating_pairing_range_card_ne_two_of_five_orbit
    {A V W : Type*} [Group A] [Finite A] [Group V] [Group W]
    [Finite W] [IsMulCommutative W]
    [MulDistribMulAction A V] [MulDistribMulAction A W]
    (hA : Nat.card A = 5) (hfixed : FixedPoints.subgroup A W = ⊥)
    (f : V →* (V →* W)) (halt : ∀ x, f x x = 1)
    (hsymm : ∀ x y, f x y = f y x)
    (hequiv : ∀ (a : A) (x y : V), f (a • x) (a • y) = a • f x y)
    (v : V) (hgen : closure (Set.range fun a : A => a • v) = ⊤) :
    Nat.card (f v).range ≠ 2 := by
  classical
  intro htwo
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : (f v).range)).mp htwo
  have hwne : (w : W) ≠ 1 := fun h => hw (Subtype.ext h)
  have hline (u : W) (hu : u ∈ (f v).range) (hne : u ≠ 1) : u = w := by
    exact congrArg Subtype.val (huniq ⟨u, hu⟩ (fun h => hne (congrArg Subtype.val h)))
  have hfree (a : A) (ha : a ≠ 1) : a • (w : W) ≠ w := by
    intro haw
    let : Fact (Nat.Prime (Nat.card A)) := ⟨by rw [hA]; decide⟩
    rcases (MulAction.stabilizer A (w : W)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hm : a ∈ MulAction.stabilizer A (w : W) := haw
      rw [hb] at hm
      exact ha hm
    · apply hwne
      apply hfixed.le
      intro b
      have hm : b ∈ MulAction.stabilizer A (w : W) := ht ▸ mem_top b
      exact hm
  have hzero (a : A) : f v (a • v) = 1 := by
    by_cases ha : a = 1
    · subst a
      simpa only [one_smul] using halt v
    by_contra hn
    have hleft : f v (a • v) = w := hline _ ⟨a • v, rfl⟩ hn
    have hright : a • f v (a⁻¹ • v) = f v (a • v) := by
      rw [← hequiv, smul_inv_smul, hsymm]
    have hne : f v (a⁻¹ • v) ≠ 1 := by
      intro hh
      rw [hh, smul_one] at hright
      exact hn hright.symm
    have hh := hline _ ⟨a⁻¹ • v, rfl⟩ hne
    exact hfree a ha (by rw [hh, hleft] at hright; exact hright)
  have hker : (f v).ker = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    exact hzero a
  have hrange : (f v).range = ⊥ := by
    apply bot_unique
    rintro x ⟨y, rfl⟩
    exact (show y ∈ (f v).ker from hker ▸ mem_top y)
  rw [hrange, card_bot] at htwo
  omega

end Theory.GroupAction
