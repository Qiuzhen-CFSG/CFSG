module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

namespace SmallNonabelianTwoGroup

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

public theorem order_five_actor_fixed_subgroup_eq_bot
    {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16)
    (actor : Subgroup (MulAut V)) (hactor : Nat.card actor = 5) :
    FixedPoints.subgroup actor V = ⊥ := by
  classical
  let fixed : Subgroup V := FixedPoints.subgroup actor V
  have hpgroup : IsPGroup 5 actor := IsPGroup.of_card (n := 1) (by simpa using hactor)
  have hmod := hpgroup.card_modEq_card_fixedPoints V
  change Nat.card V % 5 = Nat.card fixed % 5 at hmod
  rw [hV] at hmod
  have hdiv : Nat.card fixed ∣ 2 ^ 4 := by
    simpa [hV] using fixed.card_subgroup_dvd_card
  obtain ⟨dimension, hdimension, hcard⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdiv
  have hproper : fixed ≠ ⊤ := by
    intro htop
    have hbot : actor = ⊥ := by
      apply eq_bot_iff.mpr
      intro aut haut
      change aut = 1
      apply MulEquiv.ext
      intro vector
      have hmem : vector ∈ fixed := htop ▸ Subgroup.mem_top vector
      exact (FixedPoints.mem_subgroup (M := actor) (a := vector)).mp hmem ⟨aut, haut⟩
    have hbad : Nat.card actor = 1 := by simp [hbot]
    omega
  have hsmall : dimension < 4 := by
    by_contra hnot
    have heq : dimension = 4 := by omega
    exact hproper (fixed.eq_top_of_card_eq (by simpa [heq, hV] using hcard))
  have hone : Nat.card fixed = 1 := by
    rw [hcard] at hmod ⊢
    interval_cases dimension <;> norm_num at *
  exact Subgroup.card_eq_one.mp hone

public theorem invariant_fiber_card_mod_five_of_order_five_actor
    {V W : Type*} [Group V] [Finite V] [One W]
    (hV : Nat.card V = 16) (square : V → W) (hone : square 1 = 1)
    (actor : Subgroup (MulAut V)) (hactor : Nat.card actor = 5)
    (hinvariant : ∀ aut ∈ actor, ∀ vector, square (aut vector) = square vector) :
    Nat.card {vector : V // square vector = 1} % 5 = 1 := by
  classical
  let zeros := {vector : V // square vector = 1}
  let : MulAction actor zeros :=
    { smul aut vector := ⟨aut.val vector.val,
        (hinvariant aut.val aut.property vector.val).trans vector.property⟩
      one_smul vector := Subtype.ext (by rfl)
      mul_smul aut other vector := Subtype.ext (by rfl) }
  have hpgroup : IsPGroup 5 actor := IsPGroup.of_card (n := 1) (by simpa using hactor)
  have hmod := hpgroup.card_modEq_card_fixedPoints zeros
  have hfixed := order_five_actor_fixed_subgroup_eq_bot hV actor hactor
  have hval (vector : MulAction.fixedPoints actor zeros) : vector.val.val = 1 := by
    have hmem : vector.val.val ∈ FixedPoints.subgroup actor V := by
      rw [FixedPoints.mem_subgroup]
      intro aut
      exact congrArg Subtype.val (vector.property aut)
    simpa [hfixed] using hmem
  let : Unique (MulAction.fixedPoints actor zeros) :=
    { default := ⟨⟨1, hone⟩, by
        intro aut
        apply Subtype.ext
        exact map_one aut.val⟩
      uniq vector := by
        apply Subtype.ext
        apply Subtype.ext
        exact hval vector }
  change Nat.card zeros % 5 = Nat.card (MulAction.fixedPoints actor zeros) % 5 at hmod
  simpa using hmod

public theorem invariant_fiber_card_mod_five_of_five_dvd_actor
    {V W : Type*} [Group V] [Finite V] [One W]
    (hV : Nat.card V = 16) (square : V → W) (hone : square 1 = 1)
    (actor : Subgroup (MulAut V))
    (hinvariant : ∀ aut ∈ actor, ∀ vector, square (aut vector) = square vector)
    (hfive : 5 ∣ Nat.card actor) :
    Nat.card {vector : V // square vector = 1} % 5 = 1 := by
  obtain ⟨aut, horder⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let line : Subgroup (MulAut V) := Subgroup.zpowers aut.val
  have hline : Nat.card line = 5 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, horder]
  apply invariant_fiber_card_mod_five_of_order_five_actor hV square hone line hline
  intro other hother vector
  exact hinvariant other ((Subgroup.zpowers_le.mpr aut.property) hother) vector

end SmallNonabelianTwoGroup

