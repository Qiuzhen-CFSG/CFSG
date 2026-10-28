module

public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupAction.QuotientFixedIndex
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A fixed-point invariant for cubic actions on two-groups

For a three-group acting on a finite two-group, the fixed subgroup has index
`4^n`. Define its cubic length to be `log₄` of this actual index. Orbit counting
modulo three proves integrality. Coprime fixed-point lifting proves
multiplicativity of indices across invariant normal quotients, hence additivity
of the length. Equivariant isomorphisms preserve the length, and equivariant
subquotients cannot increase it.

These facts provide a numerical alternative to chief-series refinement in
Aschbacher–Smith 13.8.33 (printed p.968). A nontrivial irreducible binary module
for a cyclic actor of order three contributes one. Applications must retain
the actual actor and establish the fixed indices of their module sections.
-/

@[expose] public section

namespace FixedPoints

variable {A V W : Type*} [Group A] [Group V] [Group W]
  [MulDistribMulAction A V] [MulDistribMulAction A W]

/-- The intrinsic cubic fixed-point invariant. -/
noncomputable def cubicLength (A V : Type*) [Group A] [Group V]
    [MulDistribMulAction A V] : ℕ := Nat.log 4 (subgroup A V).index

/-- An equivariant injective map reflects the fixed subgroup. -/
theorem comap_fixed_of_injective (f : V →* W) (hf : Function.Injective f)
    (heq : ∀ (a : A) v, f (a • v) = a • f v) :
    (subgroup A W).comap f = subgroup A V := by
  ext v
  constructor
  · intro hv a
    apply hf
    rw [heq]
    exact hv a
  · intro hv a
    rw [← heq, hv a]

/-- Fixed indices cannot increase on an equivariant subgroup. -/
theorem index_le_of_injective [Finite W]
    (f : V →* W) (hf : Function.Injective f)
    (heq : ∀ (a : A) v, f (a • v) = a • f v) :
    (subgroup A V).index ≤ (subgroup A W).index := by
  rw [← comap_fixed_of_injective f hf heq, Subgroup.index_comap]
  simpa only [Subgroup.relIndex_top_right] using
    (subgroup A W).relIndex_le_of_le_right (show f.range ≤ ⊤ from le_top)
      (by simpa using (Subgroup.FiniteIndex.index_ne_zero (H := subgroup A W)))

/-- Both the group map and its action compatibility are retained. -/
theorem index_eq_of_equivariant (e : V ≃* W)
    (heq : ∀ (a : A) v, e (a • v) = a • e v) :
    (subgroup A V).index = (subgroup A W).index := by
  rw [← comap_fixed_of_injective e.toMonoidHom e.injective heq,
    Subgroup.index_comap, e.toMonoidHom.range_eq_top_of_surjective e.surjective,
    Subgroup.relIndex_top_right]

theorem cubicLength_eq_of_equivariant (e : V ≃* W)
    (heq : ∀ (a : A) v, e (a • v) = a • e v) :
    cubicLength A V = cubicLength A W := by
  unfold cubicLength
  rw [index_eq_of_equivariant e heq]

omit [MulDistribMulAction A W] in
/-- Changing the actor through a surjective homomorphism preserves the
invariant, provided the actual group isomorphism intertwines the actions. -/
theorem index_eq_of_equivariant_surjective_actor {B : Type*} [Group B]
    [MulDistribMulAction B W] (f : A →* B) (hf : Function.Surjective f)
    (e : V ≃* W) (heq : ∀ (a : A) v, e (a • v) = f a • e v) :
    (subgroup A V).index = (subgroup B W).index := by
  have hc : (subgroup B W).comap e.toMonoidHom = subgroup A V := by
    ext v
    constructor
    · intro hv a
      apply e.injective
      rw [heq]
      exact hv (f a)
    · intro hv b
      obtain ⟨a, rfl⟩ := hf b
      change f a • e v = e v
      rw [← heq, hv a]
  rw [← hc, Subgroup.index_comap,
    e.toMonoidHom.range_eq_top_of_surjective e.surjective, Subgroup.relIndex_top_right]

omit [MulDistribMulAction A W] in
theorem cubicLength_eq_of_equivariant_surjective_actor {B : Type*} [Group B]
    [MulDistribMulAction B W] (f : A →* B) (hf : Function.Surjective f)
    (e : V ≃* W) (heq : ∀ (a : A) v, e (a • v) = f a • e v) :
    cubicLength A V = cubicLength B W := by
  unfold cubicLength
  rw [index_eq_of_equivariant_surjective_actor f hf e heq]

theorem cubicLength_eq_zero_of_trivial (h : ∀ (a : A) (v : V), a • v = v) :
    cubicLength A V = 0 := by
  have hc : subgroup A V = ⊤ := by
    ext v
    simp only [Subgroup.mem_top, iff_true]
    exact fun a => h a v
  simp [cubicLength, hc]

theorem cubicLength_le_of_injective [Finite W]
    (f : V →* W) (hf : Function.Injective f)
    (heq : ∀ (a : A) v, f (a • v) = a • f v) :
    cubicLength A V ≤ cubicLength A W :=
  Nat.log_mono_right (index_le_of_injective f hf heq)

theorem cubicLength_le_of_surjective [Finite V] [Finite W]
    (f : V →* W) (hf : Function.Surjective f)
    (heq : ∀ (a : A) v, f (a • v) = a • f v) :
    cubicLength A W ≤ cubicLength A V :=
  Nat.log_mono_right (fixedPoints_index_le_of_surjective_equivariant f hf heq)

private theorem even_of_two_pow_mod_three {n : ℕ} (h : 2 ^ n % 3 = 1) :
    n % 2 = 0 := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  conv_lhs at h => rw [hn, pow_add, pow_mul]
  have hfour : 4 ^ (n / 2) % 3 = 1 := by
    rw [Nat.pow_mod]
    simp
  rw [show 2 ^ 2 = 4 from rfl, Nat.mul_mod, hfour, one_mul, Nat.mod_mod] at h
  rcases Nat.mod_two_eq_zero_or_one n with hz | ho
  · exact hz
  · rw [ho] at h
    norm_num at h

/-- Orbit counting makes the actual fixed index a power of four. -/
theorem index_eq_four_pow_cubicLength [Finite V]
    (hA : IsPGroup 3 A) (hV : IsPGroup 2 V) :
    (subgroup A V).index = 4 ^ cubicLength A V := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hV.index (subgroup A V)
  obtain ⟨c, hc⟩ := (hV.to_subgroup (subgroup A V)).exists_card_eq
  have hm := hA.card_modEq_card_fixedPoints V
  change Nat.card V ≡ Nat.card (subgroup A V) [MOD 3] at hm
  rw [← (subgroup A V).index_mul_card] at hm
  have hcop : Nat.Coprime 3 (Nat.card (subgroup A V)) := by
    rw [hc]
    exact Nat.Coprime.pow_right c (by decide)
  have hm' : (subgroup A V).index ≡ 1 [MOD 3] := by
    apply Nat.ModEq.cancel_right_of_coprime hcop
    simpa only [one_mul] using hm
  have he : n % 2 = 0 := even_of_two_pow_mod_three (by simpa [Nat.ModEq, hn] using hm')
  have hp : (subgroup A V).index = 4 ^ (n / 2) := by
    calc
      _ = 2 ^ n := hn
      _ = 2 ^ (2 * (n / 2)) := by congr 1; omega
      _ = 4 ^ (n / 2) := by rw [pow_mul]; rfl
  unfold cubicLength
  rw [hp, Nat.log_pow (by decide : 1 < 4)]

/-- The coprime fixed-point theorem gives multiplicativity of actual indices.
The kernel contribution is the index of its literal intersection with the
fixed subgroup. No normality of the fixed subgroup is required. -/
theorem index_eq_quotient_mul_kernel_of_coprime [Finite A] [Finite V]
    (hsolv : Group.IsSolvable V) (hcop : Nat.Coprime (Nat.card A) (Nat.card V))
    (N : Subgroup V) [N.Normal] (hN : IsInvariant A V N) :
    letI : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
    (subgroup A V).index =
      (subgroup A (V ⧸ N)).index * (N ⊓ subgroup A V).relIndex N := by
  let : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
  have hfixed := card_eq_quotient_mul_kernel_of_coprime hsolv hcop N hN
  have hkernel : Nat.card ↥(N ⊓ subgroup A V) * (N ⊓ subgroup A V).relIndex N =
      Nat.card N := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) (N ⊓ subgroup A V) N bot_le inf_le_left
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := subgroup A V))
  calc
    (subgroup A V).index * Nat.card (subgroup A V) = Nat.card V :=
      (subgroup A V).index_mul_card
    _ = Nat.card (V ⧸ N) * Nat.card N := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    _ = ((subgroup A (V ⧸ N)).index * Nat.card (subgroup A (V ⧸ N))) *
        (Nat.card ↥(N ⊓ subgroup A V) * (N ⊓ subgroup A V).relIndex N) := by
      rw [Subgroup.index_mul_card, hkernel]
    _ = ((subgroup A (V ⧸ N)).index * (N ⊓ subgroup A V).relIndex N) *
        Nat.card (subgroup A V) := by rw [hfixed]; ring

/-- Additivity across an actual invariant normal quotient. -/
theorem cubicLength_eq_quotient_add_subgroup [Finite A] [Finite V]
    (hA : IsPGroup 3 A) (hV : IsPGroup 2 V)
    (hsolv : Group.IsSolvable V)
    (N : Subgroup V) [N.Normal] (hN : IsInvariant A V N) :
    letI := hN
    letI : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
    cubicLength A V = cubicLength A (V ⧸ N) + cubicLength A N := by
  let := hN
  let : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    obtain ⟨a, ha⟩ := hA.exists_card_eq
    obtain ⟨v, hv⟩ := hV.exists_card_eq
    rw [ha, hv]
    exact ((by decide : Nat.Coprime 3 2).pow_left a).pow_right v
  have hker : (N ⊓ subgroup A V).subgroupOf N = subgroup A N := by
    ext n
    constructor
    · intro hn a
      exact Subtype.ext (hn.2 a)
    · intro hn
      exact ⟨n.property, fun a => congrArg Subtype.val (hn a)⟩
  have hi := index_eq_quotient_mul_kernel_of_coprime hsolv hcop N hN
  change (subgroup A V).index =
    (subgroup A (V ⧸ N)).index * ((N ⊓ subgroup A V).subgroupOf N).index at hi
  rw [hker, index_eq_four_pow_cubicLength hA hV,
    index_eq_four_pow_cubicLength hA (hV.to_quotient N),
    index_eq_four_pow_cubicLength hA (hV.to_subgroup N), ← pow_add] at hi
  exact Nat.pow_right_injective (by decide : 2 ≤ 4) hi

/-- A central section makes no contribution. This permits the natural module
calculations to pass through the central kernels in the source covers. -/
theorem cubicLength_eq_quotient_of_trivial_kernel [Finite A] [Finite V]
    (hA : IsPGroup 3 A) (hV : IsPGroup 2 V) (hsolv : Group.IsSolvable V)
    (N : Subgroup V) [N.Normal] (hN : IsInvariant A V N)
    (htriv : ∀ (a : A) (n : N), a • (n : V) = n) :
    letI : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
    cubicLength A V = cubicLength A (V ⧸ N) := by
  let := hN
  let : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N hN
  have hi := cubicLength_eq_quotient_add_subgroup hA hV hsolv N hN
  have hz : cubicLength A N = 0 :=
    cubicLength_eq_zero_of_trivial (fun a n => Subtype.ext (htriv a n))
  simpa only [hz, add_zero] using hi

end FixedPoints
