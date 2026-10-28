module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.PGroup

/-!
# Primitivity from a unique prime-order fixed point

If a prime-power cyclic permutation fixes just one point, every block
containing that point has cardinality congruent to one modulo the prime.
When the degree has no proper divisor with that congruence, the action is
primitive. This is used on the 36 off-scalar binary G₂ cover hyperplanes.
-/

public noncomputable section
open scoped Pointwise
namespace MulAction

/-- A transitive point stabilizer on the complement forces primitivity. -/
theorem isPreprimitive_of_stabilizer_transitive
    {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
    (a : X)
    (htrans : ∀ x y : X, x ≠ a → y ≠ a →
      ∃ g : G, g • a = a ∧ g • x = y) :
    IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases he : ∃ b ∈ B, b ≠ a
  · obtain ⟨b, hb, hba⟩ := he
    right
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxa : x = a
    · exact hxa.symm ▸ ha
    · obtain ⟨g, hga, hgb⟩ := htrans b x hba hxa
      have hgB := hB.stabilizer_le ha hga
      rw [← hgb]
      exact (mem_stabilizer_set.mp hgB b).mpr hb
  · left
    intro x hx y hy
    have hxa : x = a := not_ne_iff.mp (fun hn => he ⟨x, hx, hn⟩)
    have hya : y = a := not_ne_iff.mp (fun hn => he ⟨y, hy, hn⟩)
    exact hxa.trans hya.symm

theorem isPreprimitive_of_unique_fixed_prime
    {G X : Type*} [Group G] [MulAction G X] [Finite X] [IsPretransitive G X]
    (p : ℕ) (hp : p.Prime) (g : G) (a : X)
    (hpow : (toPerm g : Equiv.Perm X) ^ p = 1)
    (hfix : ∀ x : X, g • x = x ↔ x = a)
    (harith : ∀ n : ℕ, n ∣ Nat.card X → n % p = 1 % p →
      n = 1 ∨ n = Nat.card X) :
    IsPreprimitive G X := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  let f : Equiv.Perm X := toPerm g
  let P := Subgroup.zpowers f
  have hP : IsPGroup p P := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hpow)
  have hfB : f ∈ stabilizer (Equiv.Perm X) B := by
    change g • B = B
    exact hB.stabilizer_le ha ((hfix a).mpr rfl)
  have hPB : P ≤ stabilizer (Equiv.Perm X) B := Subgroup.zpowers_le.mpr hfB
  have hPa : P ≤ stabilizer (Equiv.Perm X) a :=
    Subgroup.zpowers_le.mpr ((hfix a).mpr rfl)
  let S : SubMulAction P X := {
    carrier := B
    smul_mem' k x hx := (mem_stabilizer_set.mp (hPB k.property) x).mpr hx }
  have hsub : Subsingleton (fixedPoints P S) := by
    constructor
    intro x y
    have he (z : fixedPoints P S) : (z.val : X) = a := by
      apply (hfix (z.val : X)).mp
      exact congrArg (fun s : S => (s : X))
        (z.property ⟨f, Subgroup.mem_zpowers f⟩)
    exact Subtype.ext (Subtype.ext ((he x).trans (he y).symm))
  have hne : Nonempty (fixedPoints P S) := by
    refine ⟨⟨⟨a, ha⟩, ?_⟩⟩
    intro k
    exact Subtype.ext (hPa k.property)
  have hc : Nat.card (fixedPoints P S) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩
  have hm := hP.card_modEq_card_fixedPoints S
  rw [hc] at hm
  change B.ncard % p = 1 % p at hm
  rcases harith B.ncard (hB.ncard_dvd_card ⟨a, ha⟩) hm with hsmall | hwhole
  · exact Or.inl (B.ncard_le_one_iff_subsingleton.mp hsmall.le)
  · exact Or.inr (B.eq_univ_iff_ncard.mpr hwhole)

end MulAction
