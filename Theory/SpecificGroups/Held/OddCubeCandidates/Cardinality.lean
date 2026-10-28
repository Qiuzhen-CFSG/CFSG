module

public import Theory.SpecificGroups.Held.OddCubeCandidates
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality.Certificates
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The two concrete Held odd-subgroup orders

The original generator closures have orders 27 and 343. The proof collects
words using the central correction z = y⁻¹*x⁻¹*y*x and reduces three
exponents modulo p. A kernel-checked decoder of the action on point zero
separates the p³ normal forms. Faithfulness of the defining representation
transfers the cardinalities back to the unchanged subgroups of Held.He.

Source: GLS3 Table 5.3p; the Held case of Aschbacher–Smith, Theorem
0.1.2(5), printed p.4. The permutation certificates use only the explicit
ATLAS model and do not assume the order or simplicity of the ambient group.
-/

namespace Held.OddCubeCandidates
namespace CardinalityProof
variable {G : Type*} [Group G]

private theorem swap (x y z : G) (hxz : Commute x z)
    (hxy : y * x = x * y * z) (i : ℕ) :
    y * x ^ i = x ^ i * y * z ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      y * x ^ (i + 1) = (y * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = (x ^ i * y * z ^ i) * x := by rw [ih]
      _ = x ^ i * (y * x) * z ^ i := by
        rw [mul_assoc, (hxz.symm.pow_left i).eq]
        simp only [mul_assoc]
      _ = x ^ (i + 1) * y * z ^ (i + 1) := by
        rw [hxy, pow_succ, pow_succ']
        simp only [mul_assoc]

private theorem y_step (x y z : G) (hxz : Commute x z) (hyz : Commute y z)
    (hxy : y * x = x * y * z) (i j k : ℕ) :
    y * (x ^ i * y ^ j * z ^ k) = x ^ i * y ^ (j + 1) * z ^ (i + k) := by
  calc
    _ = (x ^ i * y * z ^ i) * y ^ j * z ^ k := by
      rw [← mul_assoc, ← mul_assoc, swap x y z hxz hxy]
    _ = x ^ i * (y * y ^ j) * (z ^ i * z ^ k) := by
      rw [mul_assoc (x ^ i * y), (hyz.symm.pow_pow i j).eq]
      simp only [mul_assoc]
    _ = _ := by rw [← pow_succ', ← pow_add]

private theorem cover (x y z : G) (p : ℕ) (hp : 0 < p)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hxz : Commute x z) (hyz : Commute y z) (hxy : y * x = x * y * z)
    {g : G} (hg : g ∈ Subgroup.closure {x, y}) :
    ∃ t : Fin p × Fin p × Fin p, x ^ t.1.val * y ^ t.2.1.val * z ^ t.2.2.val = g := by
  let P : G → Prop := fun g => ∃ i j k : ℕ, x ^ i * y ^ j * z ^ k = g
  have hstepX : ∀ g, P g → P (x * g) := by
    rintro _ ⟨i, j, k, rfl⟩
    exact ⟨i + 1, j, k, by simp only [pow_succ', mul_assoc]⟩
  have hstepY : ∀ g, P g → P (y * g) := by
    rintro _ ⟨i, j, k, rfl⟩
    exact ⟨i, j + 1, i + k, (y_step x y z hxz hyz hxy i j k).symm⟩
  have hinv (a : G) (ha : a ^ p = 1) (hs : ∀ g, P g → P (a * g)) :
      ∀ g, P g → P (a⁻¹ * g) := by
    have hpow (n : ℕ) : ∀ g, P g → P (a ^ n * g) := by
      induction n with
      | zero => simp
      | succ n ih =>
        intro g hg
        simpa only [pow_succ', mul_assoc] using hs _ (ih g hg)
    have hi : a ^ (p - 1) = a⁻¹ := by
      rw [pow_sub a hp, ha, pow_one, one_mul]
    intro g hg
    simpa only [hi] using hpow (p - 1) g hg
  have hP : P g := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_left a ha b _ ih =>
      rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
      · exact hstepX b ih
      · exact hstepY b ih
    | inv_mul_cancel a ha b _ ih =>
      rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
      · exact hinv _ hx hstepX b ih
      · exact hinv _ hy hstepY b ih
  obtain ⟨i, j, k, rfl⟩ := hP
  refine ⟨(⟨i % p, Nat.mod_lt _ hp⟩, ⟨j % p, Nat.mod_lt _ hp⟩,
    ⟨k % p, Nat.mod_lt _ hp⟩), ?_⟩
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (pow_eq_pow_mod i hx).symm (pow_eq_pow_mod j hy).symm) (pow_eq_pow_mod k hz).symm

private theorem card (x y z : G) (p : ℕ) (hp : 0 < p)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hxz : Commute x z) (hyz : Commute y z) (hxy : y * x = x * y * z)
    (hzmem : z ∈ Subgroup.closure {x, y})
    (hinj : Function.Injective (fun t : Fin p × Fin p × Fin p =>
      x ^ t.1.val * y ^ t.2.1.val * z ^ t.2.2.val)) :
    Nat.card (Subgroup.closure {x, y}) = p ^ 3 := by
  let H := Subgroup.closure ({x, y} : Set G)
  have hxm : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hym : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let f : Fin p × Fin p × Fin p → H := fun t =>
    ⟨x ^ t.1.val * y ^ t.2.1.val * z ^ t.2.2.val,
      H.mul_mem (H.mul_mem (H.pow_mem hxm _) (H.pow_mem hym _)) (H.pow_mem hzmem _)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      exact hinj (congrArg Subtype.val h)
    · intro g
      obtain ⟨t, ht⟩ := cover x y z p hp hx hy hz hxz hyz hxy g.property
      exact ⟨t, Subtype.ext ht⟩
  simpa only [Nat.card_prod, Nat.card_fin, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using
    (Nat.card_eq_of_bijective f hf).symm

private theorem correction_mem (x y : G) :
    y⁻¹ * x⁻¹ * y * x ∈ Subgroup.closure {x, y} := by
  let H := Subgroup.closure ({x, y} : Set G)
  have hx : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hy) (H.inv_mem hx)) hy) hx

open CardinalityCertificates

/-- The first unchanged generator closure in the actual Held carrier has order 27. -/
public theorem _root_.Held.OddCubeCandidates.card_three : Nat.card three = 27 := by
  rw [← Subgroup.card_map_of_injective (K := three) representation_injective]
  rw [three, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    ← threeX_eq, ← threeY_eq]
  exact card threeX threeY threeZ 3 (by decide)
    threeX_pow threeY_pow threeZ_pow threeX_commute threeY_commute three_swap
    (threeZ_eq.symm ▸ correction_mem threeX threeY) three_normalForm_injective

/-- The second unchanged generator closure in the actual Held carrier has order 343. -/
public theorem _root_.Held.OddCubeCandidates.card_seven : Nat.card seven = 343 := by
  rw [← Subgroup.card_map_of_injective (K := seven) representation_injective]
  rw [seven, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    ← sevenX_eq, ← sevenY_eq]
  exact card sevenX sevenY sevenZ 7 (by decide)
    sevenX_pow sevenY_pow sevenZ_pow sevenX_commute sevenY_commute seven_swap
    (sevenZ_eq.symm ▸ correction_mem sevenX sevenY) seven_normalForm_injective

end CardinalityProof
end Held.OddCubeCandidates
