module

public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two

/-!
# Square-one lifts from involution fusion and an elementary eight-group

In a central extension with elementary two-kernel, conjugate involutions
have lifts with equal squares. An embedded elementary group of rank three
rules out a constant nonidentity square: the commutator pairing is additive,
whereas that constant square would make its values at (u,v), (u,w), and
(u,v+w) equal and nonidentity. Rank two does not suffice, as Q₈ shows.

The concrete consumer is the marked heptad translation group in M₂₃.
No involutory lift is assumed and no module classification is used.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.CentralDoubleCoverFusion
variable {E G : Type*} [Group E] [Group G]

private theorem square_eq_of_conjugate_images (f : E →* G)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (h2 : ∀ k ∈ f.ker, k ^ 2 = 1)
    {x y : E} (hx : orderOf (f x) = 2) (hxy : IsConj (f x) (f y)) :
    x ^ 2 = y ^ 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  obtain ⟨a, rfl⟩ := hf g
  have hxk : x ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact (orderOf_eq_prime_iff.mp hx).1
  have hxc : Commute a (x ^ 2) := mem_center_iff.mp (hc hxk) a
  have hp : f (a * x * a⁻¹) = f y := by simpa only [map_mul, map_inv] using hg
  calc
    x ^ 2 = (a * x * a⁻¹) ^ 2 := by
      calc
        x ^ 2 = a * x ^ 2 * a⁻¹ := by rw [hxc.eq, mul_inv_cancel_right]
        _ = (a * x * a⁻¹) ^ 2 := by simp only [pow_two]; group
    _ = y ^ 2 := PerfectCentralCovering.square_eq_of_map_eq_of_kernel_exponent_two
      f hc h2 hp

private theorem commutator_eq_of_three_squares (x y k : E)
    (hk : k ∈ center E) (hk2 : k ^ 2 = 1)
    (hx : x ^ 2 = k) (hy : y ^ 2 = k) (hxy : (x * y) ^ 2 = k) :
    ⁅x, y⁆ = k := by
  have hxi : x⁻¹ = x * k := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← mul_assoc, ← pow_two, hx, ← pow_two, hk2]
  have hyi : y⁻¹ = y * k := by
    apply mul_left_cancel (a := y)
    rw [mul_inv_cancel, ← mul_assoc, ← pow_two, hy, ← pow_two, hk2]
  have hky : k * y = y * k := (mem_center_iff.mp hk y).symm
  calc
    ⁅x, y⁆ = x * y * (x * k) * (y * k) := by
      rw [commutatorElement_def, hxi, hyi]
    _ = x * y * x * (k * y) * k := by group
    _ = x * y * x * (y * k) * k := by rw [hky]
    _ = (x * y) ^ 2 * k ^ 2 := by simp only [pow_two]; group
    _ = k := by rw [hxy, hk2, mul_one]

/-- One involution class and an actual elementary eight-subgroup force
square-one lifts through any central extension of kernel exponent two. -/
theorem square_eq_one_of_fusion (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (h2 : ∀ k ∈ f.ker, k ^ 2 = 1)
    (u : Multiplicative (Fin 3 → ZMod 2) →* G) (hu : Function.Injective u)
    (hclass : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (x : E) (hx : orderOf (f x) = 2) : x ^ 2 = 1 := by
  let k := x ^ 2
  have hk : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact (orderOf_eq_prime_iff.mp hx).1
  have hks (v : Fin 3 → ZMod 2) (hv : v ≠ 0) (a : E)
      (ha : f a = u (Multiplicative.ofAdd v)) : a ^ 2 = k := by
    have hv2 : (Multiplicative.ofAdd v) ^ 2 = 1 := by
      rw [pow_two]
      change v + v = 0
      ext i
      exact CharTwo.add_self_eq_zero (v i)
    have ho : orderOf (f a) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      constructor
      · rw [ha, ← map_pow, hv2, map_one]
      · rw [ha]
        intro h
        have he := hu (h.trans u.map_one.symm)
        exact hv (congrArg Multiplicative.toAdd he)
    exact square_eq_of_conjugate_images f hf hc h2 ho (hclass _ _ ho hx)
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing f hf hc u
  have hBk (v w : Fin 3 → ZMod 2) (hv : v ≠ 0) (hw : w ≠ 0)
      (hvw : v + w ≠ 0) : ((B v w).toMul : E) = k := by
    obtain ⟨a, ha⟩ := hf (u (Multiplicative.ofAdd v))
    obtain ⟨b, hb⟩ := hf (u (Multiplicative.ofAdd w))
    rw [hB v w a b ha hb]
    apply commutator_eq_of_three_squares a b k (hc hk) (h2 k hk)
      (hks v hv a ha) (hks w hw b hb)
    apply hks (v + w) hvw (a * b)
    rw [map_mul, ha, hb, ← map_mul]
    rfl
  let v : Fin 3 → ZMod 2 := Pi.single 0 1
  let w : Fin 3 → ZMod 2 := Pi.single 1 1
  let z : Fin 3 → ZMod 2 := Pi.single 2 1
  have h1 := hBk v w (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h2' := hBk v z (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h3 := hBk v (w + z) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he := congrArg (fun t : Additive (center E) => (t.toMul : E))
    ((B v).map_add w z)
  change ((B v (w + z)).toMul : E) = ((B v w).toMul : E) * ((B v z).toMul : E) at he
  rw [h1, h2', h3] at he
  exact (mul_left_cancel (show k * 1 = k * k by simpa using he)).symm

/-- The double-cover form used by the literal finite-group source consumer. -/
theorem square_eq_one_of_double_cover [Finite E]
    (f : E →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hcard : Nat.card f.ker = 2)
    (u : Multiplicative (Fin 3 → ZMod 2) →* G) (hu : Function.Injective u)
    (hclass : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (x : E) (hx : (f x) ^ 2 = 1) : x ^ 2 = 1 := by
  have h2 : ∀ k ∈ f.ker, k ^ 2 = 1 := by
    intro k hk
    have h := pow_card_eq_one' (x := (⟨k, hk⟩ : f.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  by_cases hx1 : f x = 1
  · exact h2 x hx1
  · exact square_eq_one_of_fusion f hf hc h2 u hu hclass x
      (orderOf_eq_prime_iff.mpr ⟨hx, hx1⟩)

end Theory.GroupTheory.CentralDoubleCoverFusion
