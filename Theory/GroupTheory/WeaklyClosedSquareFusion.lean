module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow

/-!+# Squares and weak closure

Let `z` be weakly closed in a subgroup `H`. If all squares of `U` lie in
`H` and `z` is a square in `U`, then every ambient normalizer of `U` fixes
`z`: its conjugate is still a square in `U`, and hence belongs to `H`.
Consequently, a normalizer moving `z` excludes a square root of `z` in `U`.
If every nonelementary possibility for `U` supplies such a root, `U` is
elementary abelian.

This is the square obstruction in Janko–Thompson, Math. Z. 113 (1970),
§4, Case 2, p.393. The local centralizer structure and the existence of a
normalizer moving the involution are separate hypotheses.
-/

namespace Subgroup

/-- A weakly closed power contained in a subgroup is fixed by its normalizer
when every such power lies in the weak-closure domain. -/
public theorem normalizer_le_centralizer_of_weakly_closed_power
    {G : Type*} [Group G] (H U : Subgroup G) (z : G) (n : ℕ)
    (hweak : ∀ t ∈ H, IsConj z t → t = z)
    (hpowers : ∀ x ∈ U, x ^ n ∈ H)
    (hroot : ∃ x ∈ U, x ^ n = z) :
    normalizer (U : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨x, hx, rfl⟩ := hroot
  intro g hg
  have hxg : (MulAut.conj g) x ∈ U := (hg x).mp hx
  have hmem : (MulAut.conj g) (x ^ n) ∈ H := by
    rw [map_pow]
    exact hpowers _ hxg
  have heq := hweak _ hmem (isConj_iff.mpr ⟨g, rfl⟩)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)

/-- A normalizer moving a weakly closed involution prevents it from being
a square when all squares lie in the weak-closure domain. -/
public theorem not_square_of_weakly_closed_of_normalizer_not_le
    {G : Type*} [Group G] (H U : Subgroup G) (z : G)
    (hweak : ∀ t ∈ H, IsConj z t → t = z)
    (hsquares : ∀ x ∈ U, x ^ 2 ∈ H)
    (hmove : ¬ normalizer (U : Set G) ≤ centralizer ({z} : Set G)) :
    ¬ ∃ x ∈ U, x ^ 2 = z :=
  fun hroot => hmove
    (normalizer_le_centralizer_of_weakly_closed_power H U z 2 hweak hsquares hroot)

/-- The weak-closure square obstruction makes a subgroup elementary if
each element with nontrivial square supplies a square root of `z`. -/
public theorem elementary_of_weakly_closed_square_obstruction
    {G : Type*} [Group G] (H U : Subgroup G) (z : G)
    (hweak : ∀ t ∈ H, IsConj z t → t = z)
    (hsquares : ∀ x ∈ U, x ^ 2 ∈ H)
    (hmove : ¬ normalizer (U : Set G) ≤ centralizer ({z} : Set G))
    (hroot : ∀ x ∈ U, x ^ 2 ≠ 1 → ∃ y ∈ U, y ^ 2 = z) :
    IsElementaryAbelian 2 U := by
  have hp (x : U) : x ^ 2 = 1 := by
    apply Subtype.ext
    by_contra h
    exact not_square_of_weakly_closed_of_normalizer_not_le H U z hweak hsquares hmove
      (hroot x x.property h)
  have hi (x : U) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp x)
  exact {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hi _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hi, hi])
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

end Subgroup

namespace Sylow

open Subgroup
open scoped Pointwise

/-- If conjugates of a central involution which are squares in the Sylow
subgroup equal that involution, a conjugate centralizing a square root of
it also equals it. Transport the root into the original Sylow inside the
centralizer of the central involution. -/
public theorem eq_of_isConj_of_commuting_square_root_of_weakly_closed_squares
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z t x : S) (hzC : z ∈ center S) (hz : z ^ 2 = 1)
    (hweak : ∀ v : S, IsConj (z : G) ((v ^ 2 : S) : G) → v ^ 2 = z)
    (hconj : IsConj (z : G) (t : G)) (hx : x ^ 2 = z) (hxt : Commute x t) :
    t = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  let H : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩))
  let y : H := ⟨f (x : G), mem_centralizer_singleton_iff.mpr (by
    have hh := (hxt.map ((f : G →* G).comp (S : Subgroup G).subtype)).eq
    change f (x : G) * f (t : G) = f (t : G) * f (x : G) at hh
    rwa [hft] at hh)⟩
  have hy4 : y ^ 4 = 1 := by
    apply Subtype.ext
    change f (x : G) ^ 4 = 1
    rw [← map_pow]
    have hx4 : x ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hx, hz]
    simpa using congrArg f (congrArg Subtype.val hx4)
  have hp : IsPGroup 2 (zpowers y) := by
    apply isPGroup_iff_orderOf_dvd_pow.mpr
    intro b
    refine ⟨2, ?_⟩
    rw [← orderOf_coe b]
    exact (orderOf_dvd_of_mem_zpowers b.property).trans
      (orderOf_dvd_of_pow_eq_one hy4)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have hyS : (MulAut.conj k) y ∈ S.subtype hSH := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (T : Set H)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let v : S := ⟨((MulAut.conj k) y : H), hyS⟩
  let a : G := (k : G) * g
  let q : G ≃* G := MulAut.conj a
  have hqt : q (t : G) = z := by
    change (k : G) * g * (t : G) * ((k : G) * g)⁻¹ = z
    have hfix : (MulAut.conj (k : G)) (z : G) = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
    calc
      _ = (MulAut.conj (k : G)) (f (t : G)) := by simp [f, mul_assoc]
      _ = z := by rw [hft]; exact hfix
  have hqz : q (z : G) = ((v ^ 2 : S) : G) := by
    rw [← hx, Subgroup.coe_pow, Subgroup.coe_pow, map_pow]
    congr 1
    simp [q, a, v, y, f, mul_assoc]
  have hv : v ^ 2 = z := hweak v (isConj_iff.mpr ⟨a, hqz⟩)
  exact Subtype.ext (q.injective (hqt.trans
    (hqz.trans (congrArg Subtype.val hv)).symm))

end Sylow
