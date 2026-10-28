module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
/-!
# Perfectness from coprime triangle relations

If two generators have orders dividing m and n, their product has order
dividing k, and gcd(m,n) = gcd(m*n,k) = 1, every abelian image is trivial.
Thus the subgroup they generate is perfect. This elementary triangle-group
argument is used for the (3,5,7) pair in the Held involution centralizer.
-/

public section
namespace Group
private theorem triangle_abelian_trivial {A : Type*} [CommGroup A]
    (x y : A) {m n k : ℕ} (hmn : m.Coprime n) (hmnk : (m * n).Coprime k)
    (hx : x ^ m = 1) (hy : y ^ n = 1) (hxy : (x * y) ^ k = 1) :
    x = 1 ∧ y = 1 := by
  have hmn' : (x * y) ^ (m * n) = 1 := by
    rw [mul_pow, pow_mul, hx, one_pow, one_mul,
      Nat.mul_comm m n, pow_mul, hy, one_pow]
  have hprod : x * y = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    simpa only [hmnk.gcd_eq_one] using
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hmn') (orderOf_dvd_of_pow_eq_one hxy)
  have hxn : x ^ n = 1 := by
    calc
      x ^ n = (x * y) ^ n := by rw [mul_pow, hy, mul_one]
      _ = 1 := by rw [hprod, one_pow]
  have hx1 : x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    simpa only [hmn.gcd_eq_one] using
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hxn)
  exact ⟨hx1, by simpa only [hx1, one_mul] using hprod⟩

/-- Coprime triangle relations force the generated subgroup to be perfect. -/
theorem isPerfect_closure_pair_of_coprime_triangle {G : Type*} [Group G]
    (x y : G) {m n k : ℕ} (hmn : m.Coprime n) (hmnk : (m * n).Coprime k)
    (hx : x ^ m = 1) (hy : y ^ n = 1) (hxy : (x * y) ^ k = 1) :
    IsPerfect (Subgroup.closure ({x, y} : Set G)) := by
  let K := Subgroup.closure ({x, y} : Set G)
  let xK : K := ⟨x, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let yK : K := ⟨y, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hgen : Subgroup.closure ({xK, yK} : Set K) = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    change K = (⊤ : Subgroup K).map K.subtype
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hp := triangle_abelian_trivial (Abelianization.of xK) (Abelianization.of yK)
    hmn hmnk
    (by rw [← map_pow]; exact congrArg Abelianization.of (Subtype.ext hx))
    (by rw [← map_pow]; exact congrArg Abelianization.of (Subtype.ext hy))
    (by rw [← map_mul, ← map_pow]; exact congrArg Abelianization.of (Subtype.ext hxy))
  refine ⟨top_unique ?_⟩
  rw [← Abelianization.ker_of, ← hgen, Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact hp.1
  · exact (Set.mem_singleton_iff.mp hz) ▸ hp.2
end Group
