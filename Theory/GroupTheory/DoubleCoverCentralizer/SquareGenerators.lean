module

public import Theory.GroupTheory.DoubleCoverCentralizer.PerfectSquareOrbit
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Elementary images from generators with a common square

A central extension with kernel of exponent two has an elementary abelian
image when the chosen generating lifts and their pairwise products become
involutions. The kernel is central, so adjoining its image preserves this
property. This is applied to the four square-root generators of the first
Hall--Janko radical in Aschbacher--Smith I.2.2(5), printed pp.411--412.
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {E B Q ι : Type*} [Group E] [Group B] [Group Q]

/-- Two involutions whose product has square one commute. -/
theorem commute_of_three_squares {x y : Q}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy)
  have hxyi : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hxy)
  exact (by simpa only [mul_inv_rev, hxi, hyi] using hxyi.symm : x * y = y * x)

/-- The literal image of the inverse image of the generated subgroup is
an elementary abelian two-group. -/
theorem elementary_image_of_square_generators (f : E →* B) (q : E →* Q)
    (hc : f.ker ≤ center E) (h2 : ∀ z ∈ f.ker, z ^ 2 = 1)
    (a : ι → E) (ha : ∀ i, q (a i) ^ 2 = 1)
    (hab : ∀ i j, (q (a i) * q (a j)) ^ 2 = 1) :
    IsElementaryAbelian 2
      (((closure (Set.range (fun i => f (a i)))).comap f).map q) := by
  let s : Set Q := Set.range (fun i => q (a i)) ∪ (f.ker.map q : Set Q)
  have hscomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨x, hx, rfl⟩) y (⟨j, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact commute_of_three_squares (ha i) (ha j) (hab i j)
    · simpa only [map_mul] using congrArg q (mem_center_iff.mp (hc hy) (a i))
    · simpa only [map_mul] using congrArg q (mem_center_iff.mp (hc hx) (a j)).symm
    · simpa only [map_mul] using congrArg q (mem_center_iff.mp (hc hy) x)
  let : IsMulCommutative (closure s) := isMulCommutative_closure hscomm
  have hse : IsElementaryAbelian 2 (closure s) :=
    IsElementaryAbelian.closure_of_isMulCommutative s (by
      rintro x (⟨i, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ha i
      · rw [← map_pow, h2 z hz, map_one])
  have hmap : (closure (Set.range a)).map f =
      closure (Set.range (fun i => f (a i))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have he : ((closure (Set.range (fun i => f (a i)))).comap f).map q =
      closure s := by
    change ((closure (Set.range (fun i => f (a i)))).comap f).map q =
      closure (Set.range (fun i => q (a i)) ∪ (f.ker.map q : Set Q))
    rw [← hmap, comap_map_eq, Subgroup.map_sup, MonoidHom.map_closure,
      ← Set.range_comp, Subgroup.closure_union, Subgroup.closure_eq]
    rfl
  rw [he]
  exact hse

end PerfectCentralCovering
