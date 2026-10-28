module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Squaring in a central extension of the binary dual natural module

The kernel is marked as the natural three-space and the quotient as its dual.
Both markings refer to the same surjective matrix-group projection and the
same automorphism action on the group. Squaring is constant on quotient
fibers because the kernel is central and elementary. Its resulting function
on the dual space is equivariant, so the stabilizer calculation in `Linear`
makes it zero. Thus the whole extension has square one and is commutative.

This supplies the square-map calculation used on pure dual factors in the
binary branch of MS93 (1993), (4.6.11)--(4.6.12), printed pp.909--912. It
does not assume or construct a dual quotient for an arbitrary MS93 core.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Linear Subgroup
variable {G A : Type*} [Group G] [Group A]

structure DualExtension (q : G →* Multiplicative W) where
  onto : Function.Surjective q
  central : q.ker ≤ center G
  coordinates : q.ker ≃* Multiplicative W
  projection : A →* S
  projection_onto : Function.Surjective projection
  action : A →* MulAut G
  quotient_action : ∀ a x, (q (action a x)).toAdd = dual (projection a) (q x).toAdd
  kernel_action : ∀ a (x y : q.ker), (y : G) = action a x →
    (coordinates y).toAdd = (projection a).val.mulVec (coordinates x).toAdd

namespace DualExtension
variable {q : G →* Multiplicative W} (d : DualExtension (A := A) q)

include d

theorem kernel_square (x : q.ker) : x ^ 2 = 1 := by
  apply d.coordinates.injective
  rw [map_pow, map_one, pow_two]
  change Multiplicative.ofAdd ((d.coordinates x).toAdd +
    (d.coordinates x).toAdd) = Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

omit d in
theorem square_mem (q : G →* Multiplicative W) (x : G) : x ^ 2 ∈ q.ker := by
  change q (x ^ 2) = 1
  rw [map_pow, pow_two]
  change Multiplicative.ofAdd ((q x).toAdd + (q x).toAdd) = Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

theorem square_eq_of_image_eq {x y : G} (h : q x = q y) : x ^ 2 = y ^ 2 := by
  let c := x * y⁻¹
  have hc : c ∈ q.ker := by
    change q (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := congrArg Subtype.val (d.kernel_square ⟨c, hc⟩)
  have hcomm : Commute c y := (mem_center_iff.mp (d.central hc) y).symm
  have he : x = c * y := by simp [c]
  calc
    x ^ 2 = (c * y) ^ 2 := congrArg (fun z : G => z ^ 2) he
    _ = c ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hc2, one_mul]

noncomputable def squareMap (v : W) : W :=
  (d.coordinates ⟨(Classical.choose (d.onto (Multiplicative.ofAdd v))) ^ 2,
    square_mem q _⟩).toAdd

theorem squareMap_image (x : G) : d.squareMap (q x).toAdd =
    (d.coordinates ⟨x ^ 2, square_mem q x⟩).toAdd := by
  unfold squareMap
  congr 2
  apply Subtype.ext
  apply d.square_eq_of_image_eq
  exact Classical.choose_spec (d.onto (Multiplicative.ofAdd (q x).toAdd))

theorem squareMap_equivariant (g : S) (v : W) :
    d.squareMap (dual g v) = g.val.mulVec (d.squareMap v) := by
  obtain ⟨a, rfl⟩ := d.projection_onto g
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (q x).toAdd = v := congrArg Multiplicative.toAdd hx
  rw [← hv, ← d.quotient_action, d.squareMap_image, d.squareMap_image]
  apply d.kernel_action
  exact (map_pow (d.action a) x 2).symm

theorem square_eq_one (x : G) : x ^ 2 = 1 := by
  have hz := equivariantDualMap_zero d.squareMap d.squareMap_equivariant (q x).toAdd
  rw [d.squareMap_image] at hz
  have he : d.coordinates ⟨x ^ 2, square_mem q x⟩ = 1 := congrArg Multiplicative.ofAdd hz
  have hx := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
  exact congrArg Subtype.val hx

theorem commutative (x y : G) : x * y = y * x := by
  have hinv (z : G) : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using d.square_eq_one z)
  calc
    x * y = (x * y)⁻¹ := (hinv (x * y)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hinv, hinv]

end DualExtension
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
