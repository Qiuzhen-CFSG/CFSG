module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Independent actions on two factors

An action transitive on the nonidentity elements of one factor and fixing
the other can be combined with the opposite action. The resulting group
is transitive on products with both coordinates nonidentity. Conjugation
transports the individual factor actions.

Used for the two center factors in Aschbacher–Smith 2.4.20(1), printed p.535.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]
open scoped Pointwise

/-- Two independent transitive factor actions are transitive off the coordinate axes. -/
theorem transitive_on_sup_complement_of_factor_actions
    (Z W A B H : Subgroup G) (hWZ : W ≤ centralizer (Z : Set G))
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hAW : A ≤ centralizer (W : Set G)) (hBZ : B ≤ centralizer (Z : Set G))
    (ha : ∀ z ∈ Z, z ≠ 1 → ∀ v ∈ Z, v ≠ 1 → ∃ a ∈ A, a*z*a⁻¹=v)
    (hb : ∀ w ∈ W, w ≠ 1 → ∀ v ∈ W, v ≠ 1 → ∃ b ∈ B, b*w*b⁻¹=v)
    (u v : G) (hu : u ∈ Z ⊔ W) (huZ : u ∉ Z) (huW : u ∉ W)
    (hv : v ∈ Z ⊔ W) (hvZ : v ∉ Z) (hvW : v ∉ W) :
    ∃ g ∈ H, g*u*g⁻¹=v := by
  have he : ((Z ⊔ W : Subgroup G) : Set G) = (Z : Set G)*(W : Set G) :=
    coe_mul_of_right_le_normalizer_left Z W (hWZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
  have hu' : u ∈ (Z : Set G)*(W : Set G) := by rw [← he]; exact hu
  have hv' : v ∈ (Z : Set G)*(W : Set G) := by rw [← he]; exact hv
  obtain ⟨z,hz,w,hw,rfl⟩ := hu'
  obtain ⟨z',hz',w',hw',rfl⟩ := hv'
  have hz1 : z ≠ 1 := by rintro rfl; exact huW (by simpa using hw)
  have hw1 : w ≠ 1 := by rintro rfl; exact huZ (by simpa using hz)
  have hz1' : z' ≠ 1 := by rintro rfl; exact hvW (by simpa using hw')
  have hw1' : w' ≠ 1 := by rintro rfl; exact hvZ (by simpa using hz')
  obtain ⟨a,haA,hea⟩ := ha z hz hz1 z' hz' hz1'
  obtain ⟨b,hbB,heb⟩ := hb w hw hw1 w' hw' hw1'
  have haw : a*w*a⁻¹=w := mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hAW haA)) w hw).symm
  have hbz : b*z'*b⁻¹=z' := mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hBZ hbB)) z' hz').symm
  refine ⟨b*a,H.mul_mem (hBH hbB) (hAH haA),?_⟩
  calc
    (b*a)*(z*w)*(b*a)⁻¹ = (b*(a*z*a⁻¹)*b⁻¹)*(b*(a*w*a⁻¹)*b⁻¹) := by group
    _ = z'*w' := by rw [hea,haw,hbz,heb]

theorem conjugate_factor_transitive
    (A Z : Subgroup G) (e : G ≃* G)
    (h : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ a ∈ A, a*z*a⁻¹=w) :
    ∀ z ∈ Z.map e.toMonoidHom, z ≠ 1 → ∀ w ∈ Z.map e.toMonoidHom, w ≠ 1 →
      ∃ a ∈ A.map e.toMonoidHom, a*z*a⁻¹=w := by
  rintro _ ⟨z,hz,rfl⟩ hz1 _ ⟨w,hw,rfl⟩ hw1
  obtain ⟨a,ha,he⟩ := h z hz (fun hz => hz1 (by simp only [hz,map_one]))
    w hw (fun hw => hw1 (by simp only [hw,map_one]))
  refine ⟨e a,mem_map_of_mem e.toMonoidHom ha,?_⟩
  simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using congrArg e he
end Subgroup
