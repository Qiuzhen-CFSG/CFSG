module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# The kernel on two subgroup sections

The automorphisms fixing a subgroup N pointwise and each coset modulo N
form a subgroup. If N is abelian, these automorphisms commute: each fixes
the other's displacement, so their products differ only by the order of
two elements of N. Neither characteristicity nor a chosen complement is
required.

Source application: the unipotent action kernel in Aschbacher–Smith
C.1.35, printed p.138; see NonblockMSLiftAction for the original lift.
-/

@[expose] public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Automorphisms fixing N pointwise and each coset modulo N. -/
def sectionKernel (N : Subgroup G) : Subgroup (MulAut G) where
  carrier := {a | (∀ x, a x * x⁻¹ ∈ N) ∧ ∀ x ∈ N, a x = x}
  one_mem' := ⟨fun x => by simp,fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    refine ⟨fun x => ?_,fun x hx => ?_⟩
    · have he : (a*b) x * x⁻¹ = (b x * x⁻¹) * (a x * x⁻¹) := by
        have hh := ha' _ (hb x)
        rw [map_mul,map_inv] at hh
        change a (b x) * x⁻¹ = _
        rw [←hh]
        group
      rw [he]
      exact N.mul_mem (hb x) (ha x)
    · change a (b x) = x
      rw [hb' x hx,ha' x hx]
  inv_mem' := by
    rintro a ⟨ha,ha'⟩
    refine ⟨fun x => ?_,fun x hx => ?_⟩
    · have hh := N.inv_mem (ha (a⁻¹ x))
      simpa using hh
    · exact a.injective (by simpa using (ha' x hx).symm)

theorem mem_sectionKernel_iff (N : Subgroup G) (a : MulAut G) :
    a ∈ sectionKernel N ↔ (∀ x, a x * x⁻¹ ∈ N) ∧ ∀ x ∈ N, a x = x := Iff.rfl

/-- The section kernel is abelian whenever its fixed subgroup is abelian. -/
theorem sectionKernel_commutative (N : Subgroup G) [IsMulCommutative N] :
    IsMulCommutative (sectionKernel N) := by
  refine ⟨⟨?_⟩⟩
  intro a b
  apply Subtype.ext
  ext x
  have ha := a.property.2 _ (b.property.1 x)
  have hb := b.property.2 _ (a.property.1 x)
  rw [map_mul,map_inv] at ha hb
  have hc := congrArg Subtype.val (mul_comm
    (⟨a.val x*x⁻¹,a.property.1 x⟩ : N) (⟨b.val x*x⁻¹,b.property.1 x⟩ : N))
  change (a.val x*x⁻¹)*(b.val x*x⁻¹) = (b.val x*x⁻¹)*(a.val x*x⁻¹) at hc
  change a.val (b.val x) = b.val (a.val x)
  calc
    a.val (b.val x) = (b.val x*x⁻¹)*(a.val x*x⁻¹)*x := by rw [←ha]; group
    _ = (a.val x*x⁻¹)*(b.val x*x⁻¹)*x := by rw [hc]
    _ = b.val (a.val x) := by rw [←hb]; group

end Subgroup
