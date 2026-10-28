module
public import Theory.GroupTheory.ClassTwoCommutator
/-!
# A central orbit makes each commutator row generate the derived group

Suppose an actor fixes the derived group pointwise and acts transitively on
noncentral cosets modulo the center. Every row [x,P] is then the whole derived
group: transfer every generating commutator to the chosen row using the actor.
This is the row-surjectivity step in MS93 (3.10)(i), printed p.880.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.ClassTwo
variable {P A : Type*} [Group P] [Group A]

theorem commutator_eq_row_of_central_orbit
    (α : A →* MulAut P)
    (hfix : ∀ a : A, ∀ c ∈ _root_.commutator P, α a c = c)
    (x : P)
    (horbit : ∀ y : P, y ∉ center P →
      ∃ a : A, (α a x)⁻¹ * y ∈ center P) :
    _root_.commutator P = ⁅zpowers x, (⊤ : Subgroup P)⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro y _ t _
    by_cases hy : y ∈ center P
    · have hc : ⁅y,t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_center_iff.mp hy t).symm)
      rw [hc]
      exact one_mem _
    obtain ⟨a,ha⟩ := horbit y hy
    have hc : y = α a x * ((α a x)⁻¹ * y) := by group
    have he : ⁅y,t⁆ = ⁅α a x,t⁆ := by
      have hcomm : ⁅(α a x)⁻¹ * y,t⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp ha t).symm)
      calc
        _ = ⁅α a x * ((α a x)⁻¹ * y),t⁆ := congrArg (fun z => ⁅z,t⁆) hc
        _ = ⁅α a x,t⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul,hcomm]
          simp
    have hmap : ⁅α a x,t⁆ = ⁅x,(α a).symm t⁆ := by
      have hm := map_commutatorElement (α a) x ((α a).symm t)
      rw [(α a).apply_symm_apply] at hm
      rw [←hm]
      exact hfix a _ (commutator_mem_commutator (mem_top _) (mem_top _))
    rw [he,hmap]
    exact commutator_mem_commutator (mem_zpowers x) (mem_top _)
  · exact commutator_mono le_top le_top

end Subgroup.ClassTwo
