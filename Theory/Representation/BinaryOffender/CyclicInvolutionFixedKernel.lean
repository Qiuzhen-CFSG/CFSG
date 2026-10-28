module

public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The pointwise fixed-space kernel in a cyclic subgroup

In a faithful binary action, the kernel on an involution's fixed space
inside its centralizer is elementary abelian. A cyclic subgroup containing
that involution therefore has precisely its order-two subgroup as the
pointwise kernel. The argument preserves the original representation and
does not require a dimension bound.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A cyclic actor containing an involution has exactly that involution's
cyclic subgroup as the kernel on its fixed space. -/
theorem subspaceKernel_eq_zpowers_of_cyclic
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (C : Subgroup G) [IsCyclic C] (t : G) (htC : t ∈ C)
    (ht : t ^ 2 = 1) (htne : t ≠ 1) :
    subspaceKernel ρ (fixedSpace ρ (zpowers t)) C = zpowers t := by
  let : IsElementaryAbelian 2 (involutionFixedKernel ρ t) :=
    involutionFixedKernel_elementary ρ hf t ht
  have hC : C ≤ centralizer {t} := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg C.subtype (mul_comm (⟨g,hg⟩ : C) ⟨t,htC⟩)
  apply le_antisymm
  · intro g hg
    have hkernel : g ∈ involutionFixedKernel ρ t := ⟨hC hg.1,hg.2⟩
    have hg2 : g ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian g hkernel
    by_cases hg1 : g = 1
    · exact hg1 ▸ one_mem _
    · have hge : (⟨g,hg.1⟩ : C) = ⟨t,htC⟩ :=
        IsCyclic.eq_of_orderOf_eq_two
          (orderOf_eq_prime (Subtype.ext hg2)
            (fun he => hg1 (congrArg C.subtype he)))
          (orderOf_eq_prime (Subtype.ext ht)
            (fun he => htne (congrArg C.subtype he)))
      have he : g = t := congrArg C.subtype hge
      rw [he]
      exact mem_zpowers t
  · apply zpowers_le.mpr
    exact ⟨htC,fun v hv => (mem_fixedSpace_zpowers_iff ρ t v).mp hv⟩

end Representation.BinaryOffender
