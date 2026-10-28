module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The two-residual of the literal cyclic source actor

The marked odd prime-power kernel and generating involution have disjoint
orders, so the kernel has index two. The quotient is a two-group, whereas
every kernel element has odd order. These two inclusions identify the
literal kernel with the actor’s two-residual. This applies to the cyclic
D.2.17 endpoints and their marked uses in original 15.1.2.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem LocalGeneration.kernel_index_two (l : LocalGeneration ρ) : l.kernel.index = 2 := by
  let := l.normal
  have ht : Nat.card (zpowers l.involution) = 2 := by rw [Nat.card_zpowers,l.order_two]
  have hd : Disjoint l.kernel (zpowers l.involution) := IsPGroup.disjoint_of_coprime
    l.pgroup (IsPGroup.of_card (n := 1) (by simpa using ht)) l.prime_odd.coprime_two_right
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint l.kernel (zpowers l.involution)
    le_normalizer_of_normal hd
  rw [l.generated,card_top,ht] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (l.kernel.card_mul_index.trans hc)

theorem LocalGeneration.kernel_eq_twoResidual (l : LocalGeneration ρ) :
    l.kernel = pResidual 2 G := by
  let := l.normal
  apply le_antisymm
  · intro x hx
    apply mem_pResidual_of_orderOf_coprime
    have hc := l.pgroup.orderOf_coprime l.prime_odd.coprime_two_right (⟨x,hx⟩ : l.kernel)
    rw [← Subgroup.orderOf_coe] at hc
    exact hc.symm
  · apply (pResidual_le_iff_isPGroup_quotient 2 l.kernel).mpr
    apply IsPGroup.of_card (n := 1)
    rw [←Subgroup.index_eq_card,l.kernel_index_two]
    rfl

end CFSG.Quasithin.ChapterD.CyclicSource
