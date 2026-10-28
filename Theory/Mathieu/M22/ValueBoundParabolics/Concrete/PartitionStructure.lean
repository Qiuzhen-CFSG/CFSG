module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.Actions
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.FiniteOrders

/-!
# The M₂₂ partition quotients and common Sylow subgroups

Restriction to the genuine hexad gives partition stabilizers of orders 384
and 768 in M₂₂ and its full design automorphism group. Their actions on the
three pairs are surjective onto S₃, with kernels of orders 64 and 128. The
kernels are therefore exactly the intrinsic two-cores.

The intersections with the marked-pair stabilizers have orders 128 and 256,
respectively, hence are ambient Sylow two-subgroups. This proves the four
partition-geometry inputs for Aschbacher–Smith E.4.3(2), printed pp. 241–242.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup
namespace PartitionStructure
theorem second_card : Nat.card second = 384 := by
  have h := card_comap_of_le_range (m22SetAction m22Hexad123) smallGroup
    (by rw [restriction_range]; exact inf_le_right)
  rw [second_preimage,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe second_le_hexad).toEquiv,
    m22HexadKernel_card m22Hexad123_mem, smallGroup_card] at h
  exact h

theorem intersection_card : Nat.card (first ⊓ second : Subgroup M22) = 128 := by
  have h := card_comap_of_le_range (m22SetAction m22Hexad123) smallMarked
    (by rw [restriction_range]; exact inf_le_left.trans inf_le_right)
  rw [intersection_preimage,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right.trans second_le_hexad)).toEquiv,
    m22HexadKernel_card m22Hexad123_mem, smallMarked_card] at h
  exact h

theorem outerSecond_card : Nat.card outerSecond = 768 := by
  have h := outer_card_double outerSecond oddElement_mem.2
  rw [comap_outerSecond, second_card] at h
  exact h

theorem outerIntersection_card :
    Nat.card (outerFirst ⊓ outerSecond : Subgroup m22DesignAut) = 256 := by
  have h := outer_card_double (outerFirst ⊓ outerSecond) oddElement_mem
  rw [Subgroup.comap_inf, comap_outerFirst, comap_outerSecond, intersection_card] at h
  exact h

noncomputable def quotientThree {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm hexadPartition) (hf : Function.Surjective f)
    (n : ℕ) (hc : Nat.card G = 2 ^ n * 6) :
    (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3) := by
  let e : hexadPartition ≃ Fin 3 := Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using hexadPartition_card)
  let f' : G →* Equiv.Perm (Fin 3) := e.permCongrHom.toMonoidHom.comp f
  have hs : Function.Surjective f' := e.permCongrHom.surjective.comp hf
  have hk : Nat.card f'.ker = 2 ^ n := by
    have h := f'.ker.card_mul_index
    rw [Subgroup.index_ker, f'.range_eq_top_of_surjective hs, Subgroup.card_top, hc] at h
    have hp : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hp] at h
    omega
  have he := ker_eq_twoCore_of_surjective_perm_three f' hs (IsPGroup.of_card hk)
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f' hs)

end PartitionStructure
open PartitionStructure

/-- The genuine three-pair action identifies the inner partition quotient. -/
noncomputable def secondQuotientEquiv :
    (second ⧸ pCore 2 second) ≃* Equiv.Perm (Fin 3) :=
  quotientThree innerPairAction innerPairAction_surjective 6 second_card

/-- The same three-pair action identifies the outer partition quotient. -/
noncomputable def outerSecondQuotientEquiv :
    (outerSecond ⧸ pCore 2 outerSecond) ≃* Equiv.Perm (Fin 3) :=
  quotientThree outerPairAction outerPairAction_surjective 7 outerSecond_card

/-- The two inner stabilizers have a common ambient Sylow two-subgroup. -/
theorem exists_sylow_le_first_inf_second :
    ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ first ⊓ second := by
  have h : Nat.card (first ⊓ second : Subgroup M22) =
      2 ^ (Nat.card M22).factorization 2 := by
    rw [intersection_card, m22_order]
    decide +kernel
  exact ⟨Sylow.ofCard (first ⊓ second) h, le_rfl⟩

/-- The two full design stabilizers have a common ambient Sylow two-subgroup. -/
theorem exists_sylow_le_outerFirst_inf_outerSecond :
    ∃ U : Sylow 2 m22DesignAut, (U : Subgroup m22DesignAut) ≤ outerFirst ⊓ outerSecond := by
  have h : Nat.card (outerFirst ⊓ outerSecond : Subgroup m22DesignAut) =
      2 ^ (Nat.card m22DesignAut).factorization 2 := by
    rw [outerIntersection_card, m22DesignAut_order]
    decide +kernel
  exact ⟨Sylow.ofCard (outerFirst ⊓ outerSecond) h, le_rfl⟩

end Sporadic.Mathieu.M22ValueBound.Concrete
