module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.MarkedCore
public import Theory.GroupTheory.CentralQuotientPGroupCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
/-!
# The reduced closure action in the wreath centralizer

The common-centralizer theorem 13.9.7 and the literal central line show that
the marked-point centralizer in C_G(z)/⟨z⟩ is a two-group. Consequently the
centralizer of its reduced normal closure is exactly the two-core. This
identifies the kernel of the actual conjugation action used in 13.9.8.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G}
namespace PairData
variable (m : PairData d)

/-- The original marked point in the actual central-involution quotient. -/
noncomputable def tTilde : m.Tilde :=
  QuotientGroup.mk' (m.Z.subgroupOf m.C) ⟨m.t,m.t_mem_C⟩

theorem tTilde_mem_closure : m.tTilde ∈ m.tilde m.U := by
  refine ⟨⟨m.t,m.t_mem_C⟩,?_,rfl⟩
  exact le_conjugateSpanBy _ _ ((show zpowers m.t ≤ m.V from le_sup_left) (mem_zpowers m.t))

/-- The source common-centralizer theorem implies a two-group point
centralizer after quotienting by the literal central involution line. -/
theorem tilde_point_centralizer_isPGroup (hE : IsEvenCharacteristicAt d.T) :
    IsPGroup 2 (centralizer ({m.tTilde} : Set m.Tilde)) := by
  let N := m.Z.subgroupOf m.C
  let t : m.C := ⟨m.t,m.t_mem_C⟩
  have hN : N ≤ center m.C := by
    intro v hv
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hZx : m.Z ≤ centralizer ({(x : G)} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp x.property).symm)
    exact (mem_centralizer_singleton_iff.mp (hZx hv)).symm
  have hNp : IsPGroup 2 N := by
    have hZ : IsPGroup 2 m.Z := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,m.z_order,pow_one])
    exact hZ.comap_subtype
  have hD : IsPGroup 2 m.D := by
    rw [m.source13_9_7 hE]
    exact d.T.isPGroup'.to_le (thompson_le_T (d := d))
  have he : centralizer ({t} : Set m.C) = m.D.subgroupOf m.C := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change x*t=t*x ↔ (x : G) ∈ m.C ∧ (x : G) ∈ centralizer ({m.t} : Set G)
    constructor
    · intro hx
      exact ⟨x.property,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx)⟩
    · intro hx
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
  apply isPGroup_centralizer_quotient_of_central_kernel N hN hNp t
  rw [he]
  exact hD.comap_subtype

/-- The reduced closure centralizer is a two-group, since it fixes the
original marked point. -/
theorem tilde_closure_centralizer_isPGroup (hE : IsEvenCharacteristicAt d.T) :
    IsPGroup 2 (centralizer (m.tilde m.U : Set m.Tilde)) :=
  (m.tilde_point_centralizer_isPGroup hE).to_le
    (centralizer_le (Set.singleton_subset_iff.mpr m.tTilde_mem_closure))

/-- The first kernel identity of 13.9.8: the literal reduced-closure
centralizer is exactly the two-core of the centralizer quotient. -/
theorem tilde_closure_centralizer_eq_pCore (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T) :
    centralizer (m.tilde m.U : Set m.Tilde) = pCore 2 m.Tilde := by
  have hr := m.closure_reduced h hE
  let := hr.normal
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,m.tilde_closure_centralizer_isPGroup hE⟩
  · exact le_centralizer_iff.mp hr.le_centralizer_pCore

/-- The actual conjugation action has precisely the source two-core kernel. -/
theorem tilde_closure_action_ker (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T) :
    letI : (m.tilde m.U).Normal := (m.closure_reduced h hE).normal
    (MulAut.conjNormal : m.Tilde →* MulAut (m.tilde m.U)).ker = pCore 2 m.Tilde := by
  let := (m.closure_reduced h hE).normal
  rw [MulAut.conjNormal_ker_eq_centralizer,m.tilde_closure_centralizer_eq_pCore h hE]

end PairData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
