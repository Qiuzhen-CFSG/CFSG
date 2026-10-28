module

public import Theory.AlgebraicGroup.BNPair.Defs

/-! Representatives of the distinguished involutions in a Tits system. -/

namespace Theory.AlgebraicGroup.TitsSystem

variable {X : Type*} [Group X]

/-- A representative of a distinguished quotient involution does not belong
to `B`. -/
public lemma representative_not_mem_B (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) (ns : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s) :
    (ns : X) ∉ T.B := by
  intro hB
  have hH : ns ∈ (T.B ⊓ T.N).subgroupOf T.N := by
    change (ns : X) ∈ T.B ⊓ T.N
    exact ⟨hB, ns.property⟩
  have hmk : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = 1 :=
    (QuotientGroup.eq_one_iff ns).2 hH
  exact (T.involutions s hs).1 (hns.symm.trans hmk)

/-- The square of a representative of a distinguished quotient involution
lies in `B ∩ N`. -/
public lemma representative_sq_mem_intersection (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) (ns : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s) :
    ns ^ 2 ∈ (T.B ⊓ T.N).subgroupOf T.N := by
  apply (QuotientGroup.eq_one_iff (ns ^ 2)).1
  change QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (ns ^ 2) = 1
  rw [map_pow, hns, (T.involutions s hs).2]

end Theory.AlgebraicGroup.TitsSystem
