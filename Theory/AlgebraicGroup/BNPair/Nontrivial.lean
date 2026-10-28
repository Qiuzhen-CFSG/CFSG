module

public import Theory.AlgebraicGroup.BNPair.Representatives

/-! The nontriviality axiom in selected-representative notation. -/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- The nontriviality axiom of a Tits system, expressed using any supplied
representative of the distinguished quotient class. -/
public lemma nontrivial_of_representative (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) (ns : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s) :
    ({(ns : X)} : Set X) * (T.B : Set X) * ({(ns : X)} : Set X) ≠
      (T.B : Set X) := by
  intro h
  apply T.nontrivial s hs
  calc
    representativeSet T.B T.N s * (T.B : Set X) * representativeSet T.B T.N s =
        ({(ns : X)} : Set X) * (T.B : Set X) * ({(ns : X)} : Set X) := by
      rw [mul_assoc, B_mul_representativeSet T.B T.N s ns hns, ← mul_assoc,
        representativeSet_mul_B T.B T.N s ns hns]
    _ = (T.B : Set X) := h

end Theory.AlgebraicGroup.TitsSystem
