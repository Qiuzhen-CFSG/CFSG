module

public import Theory.AlgebraicGroup.BNPair.Representatives

/-! The exchange axiom in selected-representative notation. -/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- The exchange axiom of a Tits system, expressed using any supplied
representatives of the two quotient classes. -/
public lemma exchange_of_representatives (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (ns nw : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w) :
    ({(ns : X)} : Set X) * (T.B : Set X) * ({(nw : X)} : Set X) ⊆
      ((T.B : Set X) * ({((ns * nw : T.N) : X)} : Set X) * (T.B : Set X)) ∪
        ((T.B : Set X) * ({(nw : X)} : Set X) * (T.B : Set X)) := by
  have hnsnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (ns * nw) = s * w := by
    rw [map_mul, hns, hnw]
  have hleft :
      ({(ns : X)} : Set X) * (T.B : Set X) * ({(nw : X)} : Set X) =
        representativeSet T.B T.N s * (T.B : Set X) *
          representativeSet T.B T.N w := by
    rw [← representativeSet_mul_B T.B T.N s ns hns, mul_assoc,
      ← B_mul_representativeSet T.B T.N w nw hnw, ← mul_assoc]
  rw [hleft]
  simpa only [B_mul_representativeSet T.B T.N (s * w) (ns * nw) hnsnw,
    B_mul_representativeSet T.B T.N w nw hnw] using T.exchange s hs w

end Theory.AlgebraicGroup.TitsSystem
