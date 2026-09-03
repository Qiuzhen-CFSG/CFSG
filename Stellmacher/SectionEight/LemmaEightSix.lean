module

public import Stellmacher.LaterDefs


open scoped BigOperators Pointwise

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

public inductive LemmaEightSixAlternative
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (aPrev : ctx.Γ.Vertex) (D L Q T : Subgroup H) : Prop
  | a
      (_ : 2 ^ 5 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 6)
      (_ : ∀ d : ctx.Γ.Vertex,
        QuotientIsModel (GAt ctx.Γ d) (QAt ctx.Γ d) SL2Two)
      (_ : Q = QAt ctx.Γ ctx.criticalPath.a)
      (_ : IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4))
      (_ : ∃ t : H,
        (t = 1 ∨ IsInvertingOn t (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a))) ∧
        Q = GeneratedWith (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) t)
      (_ : (IsCentralProductModel
          (QAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8 ∨
        IsCentralProductQ8Q8 (QAt ctx.Γ ctx.criticalPath.firstStep)) ∧
        IsModel
          (QAt ctx.Γ ctx.criticalPath.firstStep ⊓
            EAt ctx.Γ ctx.criticalPath.firstStep) Q8)
  | b
      (_ : 2 ^ 8 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 10)
      (_ : QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
      (_ : QuotientIsSemidirectModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep)
        SL2Two C2)
      (_ : QuotientOrderLe Q (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) 4 ∧
        IsSpecialTwo (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) ∧
        Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) = 2 ^ 6 ∧
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ⊓
          Subgroup.centralizer (T : Set H) = ⊥)
      (_ : IsCentralProductQ8Q8 (VAt ctx.Γ ctx.criticalPath.firstStep) ∧
        FrattiniAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) =
          ZAt ctx.Γ ctx.criticalPath.firstStep)
      (_ : ∃ W : Subgroup H,
        W ≤ L ∧ (W.subgroupOf L).Normal ∧
        IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 2 ^ 4 ∧
        IsNonsolvableNormalizer W)
  | c
      (_ : 2 ^ 14 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 15)
      (_ : QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
      (_ : QuotientElementaryAbelian
        (EAt ctx.Γ ctx.criticalPath.firstStep)
        (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) 3 4)
      (_ : QuotientCardEq Q D (2 ^ 6) ∧ Nat.card D = 2 ^ 5 ∧
        Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 ∧
        IsInternalDirectProductTwo D
          (Q ⊓ Subgroup.centralizer (T : Set H))
          (ZAt ctx.Γ ctx.criticalPath.a))
      (_ : IsExtraspecial 2 (↥(QAt ctx.Γ ctx.criticalPath.firstStep)) ∧
        Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 9 ∧
        QuotientElementaryAbelian Q
          (Q ⊓ QAt ctx.Γ ctx.criticalPath.firstStep) 2 3)
      (_ : QuotientQInvariantOrderThreeFixedPointFree
        (EAt ctx.Γ ctx.criticalPath.firstStep)
        (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))
        Q (ZAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep))
      (_ : QuotientInvolutionCentralizes Q
        (QAt ctx.Γ ctx.criticalPath.firstStep))
      (_ : ∃ lam : ctx.Γ.Vertex,
        lam ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
        lam ≠ ctx.criticalPath.a ∧
        QuotientIsModel
          (Subgroup.normalizer
            ((ZAt ctx.Γ lam ⊔ ZAt ctx.Γ ctx.criticalPath.a : Subgroup H) : Set H))
          (Subgroup.centralizer
            ((ZAt ctx.Γ lam ⊔ ZAt ctx.Γ ctx.criticalPath.a : Subgroup H) : Set H))
          L3Two)

public structure LemmaEightSixConclusion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (aPrev : ctx.Γ.Vertex) (D L Q T : Subgroup H) : Prop where
  previous_vertex : aPrev ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
    aPrev ≠ ctx.criticalPath.firstStep
  definitions :
    D = QAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
    L = conjugateClosure (QAt ctx.Γ aPrev) (GAt ctx.Γ ctx.criticalPath.a) ∧
    Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)
  base : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
    QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D
  alternative : LemmaEightSixAlternative ctx aPrev D L Q T

/-- **Stellmacher (8.6).**  Under the hypothesis of (8.2), choose
`a−1 ∈ D(a)\{a+1}`, `D`, `L`, `Q`, and a Sylow 3-subgroup `T` as in the
paper.  Then the displayed commutator, elementary-abelian, and three-case
classification conclusions hold. -/
public theorem lemma_eight_six
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (aPrev : ctx.Γ.Vertex) (D L Q T : Subgroup H)
    (hprev : aPrev ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      aPrev ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ aPrev)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    LemmaEightSixConclusion ctx aPrev D L Q T := by
  sorry

end Stellmacher.SectionEight
