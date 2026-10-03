module
public import Stellmacher.LaterDefs

/-!
# The conclusion and alternatives of Stellmacher (8.6)

The common conclusion records the prescribed predecessor, the opposite-core
intersection D, the local conjugate closure L with two-core Q, and the selected
Sylow three-subgroup T. It includes [D,L] = Z_a and elementary-abelian
structure for D and Q/D. The three alternatives give the small-index case A,
the wreath-product case B with its nonsolvable normalizer, and case C with
its extraspecial core and L3(2) normalizer quotient.

These are the unchanged public conclusion types used by the numbered theorem
and its proved branch modules. They are separated from the proof so branch
results can be checked independently while preserving all public names and
re-exports. Source: Stellmacher, Journal of Algebra 190 (1997), (8.6),
printed p.41; refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
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
      (_ : QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep)
        SL2TwoWreathC2)
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

end Stellmacher.SectionEight
