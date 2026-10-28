module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverUnitary

/-!
# Outer actors on the remaining central cubic covers

The order-nine implementer of an inner outside cubic has centralizer of
three-rank at most one. In either special linear or special unitary degree
three, its nonidentity central cube instead supplies a fixed torus of
three-rank two. Thus the original outside cubic acts outer on the actual
cover, including its center of order three.

The noncubic exceptional field rows and the outer-cover diagonal analysis
remain explicit obligations. The ordinary-root application uses the same
Cartan element and literal two-core quotient.
Source: Aschbacher–Smith A.3.18, printed pp.52–53, and 4.3.6, p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The central cubic cover with its actual outer conjugation action. -/
def OuterCubicCoverActor {S : Type*} [Group S] (L : Subgroup S) (x : S) : Prop :=
  Nat.card (center L) = 3 ∧
    ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧ IsSLSign L unitary 3 q ∧
      ∃ α : MulAut L, (∀ l : L, (α l).val = x * l.val * x⁻¹) ∧
        α ∉ MulAut.innerSubgroup L

variable {H : Type*} [Group H] [Finite H]

/-- Every outside cubic on a classical central three-cover acts outer under
SQTK. The special unitary case retains the original quadratic field. -/
theorem cubic_cover_actor_outer
    (hH : IsSQTK KnownSimple.IsKnownSimple H) {K : Subgroup H} [K.Normal]
    (hz : Nat.card (center K) = 3) (hr : 1 < primeRank 3 K)
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q) (hm : IsSLSign K unitary 3 q)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) : OuterCubicCoverActor K a := by
  refine ⟨hz, unitary, q, hq, hm, MulAut.conjNormal a, fun _ => rfl, ?_⟩
  have hb := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  cases unitary with
  | false =>
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    exact CoverInner.not_inner_of_linear_cover K hz hr hb e a ha haK
  | true =>
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
    exact CoverInner.not_inner_of_unitary_cover K hz hr hb J q hq hcard hconj e a ha haK

/-- Only exceptional noncubic field actors and outer actors on actual
central cubic covers remain in the source classification. -/
def OuterCoverRemainder (p : ℕ) (K : Subgroup H) (a : H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    ExceptionalFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ OuterCubicCoverActor (twoCoreComponent K) (QuotientGroup.mk' (pCore 2 H) a))

/-- Apply both fixed-torus exclusions to the original split-prime domain,
keeping the outside element in the literal ambient two-core quotient. -/
theorem alternatives_or_outer_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ OuterCoverRemainder p K a := by
  rcases alternatives_or_exceptional_or_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with hex | ⟨rfl, hz, u, q, hq, hm⟩
  · exact Or.inr (Or.inl hex)
  let : (twoCoreComponent K).Normal := twoCore_normal K
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact Or.inr (Or.inr ⟨rfl, cubic_cover_actor_outer (twoCore_sqtk hH) hz hr' u q hq hm
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2⟩)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
