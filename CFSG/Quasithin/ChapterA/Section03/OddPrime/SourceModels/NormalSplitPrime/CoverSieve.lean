module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitarySieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverLinear

/-!
# The actual actor on the remaining central cubic covers

An outside cubic acting inner on a component with center of order three
forces an order-nine implementer with nonidentity central cube. Its
centralizer has three-rank at most one. For an SL₃ cover the determinant
and eigenbasis calculation constructs a fixed elementary nine, excluding
that inner action. Thus a linear cover has an outer actor; a remaining
inner unitary actor retains its actual order-nine lift and central cube.

The exceptional field rows and the outer diagonal analysis remain explicit
source obligations. No projective quotient replaces a cubic cover.
Source: Aschbacher–Smith A.3.18, printed pp.52–53; the literal ordinary-root
application is 4.3.6, p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The remaining covering model with its literal outside action. Inner
linear actions have been excluded; inner unitary actions keep the order-nine
implementer and its nontrivial central cube as proved conclusions. -/
def CubicCoverActor {S : Type*} [Group S] (L : Subgroup S) (x : S) : Prop :=
  Nat.card (center L) = 3 ∧
    ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧ IsSLSign L unitary 3 q ∧
      ∃ α : MulAut L, (∀ l : L, (α l).val = x * l.val * x⁻¹) ∧
        (α ∉ MulAut.innerSubgroup L ∨ (unitary = true ∧
          ∃ y : L, MulAut.conj y = α ∧ orderOf y = 9 ∧ y^3 ∈ center L ∧
            y^3 ≠ 1 ∧ primeRank 3 (centralizer ({y} : Set L)) < 2))

variable {H : Type*} [Group H] [Finite H]

/-- The ordinary cubic cover conclusion, retaining the central covering group. -/
theorem cubic_cover_actor
    (hH : IsSQTK KnownSimple.IsKnownSimple H) {K : Subgroup H} [K.Normal]
    (hz : Nat.card (center K) = 3) (hr : 1 < primeRank 3 K)
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q) (hm : IsSLSign K unitary 3 q)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) : CubicCoverActor K a := by
  let α : MulAut K := MulAut.conjNormal a
  refine ⟨hz,unitary,q,hq,hm,α,fun _ => rfl,?_⟩
  by_cases hi : α ∈ MulAut.innerSubgroup K
  · right
    have hb := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
    have hu : unitary = true := by
      cases unitary with
      | true => rfl
      | false =>
        obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
        exact (CoverInner.not_inner_of_linear_cover K hz hr hb e a ha haK hi).elim
    exact ⟨hu,CoverInner.exists_nine_implementer K hz hr hb a ha haK hi⟩
  · exact Or.inl hi

/-- The exact exceptional field cases, or the actual cubic cover actor with
all linear inner actions excluded. -/
def CoverActionRemainder (p : ℕ) (K : Subgroup H) (a : H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    ExceptionalFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ CubicCoverActor (twoCoreComponent K) (QuotientGroup.mk' (pCore 2 H) a))

/-- Apply the covering actor calculation to the literal two-core image of
the original split extension, with its original outside order-p element. -/
theorem alternatives_or_cover_action
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ CoverActionRemainder p K a := by
  rcases alternatives_or_exceptional_or_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with hex | ⟨rfl,hz,u,q,hq,hm⟩
  · exact Or.inr (Or.inl hex)
  let : (twoCoreComponent K).Normal := twoCore_normal K
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact Or.inr (Or.inr ⟨rfl,cubic_cover_actor (twoCore_sqtk hH) hz hr' u q hq hm
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2⟩)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
