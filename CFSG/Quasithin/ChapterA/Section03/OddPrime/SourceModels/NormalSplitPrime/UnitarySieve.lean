module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.FieldSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.EvenUnitary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.NoncubicUnitary

/-!
# Removing all binary unitary actors from the split-prime remainder

The noncubic unitary fixed-subfield theorem absorbs the original outside
actor. At three, the mixed determinant obstruction and the explicit fixed
nine give the complete PGU₃ star-residual alternative. Thus the original
catalogue leaves only noncubic triality/Ree actors and genuine classical
cubic covers. The cover conclusion and both exceptional families remain
explicit proof obligations, not assumed classification results.

The ordinary-root leaf applies this reduction on its literal Cartan
extension. Source: Aschbacher–Smith A.3.18, pp.51–53, and 4.3.6, p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The exceptional noncubic field rows still requiring their fixed-subfield calculation. -/
def ExceptionalFieldModel (S : Type*) [Group S] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
    (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At S m)

variable {H : Type*} [Group H] [Finite H]

/-- Every unitary model has been removed; these are the remaining source obligations. -/
def ExceptionalOrCoverRemainder (p : ℕ) (K : Subgroup H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    ExceptionalFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ Nat.card (center (twoCoreComponent K)) = 3 ∧
    ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
      IsSLSign (twoCoreComponent K) unitary 3 q)

/-- The full split domain with every binary unitary case discharged. -/
theorem alternatives_or_exceptional_or_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ ExceptionalOrCoverRemainder p K := by
  rcases alternatives_or_reduced_actor_remainder hH hK hp ho hr a ha haK hgen
    with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3,hz,hm⟩ | ⟨rfl,hz,n,hn,_,hm⟩ | hcover
  · cases hm with
    | unitary n hn hm =>
      exact (not_noncubic_unitary_twoCore_model hH hK hp ho hp3 hr hz hn hm a ha haK).elim
    | triality n hn hm => exact Or.inr (Or.inl ⟨hp3,hz,Or.inl ⟨n,hn,hm⟩⟩)
    | ree m hm he => exact Or.inr (Or.inl ⟨hp3,hz,Or.inr ⟨m,hm,he⟩⟩)
  · exact Or.inl (alternatives_of_even_unitary_cubic_model hH hK hr hz (by omega) hm a ha haK hgen)
  · exact Or.inr (Or.inr hcover)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
