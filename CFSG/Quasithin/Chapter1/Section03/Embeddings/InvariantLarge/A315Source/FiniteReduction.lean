module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.Remaining
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteConsequences
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.LinearTwo

/-!
# The remaining odd-degree-three and Janko source branches

The original full Theorem C reduction is combined with the unconditional
odd PSL₂ Sylow-overgroup theorem and the actual finite Sylow-pair exclusions.
The literal faithful quotient action from SylowInput therefore has the proved
original symplectic alternative, or an odd PSL₃/PSU₃, J₂ or J₄ model. All
completed rows are eliminated without raw A.3.15 or local-output premises.
The three retained families have separate source owners; this is a reduction,
not a claim that the complete invariant branch has already been proved.

Source: Aschbacher–Smith A.3.15, pp.50–51, and Proposition 1.3.4, pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Section02.LocalModels ClassificationModels
variable {J : Type*} [Group J] [Finite J] {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

theorem remaining_odd_three_or_janko [Group.IsPerfect D]
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hm : RemainingModels D) :
    (∃ q, q.Prime ∧ Odd q ∧ ∃ unitary, IsPSLSign D unitary 3 q) ∨
      Nonempty (D ≃* Sporadic.LeechRelated.J2.Carrier) ∨ Nonempty (D ≃* Janko4.Model) := by
  cases hm with
  | linearTwo q e hq ho he hs hm => exact (OddSource.not_linearTwo hA hB hq ho hm).elim
  | oddThree q hq ho unitary hm => exact Or.inl ⟨q,hq,ho,unitary,hm⟩
  | sporadic name hname hm =>
    rcases hname with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
    · exact (not_higmanSims hA hB hm.some).elim
    · exact (not_held hA hB hm.some).elim
    · exact (not_rudvalis hA hB hm.some).elim
  | triality hm => exact (not_triality_two hA hB hm).elim
  | tits hm => exact (not_tits hA hB hm.some).elim
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
open Section02.LocalModels ClassificationModels
universe u
variable
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {T X P H L : Subgroup G}
include hA hC

theorem SylowInput.alternatives_or_odd_three_or_janko
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p) :
    Alternatives p T P L ∨
    (∃ q, q.Prime ∧ Odd q ∧ ∃ unitary,
      IsPSLSign (SourceTransport.component h) unitary 3 q) ∨
      Nonempty (SourceTransport.component h ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (SourceTransport.component h ≃* Janko4.Model) := by
  rcases h.alternatives_or_remaining_models hA hC hp with ha | hm
  · exact Or.inl ha
  · right
    let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
    let : Group.IsPerfect ((XiQuotient L) ⧸ center (XiQuotient L)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    let : Group.IsPerfect (SourceTransport.component h) :=
      Group.IsPerfect.ofSurjective (f := (SourceTransport.simpleComponentEquiv h).toMonoidHom)
        (SourceTransport.simpleComponentEquiv h).surjective
    exact A315Source.remaining_odd_three_or_janko (h.a315Input hA hC hp)
      (SourceTransport.complement_pairAction h hA hC hp) hm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
