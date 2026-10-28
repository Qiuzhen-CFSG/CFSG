module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteReduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.JankoTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.JankoFour
/-!
# The invariant large-prime source reduced to odd degree three

The actual J₂ and J₄ local Sylow-pair exclusions are combined with the proved
prime restrictions. Together with the complete finite reduction, this removes
every alternating, sporadic, rank-one and exceptional binary endpoint from
the original intrinsic action. The actual SylowInput therefore yields its
original conclusion, including the full symplectic cyclic automizer, or an
odd PSL₃/PSU₃ model for its faithful normal component.

The remaining odd degree-three source theorem is independent. This module
retains that explicit model alternative and asserts no unproved A.3.15 case
existence. Source: Aschbacher–Smith A.3.15, pp.50–51, and 1.3.4, pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
variable {J : Type*} [Group J] [Finite J] {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
theorem not_jankoTwo
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have he := prime_eq_five_of_jankoTwo hA hB e
  subst p
  exact ExceptionalOdd.not_jankoTwo hA hB e

theorem not_jankoFour
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Janko4.Model) : False := by
  have he := prime_eq_eleven_of_jankoFour hA hB e
  subst p
  exact ExceptionalOdd.not_jankoFour hA hB e
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

theorem SylowInput.alternatives_or_odd_three
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p) :
    Alternatives p T P L ∨
    (∃ q, q.Prime ∧ Odd q ∧ ∃ unitary,
      IsPSLSign (SourceTransport.component h) unitary 3 q) := by
  rcases h.alternatives_or_odd_three_or_janko hA hC hp with ha | hm | hm | hm
  · exact Or.inl ha
  · exact Or.inr hm
  · exact (A315Source.not_jankoTwo (h.a315Input hA hC hp)
      (SourceTransport.complement_pairAction h hA hC hp) hm.some).elim
  · exact (A315Source.not_jankoFour (h.a315Input hA hC hp)
      (SourceTransport.complement_pairAction h hA hC hp) hm.some).elim
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
