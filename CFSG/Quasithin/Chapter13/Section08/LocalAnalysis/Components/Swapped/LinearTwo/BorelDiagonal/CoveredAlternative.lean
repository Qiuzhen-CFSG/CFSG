module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeConjugation

/-!
# The actual covered-A₆ quotient alternative

Three-rank two excludes the ordinary A₆ case because its marked local
quotient above O₂(L₁) has order three. The output identifies L/O₂(L) with
the even hexacode automorphism carrier of the triple cover. The earlier
model alternatives and ordinary local quotient calculation remain explicit
source inputs; the Borel construction supplies the rank-two hypothesis.

Source: Aschbacher–Smith, Notation 13.2.1, printed p.877, and the proof of
13.8.16(1), printed p.952, using the theta identity in 13.7.3(9).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G] [Finite G]

/-- The Borel's transferred rank excludes the ordinary A₆ alternative, whose
marked local quotient is cubic. The output is an actual quotient isomorphism. -/
theorem covered_quotient_of_threeRank_two (L L₁ : Subgroup G)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hrank : primeRank 3 L₁ = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases hmodels with h | h
  · have hbound := rank_le_one_of_cubic_core_quotient L₁ (ha6 h)
    omega
  · exact h

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
