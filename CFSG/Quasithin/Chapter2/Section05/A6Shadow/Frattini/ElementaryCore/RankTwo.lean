module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.RankTwo.LocalCore
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.RankTwo.Family

/-!
# The rank-two E₃₂ family in the elementary-core argument

The local cores are the actual relative centralizers. When S_C is an
elementary four-group, the crossed core supplies a transposition and
centralizes the inner Sylow factor upstairs. Thus the local cores split
as S_C S_C^x E_i and are elementary of order 32. Kernel-image counting
classifies every elementary subgroup of largest order, and a lift of
the model rotation interchanges the two cores. Applying the family orbit
lemma retains the original crossing element x throughout.

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. The final
wrapper accepts the reduction owner's four inputs; the proof needs only
that S_C is elementary of order four. The rank reduction and the other
branches remain with the source assembly.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

theorem localCore_split (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 4)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    localCore d E = d.SC ⊔ rightConjugate d.x d.SC ⊔ E := by
  rw [localCore_eq d E hE]
  rcases four_subgroups d E hE with rfl | rfl
  · exact centralizer_fourZero_split d hEA hcard
  · exact centralizer_fourOne_split d hEA hcard

theorem localCore_elementary (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 4)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    IsElementaryAbelian 2 (localCore d E) := by
  rw [localCore_eq d E hE]
  rcases four_subgroups d E hE with rfl | rfl
  · exact centralizer_fourZero_elementary d hEA hcard
  · exact centralizer_fourOne_elementary d hEA hcard

theorem localCore_card (hcard : Nat.card d.SC = 4)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    Nat.card (localCore d E) = 32 := by
  rw [localCore_eq d E hE]
  rcases four_subgroups d E hE with rfl | rfl
  · exact card_centralizer_fourZero d hcard
  · exact card_centralizer_fourOne d hcard

theorem largestElementary_eq_pair (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 4) :
    largestElementary d.S = {localCore d (fourZero d), localCore d (fourOne d)} := by
  rw [localCore_eq d _ (fourZero_le d), localCore_eq d _ (fourOne_le d)]
  exact largest_elementary_family d hEA hcard

theorem localCores_conjugate : ∃ s ∈ d.S,
    rightConjugate s (localCore d (fourZero d)) = localCore d (fourOne d) := by
  rw [localCore_eq d _ (fourZero_le d), localCore_eq d _ (fourOne_le d)]
  exact centralizers_conjugate d

/-- The original crossing has the source orbit whenever its core is an
actual elementary four-group. No later involution identity is needed. -/
theorem hasNormalizerOrbit_of_elementary_four (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) : HasNormalizerOrbit d :=
  hasNormalizerOrbit_of_largest_pair d (largestElementary_eq_pair d hEA hcard)
    (localCores_conjugate d)

/-- Source-facing rank-two interface, accepting precisely the reduction
owner's inputs. The proof establishes the stronger two-input result above. -/
theorem hasNormalizerOrbit_of_rank_two (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) (_hz : d.z = d.zK)
    (_hplus : plus d = d.SC ⊔ rightConjugate d.x d.SC) : HasNormalizerOrbit d :=
  hasNormalizerOrbit_of_elementary_four d hEA hcard

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
