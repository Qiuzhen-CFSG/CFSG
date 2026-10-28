module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryTransportExtras
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCounts
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPlacement

/-!
# The Held elementary certificates for arbitrary original subgroups

Sylow conjugacy transports the complete native class counts and pure-sixteen
placement to arbitrary elementary subgroups. Both the normalizer divisor and
the exact original subgroup are preserved by the same conjugation.
Source: Aschbacher--Smith 12.7.5, printed p. 840.
-/

public section
open Subgroup
namespace Held.OrdinaryElementary
open LocalPairs.SylowGeometry.Calculations
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

theorem card_classA_thirtyTwo
    (E : Subgroup He) [IsElementaryAbelian 2 E] (hE : Nat.card E = 32) :
    Nat.card {x : E // IsConj a (x : He)} = 6 ∨
      Nat.card {x : E // IsConj a (x : He)} = 10 := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_representative E
  let F := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hF : Nat.card F = 32 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hE
  simpa only [F, card_classA_map_conj] using card_classA_thirtyTwo_of_le F hF hg

theorem card_classA_sixteen
    (E : Subgroup He) [IsElementaryAbelian 2 E] (hE : Nat.card E = 16) :
    Nat.card {x : E // IsConj a (x : He)} = 0 ∨
      Nat.card {x : E // IsConj a (x : He)} = 2 ∨
      Nat.card {x : E // IsConj a (x : He)} = 4 ∨
      Nat.card {x : E // IsConj a (x : He)} = 6 ∨
      Nat.card {x : E // IsConj a (x : He)} = 12 := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_representative E
  let F := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hF : Nat.card F = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hE
  simpa only [F, card_classA_map_conj] using card_classA_sixteen_of_le F hF hg

theorem pure_sixteen_le_conjugate_core
    (E : Subgroup He) [IsElementaryAbelian 2 E] (hE : Nat.card E = 16)
    (hpure : ∀ x : E, ¬ IsConj a (x : He))
    (h5 : 5 ∣ Nat.card (normalizer (E : Set He))) :
    ∃ i : Bool, ∃ k : He, E ≤ (ambientWordCore i).map (MulAut.conj k).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_representative E
  let F := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hF : Nat.card F = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hE
  have h5F : 5 ∣ Nat.card (normalizer (F : Set He)) := by
    simpa only [F, normalizer_card_map_conj] using h5
  obtain ⟨i, k, hFk⟩ := pure_sixteen_le_conjugate_core_of_le F hF (pure_map_conj E g hpure) h5F hg
  exact ⟨i, g⁻¹*k, le_map_conj_of_map_conj_le E (ambientWordCore i) g k hFk⟩

end Held.OrdinaryElementary
