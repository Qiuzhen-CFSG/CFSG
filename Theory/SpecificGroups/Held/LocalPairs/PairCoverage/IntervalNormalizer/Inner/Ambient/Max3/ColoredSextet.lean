module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitData
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask4
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask5
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask8
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask9
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet.Mask13
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound

/-!
# The seven colored Held graph groups and the max3 sextet

Six colorings force the sextet by one or two neighbor-count refinements.
The exceptional mask 12 refines the representative coloring. The proved bound
of 1024 on the even representative graph group shows that the actual
representative fills that group: its permitted orbit-label identity supplies
the matching lower bound. Its generators lie in max3 and therefore preserve
the sextet.

The final containment retains only the representative orbit-label identity,
as permitted by its contract. The graph bound is discharged by
`InnerNormalizer.GraphBound`. No identification of the seven colors with
actual entry orbit sizes, or of the sextet stabilizer with max3, is needed.

Sources: ATLAS HeG1-p2058B0/max3 and GLS3 Table 5.3p.
Finite data and their reproduction are documented in ColoredSextet/Source.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations

/-- The original representative supplies 1024 actual even graph symmetries. -/
public theorem representative_even_le_sextet_of_card_bound
    (horbits : ∀ x : Fin 2058,
      InnerNormalizer.orbitSizeLabel x = Nat.card (MulAction.orbit representative x))
    (hupper : Nat.card InnerNormalizer.evenColoredGraphGroup ≤ 1024) :
    InnerNormalizer.evenColoredGraphGroup ≤ sextetPermutationStabilizer := by
  have hp : representative.map representation ≤ InnerNormalizer.evenColoredGraphGroup := by
    rintro _ ⟨g, hg, rfl⟩
    exact InnerNormalizer.normalizer_mem_evenColoredGraphGroup horbits g (le_normalizer hg)
  have he : representative.map representation = InnerNormalizer.evenColoredGraphGroup := by
    apply eq_of_le_of_card_ge hp
    rw [Subgroup.card_map_of_injective representation_injective]
    exact hupper.trans (InnerNormalizer.representative_card_ge_of_orbit_labels horbits)
  intro σ hσ
  rw [← he] at hσ
  obtain ⟨g, hg, rfl⟩ := hσ
  exact localOvergroup_le_sextetStabilizer (representative_le_localOvergroup hg)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.ColoredSextet

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3

/-- Six masks preserve the sextet even without restricting permutation parity. -/
public theorem coloredGraphGroup_le_sextet_of_ne_five
    (t : Fin 7) (ht : t ≠ 5) : coloredGraphGroup t ≤ sextetPermutationStabilizer := by
  fin_cases t
  · exact ColoredSextet.coloredGraphGroup_0_le_sextet
  · exact ColoredSextet.coloredGraphGroup_1_le_sextet
  · exact ColoredSextet.coloredGraphGroup_2_le_sextet
  · exact ColoredSextet.coloredGraphGroup_3_le_sextet
  · exact ColoredSextet.coloredGraphGroup_4_le_sextet
  · exact (ht rfl).elim
  · exact ColoredSextet.coloredGraphGroup_6_le_sextet

/-- Assembly of all seven containments from the independent representative bound.
The representative orbit-label identity is an explicitly permitted premise. -/
public theorem evenColoredGraphGroup_le_sextet_of_representative_bound
    (horbitsP : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit SylowGeometry.Calculations.representative x))
    (hupper : Nat.card SylowGeometry.Calculations.InnerNormalizer.evenColoredGraphGroup ≤ 1024)
    (t : Fin 7) : evenColoredGraphGroup t ≤ sextetPermutationStabilizer := by
  by_cases ht : t = 5
  · subst t
    exact ColoredSextet.evenColoredGraphGroup_5_le_representative_even.trans
      (ColoredSextet.representative_even_le_sextet_of_card_bound horbitsP hupper)
  · exact inf_le_left.trans (coloredGraphGroup_le_sextet_of_ne_five t ht)

/-- Every even symmetry of each of the seven published colored Held graphs
preserves the max3 sextet. Only the representative orbit-label identity is
assumed; the representative graph bound is already proved. -/
public theorem evenColoredGraphGroup_le_sextet
    (horbitsP : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit SylowGeometry.Calculations.representative x))
    (t : Fin 7) : evenColoredGraphGroup t ≤ sextetPermutationStabilizer :=
  evenColoredGraphGroup_le_sextet_of_representative_bound horbitsP
    SylowGeometry.Calculations.InnerNormalizer.evenColoredGraphGroup_card_le t

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
