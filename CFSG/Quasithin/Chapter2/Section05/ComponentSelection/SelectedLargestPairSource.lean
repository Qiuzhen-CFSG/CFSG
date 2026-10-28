module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlignedPairs
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.StarredSourceSetup
public import CFSG.Quasithin.Chapter2.Section05.LargestPairSource
/-!
# A largest source pair inside the prescribed Sylow subgroup

The saturated-pair selection retains the globally largest base when H is
in Γ*. Conjugation within H ∩ M places its base and two-core in the
prescribed source Sylow. This provides the literal U*(H) member required
by 2.5.12 and the later order-two core argument, without assuming its base
was already aligned.

Source: Aschbacher--Smith Notation 2.5.9 and 2.5.10, printed p.557.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The genuine Γ* setup supplies a globally largest pair in its original Sylow. -/
theorem MathieuSourceSetup.exists_largest_pair_in_sylow
    (c : MathieuSourceSetup H K M S z)
    (hstar : H ∈ gammaStar (Chapter1.He G) M) :
    ∃ U L : Subgroup G, (U, L) ∈ largestLocalPairs M H ∧
      U ≤ (S : Subgroup H).map H.subtype ∧
      twoCore L ≤ (S : Subgroup H).map H.subtype := by
  have hSM : (S : Subgroup H).map H.subtype ≤ M :=
    (beta_mono c.pair.1.1 c.base_le (S.isPGroup'.map H.subtype)).2.1
  obtain ⟨U, L, hp, hUS, hQS, hbig, _⟩ := exists_saturated_pair_aligned c.gamma S hSM
  exact ⟨U, L, ⟨hp, hbig hstar⟩, hUS, hQS⟩

/-- The selected largest pair also has the original marked involution in its base. -/
theorem MathieuSourceSetup.exists_largest_pair_with_mark
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hstar : H ∈ gammaStar (Chapter1.He G) M) :
    ∃ U L : Subgroup G, (U, L) ∈ largestLocalPairs M H ∧
      U ≤ (S : Subgroup H).map H.subtype ∧ z ∈ U := by
  obtain ⟨U, L, hp, hUS, _⟩ := MathieuSourceSetup.exists_largest_pair_in_sylow c hstar
  have hz : z ∈ centerIn ((S : Subgroup H).map H.subtype) := by
    let h := c.hypotheses115 hG
    exact ⟨h.mem_sylow, h.central⟩
  exact ⟨U, L, hp, hUS,
    largest_pair_center_le hG c.T c.maximal c.sylow_le hp hUS hz⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
