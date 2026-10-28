module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences

/-!
# Initial-stage assembly for binary MS93 (4.3.1)

The strict radius growth R₀ ≠ R gives the order-four and edge identities in
(i)--(ii). That order supplies the actual natural quotient and moving
generation in (iii)--(iv). These two stages hold for every contrary critical
configuration, so they discharge the uniform premises used to exclude
distance four and prove the commutator bounds and identity in (v)--(vii).

`initialFacts` constructs all seven clauses from the source, geometry,
b > 2, module facts and the contrary configuration. In particular its
natural section retains the quotient normalities, triple commutator,
fixed/moving splitting and equivariant coordinates. No later escape or
pairing conclusion is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Assemble the seven source clauses from three explicit stages.
The radius growth, representation and final geometric stage are not proved
by this conditional assembly theorem. -/
theorem initialFacts_of_stages (p : Counterexample geometry) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hgrowth : radiusCommutator p.a p.a' ≠ criticalCommutator p.a p.a')
    (sectionFacts : SectionFacts p) (tailFacts : TailFacts p) : Nonempty (InitialFacts p) := by
  have hcard := (radius_card_four_iff_ne_critical p source hb modules).mpr hgrowth
  exact ⟨{
    radius_eq_edge := radius_eq_edge_of_card_four p source hb modules hcard
    radius_card := hcard
    critical_card := p.critical_card source hb modules
    critical_index := critical_index_of_radius_card_four p source hb modules hcard
    natural_section := sectionFacts.natural_section
    moving_generation := sectionFacts.moving_generation
    six_le := tailFacts.six_le
    radius_moving_card := tailFacts.radius_moving_card
    H_card := H_card_of_radius_moving p hb tailFacts.radius_moving_card
    edge_commutator := tailFacts.edge_commutator }⟩

/-- All seven clauses of binary MS93 (4.3.1), with every intermediate stage
discharged. The uniform preceding stages apply to the actual transported
counterexamples used by the tail argument. -/
theorem initialFacts (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : Nonempty (InitialFacts p) := by
  have hfour : ∀ q : Counterexample geometry,
      Nat.card (radiusCommutator q.a q.a') = 4 := fun q =>
    (radius_card_four_iff_ne_critical q source hb modules).mpr
      (radius_ne_critical source hb modules q)
  have hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q) := fun q =>
    Natural.sectionFacts_of_radius_card_four source geometry hb modules q (hfour q)
  obtain ⟨sectionFacts⟩ := hsections p
  exact initialFacts_of_stages p source hb modules (radius_ne_critical source hb modules p)
    sectionFacts (tailFacts_of_uniform_stages source hb modules hfour hsections p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
