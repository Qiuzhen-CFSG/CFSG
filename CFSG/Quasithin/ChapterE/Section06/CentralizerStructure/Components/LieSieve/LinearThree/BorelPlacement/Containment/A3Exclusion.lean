module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.Construction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion.BlockStructure
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion.Projection
public import Theory.GroupTheory.ComponentLocalTwelveExclusion
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelTwelve

/-!
# A₃-block exclusion from even-field PSL₃ Borel overgroups

The genuine block definitions imply two-perfection, order twelve and trivial
center. These properties are transported to the relative subgroup of the
actual overgroup, retaining the subnormality required by the source.
The marked Borel projection has exactly the component's central kernel.

For a positive even field exponent, the actual matrix Borel excludes
subnormal two-perfect groups of order twelve: a nontrivial torus element
has at least q² unipotent conjugates. The central component-orbit theorem
transfers this exclusion to the join of the marked Borel with Q. This uses
only N_Q(L)-stability and retains the noncentral block module.

The ordinary even-exponent and PSL₃(4) central-cover exclusions below
discharge both intrinsic premises. They permit trivial covering centers
and need only the local component and Sylow data, without E.6.1 or E.6.7.
The parent containment module owns the subsequent E.6.7 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248, especially the Borel paragraph on p.248; C.1.7 and
C.1.12–13 supply the short-group and module definitions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
variable {G : Type*} [Group G] {D X : Subgroup G}

/-- The actual relative subgroup retains all three properties needed by the
component-orbit exclusion. Normality in the ambient group is not assumed. -/
theorem alternatingThree_relative_profile (hDX : D ≤ X)
    (hD : ChapterC.IsAlternatingBlock D 3) :
    IsPPerfect 2 (D.subgroupOf X) ∧ Nat.card (D.subgroupOf X) = 12 ∧
      center (D.subgroupOf X) = ⊥ := by
  let e := subgroupOfEquivOfLe hDX
  refine ⟨hD.2.1.twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans (alternatingThree_card hD), ?_⟩
  apply bot_unique
  intro x hx
  have he : e x ∈ center D := (centerCongr e ⟨x, hx⟩).property
  rw [alternatingThree_center_eq_bot hD, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

/-- A source-independent order-twelve exclusion suffices for genuine A₃ blocks.
The matrix and component-orbit arguments must discharge this explicit premise. -/
theorem not_alternatingThree_of_no_subnormal_twelve
    (hno : ∀ E : Subgroup X, E.IsSubnormal → IsPPerfect 2 E →
      center E = ⊥ → Nat.card E ≠ 12)
    (hDX : D ≤ X) (hs : (D.subgroupOf X).IsSubnormal) :
    ¬ ChapterC.IsAlternatingBlock D 3 := by
  intro hD
  obtain ⟨hp, hc, hz⟩ := alternatingThree_relative_profile hDX hD
  exact hno (D.subgroupOf X) hs hp hz hc

variable [Finite G] {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The actual central-quotient model excludes relatively subnormal A₃ blocks
from the marked Borel overgroup, even when Q permutes the components. -/
theorem quotient_even_not_alternatingThree
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hDX : D ≤ markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)
    (hs : (D.subgroupOf
      (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)).IsSubnormal) :
    ¬ ChapterC.IsAlternatingBlock D 3 := by
  intro hD
  obtain ⟨F, _, _, hF, f, hf, hker⟩ := exists_markedBorel_projection hn iso S
  exact hL.2.relative_local_adjoin_no_twelve hL.1 (map_subtype_le _)
    (inf_le_right.trans (Subgroup.centralizer_le hU.1))
    (T.isPGroup'.to_le inf_le_left) hz (markedBorel_stable S hS) f hf hker
    (Matrix.PSL3.LinearThree.BorelStructure.borel_core_selfCentralizing F hF)
    (Matrix.PSL3.LinearThree.BorelTwelve.card_ne_twelve F hn heven hF)
    D hDX hs hD.2.1.twoPerfect (alternatingThree_center_eq_bot hD)
    (alternatingThree_card hD)

/-- The ordinary PSL₃(2ⁿ) branch for positive even n. The matrix model supplies
the trivial center and the genuine central-quotient identification. -/
theorem ordinary_even_not_alternatingThree
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hDX : D ≤ markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)
    (hs : (D.subgroupOf
      (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)).IsSubnormal) :
    ¬ ChapterC.IsAlternatingBlock D 3 :=
  quotient_even_not_alternatingThree hU hL S hS hn heven
    (ordinary_center_isTwoGroup iso) (ordinary_quotient_model iso) hDX hs

/-- The central-cover PSL₃(4) branch, including a trivial covering center. -/
theorem cover_not_alternatingThree
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L)) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hDX : D ≤ markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)
    (hs : (D.subgroupOf
      (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)).IsSubnormal) :
    ¬ ChapterC.IsAlternatingBlock D 3 :=
  quotient_even_not_alternatingThree hU hL S hS (n := 2) (by decide) (by decide)
    hz iso hDX hs

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
