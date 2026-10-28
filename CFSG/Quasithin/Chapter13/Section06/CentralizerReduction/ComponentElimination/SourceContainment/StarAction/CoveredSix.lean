module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.Centerless
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.CoveredSix.SourceConsequence
public import Theory.Representation.HexacodeAction.Cover

/-!
# The central cubic reduction in the covered-six branch

Under hypothetical star normalization, the actual L_v⁺ equals the image
of Z(K⁺), when K⁺ is identified with the genuine hexacode triple cover.
The marked 13.6.11 action gives nontriviality; the star-to-plus comparison
and 13.6.20 containment give centrality; the center has prime order three.
Thus this case does not reduce to the centerless argument.

The covered-six star obstruction remains unresolved: a central cubic
acts nontrivially on the genuine six-dimensional module. The separate
SourceConsequence module proves the source conclusion K ⊄ M directly
from the genuine earlier 13.6.16(1) inputs, providing an alternative route
for 13.6.21 without assuming the missing star obstruction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.11 and 13.6.14, printed pp.928–930; 13.6.20–21, pp.931–932.
The concrete covered group and its center are from the attributed ATLAS
port in Theory.Representation.HexacodeAction.Cover.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.CoveredSix
open ComponentSelection
variable {G : Type*} [Group G]

private theorem eq_of_le_of_cubic_card {A B : Subgroup G} (hAB : A ≤ B)
    (hA : A ≠ ⊥) (hB : Nat.card B = 3) : A = B := by
  let : Fact (Nat.card B).Prime := ⟨hB ▸ Nat.prime_three⟩
  rcases (A.subgroupOf B).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have he := congrArg (map B.subtype) hb
    rw [map_subgroupOf_eq_of_le hAB, Subgroup.map_bot] at he
    exact (hA he).elim
  · have he := congrArg (map B.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hAB, ← MonoidHom.range_eq_map,
      range_subtype] using he

/-- Hypothetical normalization forces equality with the actual cubic center.
This is a reduction, not a contradiction: the genuine covered-six center
has a nontrivial action on its faithful module. -/
theorem plusImage_Lv_eq_center_of_star_normalizes [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (K T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hLK : Lv L (A5Module.markedV s) ≤ K)
    (hR : pCore 2 (Gplus K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz) = ⊥)
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (e : plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K ≃*
      Atlas.Codes.HexEvenAutomorphisms)
    (hstar : starImage (A5Module.markedZ s) (A5Module.markedV s) K ≤
      normalizer (starImage (A5Module.markedZ s) (A5Module.markedV s)
        (Lv L (A5Module.markedV s)) : Set (Gstar (A5Module.markedZ s) (A5Module.markedV s)))) :
    plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
        (Lv L (A5Module.markedV s)) =
      (center (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K)).map
        (plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K).subtype := by
  let C := plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz K
  have hcenter : Nat.card (center C) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card
  have hc := plus_commutator_eq_bot_of_star_normalizes K L T _ _ hL hz hK hR hcard hstar
  apply eq_of_le_of_cubic_card
    (plusImage_Lv_le_center_of_commutator_eq_bot K L T _ _ hL hz hLK hc)
    (plusImage_Lv_ne_bot s K T S hS hL hz hK hn)
  exact (Nat.card_congr
    ((center C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv).symm.trans hcenter

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.CoveredSix
