module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.OnanSource
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The source O'Nan obstruction from the two intrinsic image bounds

For the actual V=C_T(X), containment V≤X already puts V in O₂(X):
V is a two-group and centralizes X. Thus the exceptional order-21 case
needs only the two intrinsic seven-free image bounds. The stronger
V=Φ(O₂(X)) equality is not required for this contradiction.

All original root geometry, actor maps, Sylow index and cover-normalizer
conditions are retained. The complete Goldschmidt–O'Nan theorem discharges
the alternatives premise, and its first three cases use the existing
normalizer and orbit-count arguments. The source geometry and the two
image bounds still have to be constructed by their existing owners.

Source: Aschbacher–Smith, Lemma16.5.13, printed pp.1201–1202.
-/

@[expose] public section
open Subgroup
open Representation Representation.BinaryOffender Representation.GoldschmidtONan
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
variable {G : Type*} [Group G]

/-- A Sylow-centralizer contained in X lies in its actual embedded two-core. -/
theorem space_le_twoCore_of_le_residual {T : Sylow 2 G} {X : Subgroup G}
    (hVX : space T X ≤ X) : space T X ≤ twoCore X := by
  change space T X ≤ X.pCoreIn 2
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le (show space T X ≤ T from inf_le_left)) hVX
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer (space T X : Set G))
  intro x hx
  apply mem_centralizer_iff.mpr
  intro v hv
  exact (mem_centralizer_iff.mp hv.2 x hx).symm

private theorem source_binary_card {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] :
    Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The two intrinsic seven-free images required by the order-21 obstruction. -/
def SourceImageBounds (V X : Subgroup G) : Prop :=
  Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range) ∧
  Nat.Coprime 7 (Nat.card ((topAction (residualAction V X)).ker.map
    (sectionAction (residualAction V X))))

/-- The full source alternatives are impossible from the root geometry and the
two intrinsic image bounds; no Frattini-equality premise is needed. -/
theorem no_onan_action_of_source_image_bounds [Finite G]
    {T : Sylow 2 G} {L X Z : Subgroup G} [IsElementaryAbelian 2 (space T X)]
    (S : Subgroup (action (space T X) X).range)
    (hinput : Input (representation (space T X) X) S)
    (hfixed : fixedSpace (representation (space T X) X) S =
      linearSpace (space T X) (commutingSylow T L))
    (hmoved : Representation.RegularCyclicNormalClosure.displacementSpan
      (representation (space T X) X) S ⊤ = linearSpace (space T X) Z)
    (hXL : X ≤ L) (hZ : Z ≠ ⊥) (hZV : Z ≤ space T X) (hZX : Z ≤ X)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hbound : ((T : Subgroup G) ⊓ normalizer (X : Set G)).relIndex T ≤ 2)
    (g : G) (hg : g ∈ actingGroup (space T X) X)
    (hmove : g ∉ normalizer (commutingSylow T L : Set G))
    (hcoverT : commutingSylow T L ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G))
    (hcover : space T X ≤ X → SourceImageBounds (space T X) X) : False := by
  have halt := CFSG.Quasithin.GoldschmidtONan.alternatives hinput
  let V := space (T : Subgroup G) X
  let C := commutingSylow T L
  let ρ := representation V X
  let π := (action V X).rangeRestrict
  have hCV : C ≤ V := le_inf inf_le_left (inf_le_right.trans (centralizer_le hXL))
  have horbit := fixedOrbit_card_eq_relIndex hCV hfixed
  rcases halt with hs | hs | hs | he
  · have hfix := hs.2 (π ⟨g, hg⟩)
    rw [hfixed] at hfix
    exact hmove (mem_normalizer_iff_map_conj_eq.mpr
      ((linearSpace_map_eq_iff hCV hCV ⟨g, hg⟩).mp hfix))
  · obtain ⟨horb, t, _, ht, _⟩ := hs
    obtain ⟨m, hm⟩ := (action V X).rangeRestrict_surjective t
    have hswap : C.conjBy m = Z := by
      rw [← hm, hfixed, hmoved] at ht
      exact (linearSpace_map_eq_iff hCV hZV m).mp ht
    have hcard : Nat.card (fixedOrbit ρ S) = 2 := by
      rw [horb, Nat.card_coe_set_eq, Set.ncard_pair hinput.fixed_ne_moved]
    have hindex : (normalizer (C : Set G)).relIndex (actingGroup V X) = 2 :=
      horbit.symm.trans hcard
    exact no_swapped_index hTL rfl m.property (hswap ▸ hZX) hcoverT hindex
  · have hcard := hs.1
    rw [source_binary_card (E := Representation.RegularCyclicNormalClosure.displacementSpan
      (representation V X) S ⊤)] at hcard
    rw [horbit] at hcard
    exact no_large_two_power_index T hinput.moved_dimension_gt_one inf_le_left
      (sylowNormalizer_le_actingGroup T X)
      (inf_le_left.trans (sylow_normalizes_commutingSylow hTL)) hbound hcard
  · have hV : Nat.card V = 8 := by
      have hc := source_binary_card (E := Additive V)
      rw [he.2.1] at hc
      exact hc
    have hVX := space_le_residual_of_order_twentyOne hV he.2.2.1 hZ hZV hZX
    obtain ⟨hq, hm⟩ := hcover hVX
    exact no_order_twentyOne_image (space_le_twoCore_of_le_residual hVX) hq hm he.2.2.1
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
