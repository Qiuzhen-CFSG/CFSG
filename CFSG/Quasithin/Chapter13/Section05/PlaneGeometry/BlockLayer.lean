module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.LocalSetup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
/-!
# The literal block layer and its full normalizer

The actual A₆ block from C.1.24 has commutator layer equal to the original
natural module V: the block support identity gives containment, and its
faithful natural coordinates give equal order. Thus N_G(L) normalizes V,
without choosing a new module or discarding a central two-cover.
The original unique maximal two-local property also supplies characteristic
two in M. These are the source inputs for the subsequent two-A₃ calculation.

Source: Aschbacher--Smith 13.5.6, printed p.917, after applying C.1.24(c).
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
local notation "H" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LH" => L.subgroupOf H
local notation "VH" => V.subgroupOf H

theorem block_layer_eq_module (hb:ChapterC.IsAlternatingBlock LH 6) :
    (ChapterC.blockU L).map L.subtype=V := by
  let := local_module_normal d
  let := local_module_elementary d
  have hblock : ChapterC.IsBlock LH :=
    ⟨inferInstance,hb.2.1,d.counterexample.local_component.1.1.subnormal⟩
  have hu:=ChapterC.RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
    LH VH hblock (local_module_commutator_ne_bot d)
  obtain ⟨e,he⟩:=ChapterC.RankOne.SymmetricSix.blockU_natural_six_coordinates LH VH hblock
    (permutation d) (permutation_local_image d) (localCoordinate d)
    (localCoordinate_conjugation d) (local_module_commutator_ne_bot d)
  have hU:(ChapterC.blockU LH).map (LH).subtype=VH := by
    apply (eq_of_le_of_card_ge (hu ▸ commutator_le_left VH LH) ?_)
    rw [card_map_of_injective (LH).subtype_injective]
    exact le_of_eq ((Nat.card_congr (localCoordinate d).toEquiv).trans
      (Nat.card_congr e.toEquiv).symm)
  have hi:=congrArg (map (H).subtype) hU
  rw [map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)] at hi
  let eL:LH≃*L:=subgroupOfEquivOfLe le_sup_left
  rw [←ChapterC.RankOne.Solvable.blockU_map_equiv eL,map_map]
  rw [map_map] at hi
  exact hi

theorem block_normalizer_normalizes_module (hb:ChapterC.IsAlternatingBlock LH 6) :
    M≤normalizer (V:Set G) := by
  rw [←block_layer_eq_module d hb,d.local_normalizer]
  have : (ChapterC.blockU L).Characteristic := by unfold ChapterC.blockU;infer_instance
  exact normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)

theorem source_maximal_local
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M) :
    IsMaximalTwoLocal M := by
  obtain ⟨N,hN,hHN⟩:=exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H
    d.counterexample.local_component.1.2
  exact hu N hN hHN ▸ hN

theorem source_characteristic_local
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M) :
    generalizedFitting M=pCore 2 M := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply d.counterexample.qtke.evenCharacteristic T M (source_maximal_local d hu)
  rw [d.local_normalizer]
  exact d.normalizes_L

/-- The original block, its literal module, and the full M normalization. -/
theorem source_block_and_module
    (hq:IsQuasisimple (L⧸pCore 2 L))
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→H≤N→N=M)
    (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0)
    (he:¬normalizer (planeCentralizer (T:=T) W:Set G)≤M) :
    ChapterC.IsAlternatingBlock L 6 ∧
      (ChapterC.blockU L).map L.subtype=V ∧
      M≤normalizer (V:Set G) ∧ generalizedFitting M=pCore 2 M := by
  have hb:=source_alternatingBlock_of_escape d hq hu W hWV hcard hn he
  exact ⟨ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (subgroupOfEquivOfLe (show L≤H from le_sup_left)) hb,
    block_layer_eq_module d hb,block_normalizer_normalizes_module d hb,
    source_characteristic_local d hu⟩

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
