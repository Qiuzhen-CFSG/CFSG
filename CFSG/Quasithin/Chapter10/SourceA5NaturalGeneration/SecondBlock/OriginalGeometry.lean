module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.Original
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.FieldUniverse
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
/-!
# Original block data for the common source assembly

The exact original natural-four section selects the genuine paired source
and identifies the first intrinsic natural block. Its full-core recovery
and paired source retain the core equality, zero center, original Baumann
placement and Sylow property, and Baumann normalization of L. These are the
same marked subgroups used by the terminal torus consumer.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance originalDataFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem source_original_block_geometry_of_hstar_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
 :
    IsL2EvenBlock L 2 ∧ pCore 2 L=blockU L ∧ center L=⊥ ∧
      baumann (T : Subgroup G) ≤ localOrbit T L ∧
      Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
        (localOrbit T L ⊔ baumann (T : Subgroup G)) ∧
      baumann (T : Subgroup G) ≤ normalizer (L : Set G) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker=C := QuotientGroup.ker_mk' C
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D hH hZH
  obtain ⟨d,E,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  have hE := ChapterC.RankOne.ChiProduct.SelectedRankOne.paired_linear_field_large
    S (source_a5_minimal_parabolic D e hn) U hU hJ q hq hk
      (source_join_not_solvable D) d E c
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq] at hE ⊢
    have hd : 2 ≤ E.degree := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      norm_num at hp
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hp
    omega
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hL : ChapterC.IsL2EvenBlock L 2 :=
    source_natural_block_of_identified_moved_section_any_universe L D.fullModule
      (ChapterC.RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLH) hb.short)
      (source_original_blockU_eq_full_moved D hb) (e.trans f) hF n
  obtain ⟨hBO,hBS⟩ := source_original_baumann_in_orbit_of_source
    D e hn hb hz hH hZH hJ d E hlarge c hexchange
  have hclass := source_original_component_localClass_of_hstar_natural_four
    D e hn hH hZH hF f n
  have hSm : (S : Subgroup X).map X.subtype=(T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hBm := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype=baumann ((S : Subgroup X).map X.subtype) at hBm
  rw [hSm] at hBm
  have hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G) := by
    have hh := map_mono (f := X.subtype)
      (le_normalizer_iff_commutator_le_right.mp hclass.2.1)
    rw [map_commutator,hBm,map_subgroupOf_eq_of_le
      ((le_componentOrbit L T).trans le_sup_left)] at hh
    exact le_normalizer_iff_commutator_le_right.mpr hh
  exact ⟨hL,source_original_block_core_eq_blockU D e hn hb hz hH hZH,
    source_original_block_center_eq_bot D hn hb hz,hBO,hBS,hBL⟩
end CFSG.Quasithin.Chapter10
