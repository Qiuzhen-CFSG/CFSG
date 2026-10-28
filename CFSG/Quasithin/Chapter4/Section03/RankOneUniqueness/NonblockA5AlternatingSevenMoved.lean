module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonsplitMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSevenMoved

/-!
# The whole initial moved module in the actual A₇ source row

The original full module W lies properly in the literal moved star module.
It lies there because [W,L]=W and L≤K; equality would make K normalize W,
contrary to the source normalizer condition. The chosen A₅ module has sixteen
elements, so the entire moved star space has more than sixteen elements.

The proved B.5.1 A₇ consumer consequently supplies splitting and natural
coordinates on that entire moved space. This retains the original star
action and its actual selected section. It does not identify this initial
space with the whole core commutator or assert that K is a block.
Source: Aschbacher--Smith C.4.1, C.4.8 and original 4.3.7,
pp.151--154 and 615--616, with B.5.1 and I.1.6, pp.99--103 and 408.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Every actual moved star section strictly contains the original full
module, so its cardinality exceeds that of the chosen sixteen-element module. -/
theorem a5_star_moved_card_gt_sixteen
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hCO : starImage (K c) (c.I.pCoreIn 2) (K c) ≤
      offenderSubgroup (starRepresentation (K c) (c.I.pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation (K c) (c.I.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation (K c) (c.I.pCoreIn 2))).subtype)
      ((starImage (K c) (c.I.pCoreIn 2) (K c)).subgroupOf
        (offenderSubgroup (starRepresentation (K c) (c.I.pCoreIn 2))))) :
    16 < Nat.card s.space.toSubmodule := by
  let R := c.I.pCoreIn 2
  let J := K c ⊔ R
  let U := starV (K c) R
  let B := (K c).subgroupOf J
  let A := (⁅U,B⁆ : Subgroup J).map J.subtype
  have hspan : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  have hm : ⁅W c,L⁆ = W c :=
    (show W c = ⁅W c,L⁆ from by simpa only [hspan] using c.c28.module_commutator).symm
  have hWU : W c ≤ U.map J.subtype :=
    c.c28.constrained_module_le_starV c.K c.component c.quotient c.block_source_outside hf
  have hA : A = ⁅U.map J.subtype,K c⁆ := by
    change (⁅U,B⁆ : Subgroup J).map J.subtype = _
    rw [map_commutator,map_subgroupOf_eq_of_le (show K c ≤ J from le_sup_left)]
  have hWA : W c < A := by
    apply lt_of_le_of_ne
    · rw [hA,←hm]
      exact commutator_mono hWU c.le_component
    · intro he
      have hn : K c ≤ normalizer (W c : Set G) := by
        rw [he,hA]
        exact normalizer_commutator_ge_right _ _
      exact c.component_outside
        ((le_inf (map_subtype_le _) hn).trans (c.c28.module_normalizer.trans inf_le_right))
  have hv : Nat.card V = 16 := by
    rw [←d.flag.module.range_eq,←Nat.card_congr (MonoidHom.ofInjective d.flag.module.injective).toEquiv]
    change Nat.card (BinaryPermutation.core (Fin 5)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,BinaryPermutation.finrank_core]
    rfl
  have hW : 16 ≤ Nat.card (W c) := hv ▸
    card_le_of_le (Section02.Unitary.chosen_le_fullModule d.chosen)
  have hlt : Nat.card (W c) < Nat.card A :=
    Set.Finite.card_lt_card (Set.toFinite (A : Set G)) hWA
  have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace U B := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U
      (QuotientGroup.mk' (starKernel (K c) R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),s.space_eq]
    change subspaceCommutator
      ((starRepresentation (K c) R).comp
        (offenderSubgroup (starRepresentation (K c) R)).subtype) ⊤
      ((starImage (K c) R (K c)).subgroupOf
        (offenderSubgroup (starRepresentation (K c) R))) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    rfl
  let : IsElementaryAbelian 2 (⁅U,B⁆ : Subgroup J) :=
    IsElementaryAbelian.of_le (commutator_le_left U B)
  have hc := Nat.card_congr (NormalElementaryQuotient.commutatorSpaceEquiv U B).toEquiv
  change Nat.card (⁅U,B⁆ : Subgroup J) = Nat.card (NormalElementaryQuotient.commutatorSpace U B) at hc
  have hcard : Nat.card A = Nat.card s.space.toSubmodule := by
    change Nat.card ((⁅U,B⁆ : Subgroup J).map J.subtype) = _
    rw [card_map_of_injective J.subtype_injective,hs]
    exact hc
  exact hcard ▸ hW.trans_lt hlt

/-- The actual A₇ star row supplies natural coordinates on its whole moved
space and a complement to the component-fixed space, without a block premise. -/
theorem alternatingSeven_star_natural_moved_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* alternatingGroup (Fin 7)) :
    let ρ := starRepresentation (K c) (c.I.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K c) (c.I.pCoreIn 2) (K c)
    C ≤ O ∧ ∃ s : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp O.subtype) (C.subgroupOf O),
      IsCompl s.sectionData.space.toSubmodule (fixedSpace (ρ.comp O.subtype) (C.subgroupOf O)) ∧
      IsAlternatingNatural (s.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype) 7 := by
  obtain ⟨hCO,⟨s⟩⟩ := C27Source.star_moved_section_from_source (c.block_source_input hf)
  exact ⟨hCO,s,SourceCompletion.AlternatingSevenActor.natural_moved_of_card_gt_sixteen
    s ((subgroupOfEquivOfLe hCO).trans e)
    (a5_star_moved_card_gt_sixteen d c hf hCO s.sectionData)⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
