module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.CoreEquality
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# Core-component assembly for the original marked point

The global two-core calculation is complete. The original index-two
comparison RQ ≤ T restricts to the two centralizers of d. Once the point
block belongs to the local family at this smaller subgroup, source 1.2.5
provides an actual containing C-component in C_G(d), with all maps carried
through the literal subgroup inclusion.

The local-family placement and the residual commutator on the original
seed remain separate explicit source obligations. The final theorem applies
this reduction to the original factor-self-centralization consumer.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998; 1.2.3 and 1.2.5.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]
namespace MarkedPoint
variable {T : Sylow 2 G} {V L A : Subgroup G} {F : InvariantFlag T V 2}

abbrev localSylow (P : MarkedPoint F L A) : Subgroup G :=
  ((F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2) ⊓ P.globalCentralizer

end MarkedPoint

theorem source_localSylow_comparison
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    {A : Subgroup G} (P : MarkedPoint F (sourceResidual M Mc) A) :
    P.localSylow ≤ P.sylowCentralizer ∧ P.localSylow.relIndex P.sylowCentralizer ≤ 2 := by
  obtain ⟨hRT,hi⟩ := source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh
  let W := (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2
  have hWT : W ≤ (T : Subgroup G) := sup_le hRT hQT
  refine ⟨inf_le_inf_right _ hWT, ?_⟩
  change (W ⊓ P.globalCentralizer).relIndex
    ((T : Subgroup G) ⊓ P.globalCentralizer) ≤ 2
  have he : (W ⊓ P.globalCentralizer).relIndex
      ((T : Subgroup G) ⊓ P.globalCentralizer) =
      W.relIndex ((T : Subgroup G) ⊓ P.globalCentralizer) := by
    rw [← inf_relIndex_right W ((T : Subgroup G) ⊓ P.globalCentralizer),
      ← inf_assoc,inf_of_le_left hWT]
  rw [he]
  exact (relIndex_le_of_le_right inf_le_left (by rw [hi]; decide)).trans_eq hi

variable {T : Sylow 2 G} {V : Subgroup G}

/-- The remaining local-family placement, at the original RQ-centralizer. -/
def LocalFamilySource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z →
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.blockCentralizer ∈ Chapter1.L G P.localSylow

/-- The original seed and literal residual required by the chosen 1.2.11 application. -/
def ResidualCommutatorSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z →
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      z ∈ ⁅V,
        (pResidual 2 (P.globalCentralizer ⊓ normalizer (V : Set G) : Subgroup G)).map
          (P.globalCentralizer ⊓ normalizer (V : Set G)).subtype⁆

/-- Final assembly of the core and Chapter 1 enclosure, with its two remaining
source obligations explicit. This theorem does not discharge those obligations. -/
theorem coreComponentSource_of_localFamily_and_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hlocal : LocalFamilySource F (sourceResidual M Mc))
    (hcomm : ResidualCommutatorSource F (sourceResidual M Mc)) :
    CoreComponentSource F (sourceResidual M Mc) := by
  intro A hA hlt P z hz hgeom hSylow
  have hcore := source_global_core_eq hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs A hA hlt P z hz hSylow
  have hS := source_localSylow_comparison hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs P
  have hR : P.localSylow ≤ P.globalCentralizer := inf_le_right
  have hB : P.blockCentralizer ≤ P.globalCentralizer := inf_le_right
  have hl := (Chapter1.mem_LIn_iff_subgroupOf hR hB).mp
    ⟨hB,hlocal A hA hlt P z hz hgeom hSylow⟩
  have hzcomm := hcomm A hA hlt P z hz hgeom hSylow
  obtain ⟨S,hSmap⟩ := hSylow
  have hRS : P.localSylow.subgroupOf P.globalCentralizer ≤ (S : Subgroup P.globalCentralizer) := by
    have hh := comap_mono (f := P.globalCentralizer.subtype) hS.1
    rw [← hSmap,comap_map_eq_self_of_injective P.globalCentralizer.subtype_injective] at hh
    exact hh
  have hi : (P.localSylow.subgroupOf P.globalCentralizer).relIndex
      (S : Subgroup P.globalCentralizer) ≤ 2 := by
    rw [← relIndex_map_map_of_injective _ _ P.globalCentralizer.subtype_injective,
      map_subgroupOf_eq_of_le hR,hSmap]
    exact hS.2
  have hH : P.globalCentralizer ∈ Chapter1.H G := by
    change P.globalCentralizer.pCoreIn 2 ≠ ⊥
    rw [hcore]
    exact zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  obtain ⟨B,hBcomp,_⟩ := Chapter1.Section02.index_le_two_local_component_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH) S hRS hi hl
  refine ⟨hcore,⟨B.map P.globalCentralizer.subtype,⟨map_subtype_le _,?_⟩,?_⟩,
    hzcomm⟩
  · change ((B.map P.globalCentralizer.subtype).comap P.globalCentralizer.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective P.globalCentralizer.subtype_injective]
    exact hBcomp.1
  · have hh := map_mono (f := P.globalCentralizer.subtype) hBcomp.2
    rwa [map_subgroupOf_eq_of_le hB] at hh

/-- Apply the completed core calculation and enclosure reduction to the
original factor-self-centralization consumer. -/
theorem factorSelfCentralizing_of_core_leaves
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hgeometry : FourCenterSource F (sourceResidual M Mc))
    (hlocal : LocalFamilySource F (sourceResidual M Mc))
    (hcomm : ResidualCommutatorSource F (sourceResidual M Mc))
    (hexclude : ModelExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) := by
  exact factorSelfCentralizing_of_source_inputs hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs hgeometry
    (coreComponentSource_of_localFamily_and_commutator hG T hempty hM hu hmany hcard e
      hnot F hne g hgP hgH hs hlocal hcomm) hexclude

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
