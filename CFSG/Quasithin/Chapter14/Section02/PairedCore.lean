module
public import CFSG.Quasithin.Chapter14.Section02.OriginalMovement
public import CFSG.Quasithin.Chapter14.Section02.PairedKOne
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.LinearCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Core
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Two-core containment for the original exchanged K₁

In the quotient by the original minimal-parabolic core, the marked Bender
component is simple. The existing odd Borel argument makes the two-core
of the maximal subgroup preserve that component. C-component normalizer
lifting restores this statement on H. Since O₂(M) lies in O₂(H∩M), it
normalizes the actual K₁. This proves the nonexceptional conclusion of
14.2.12, and hence 14.2.13, in the exchanged branch.

The second subgroup uses the whole O²(H), whose image normalizes K₁
because its normalizer has index two. Together with the original movement
theorem this supplies S₂≤S, Y=[Y,S₂], the S₃ quotient and the prescribed
Sylow intersection, with no extra containment or movement premise.
Source: Aschbacher--Smith 14.2.12--14, printed pp.983--984.

The internal Structure import identifies its literal minimal-parabolic core
with the normal-core denominator in the existing marked-model interface.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

theorem marked_bender_overlap_core_normalizes
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) K f) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ normalizer (K : Set H) := by
  let N := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  obtain ⟨hPs,hJs⟩ := Structure.source_star_minimal_core_free T hP
  have hsq := Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hH T hP hs
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  have hrad : solvableRadical (H ⧸ J) = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hPs hsX).symm.trans hJs
  have ho := Structure.generating_component_orbit_eq_residual hsq.stronglyQuasithin S hi.2.1 hi.2.2.2
  have hN : ChapterB.minimalParabolicMax S hPs = N.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hcore : (N.map q).pCoreIn 2 ≤ normalizer (D : Set (H ⧸ J)) := by
    rw [←hN]
    rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,d,_⟩ | ⟨m,hm,_,d,_⟩
    · let eD := d.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F).symm
      exact Witnesses.PairedBender.core_normalizes_linear_component (by omega) hcard S hPs
        D hi.2.1 hi.2.1.isCComponent hrad ho eD
    · exact Witnesses.PairedBender.Suzuki.core_normalizes_component S hPs D hi.2.1 hrad ho (by omega) d
  have hmap := (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q N).trans hcore
  have hle := map_le_iff_le_comap.mp hmap
  rwa [normalizer_cComponent_quotient hK J] at hle

variable {G : Type*} [Group G] [Finite G]

/-- The original O₂(M) normalizes the selected exchanged Bender component. -/
theorem source_paired_M_core_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ}
    (hm : ExchangedModel ((H ⊓ M).subgroupOf H) K f) :
    M.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  obtain ⟨_,hP,hN,hsq,_,_⟩ := source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax TH hP :=
    ChapterB.minimalParabolicMax_unique TH hP hN (fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hloc := marked_bender_overlap_core_normalizes hsq TH hP hs K hK hgen (hmax ▸ hm)
  rw [←hmax] at hloc
  have hamb := (map_mono (f := H.subtype) hloc).trans (K.le_normalizer_map H.subtype)
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le inf_le_left] at hamb
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hM.1.2] using
      pCoreIn_le_sylow M (T.subtype hM.1.2)
  have hQI : M.pCoreIn 2 ≤ H ⊓ M := le_inf (hQT.trans hTH) (pCoreIn_le 2 M)
  have hQcore : M.pCoreIn 2 ≤ (H ⊓ M).pCoreIn 2 :=
    (le_inf hQI le_rfl).trans (inf_pCoreIn_le_of_le 2 (inf_le_right : H ⊓ M ≤ M))
  exact le_inf hQT (hQcore.trans hamb)

/-- Original 14.2.13--14 in the exchanged branch, on the literal second parabolic. -/
theorem source_paired_second_parabolic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ}
    (hm : ExchangedModel ((H ⊓ M).subgroupOf H) K f)
    (hi : (normalizer (K : Set H)).index = 2) :
    let Y := sourceResidual M Mc
    let S := (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype)
    M.pCoreIn 2 ≤ S ∧ Y.pCoreIn 2 ≤ S ∧ S₂ ≤ S ∧ Y = ⁅Y,S₂⁆ ∧
      Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) ∧ S ⊓ (Y ⊔ S₂) = S₂ ∧ Chapter1.IsSylowIn 2 S₂ (Y ⊔ S₂) := by
  let Y := sourceResidual M Mc
  let S := (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype)
  have hMS := source_paired_M_core_normalizes hG T hempty hM hu hmany hcard e H hH hn K hK hgen hm
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc)
  have hYS : Y.pCoreIn 2 ≤ S :=
    (pCoreIn_mono_of_normalizes (sourceResidual_le M Mc) hMY).trans hMS
  let N := normalizer (K : Set H)
  let : N.Normal := normal_of_index_eq_two hi
  have hquot : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
    rw [←Subgroup.index_eq_card,hi]
    rfl)
  have hres : pResidual 2 H ≤ N := (pResidual_le_iff_isPGroup_quotient 2 N).mpr hquot
  have hresN := (map_mono (f := H.subtype) hres).trans (K.le_normalizer_map H.subtype)
  have hRS : R ≤ S := sup_le hYS (le_inf inf_le_left (inf_le_right.trans hresN))
  obtain ⟨hmove,hmodel,hinter,hsyl⟩ := source_lemma_14_2_14 hG T hempty hM hu hmany hcard e H hH
  refine ⟨hMS,hYS,hRS,hmove,hmodel,?_,hsyl⟩
  exact le_antisymm ((inf_le_inf_right _ (inf_le_left : S ≤ (T : Subgroup G))).trans_eq hinter)
    (le_inf hRS le_sup_right)

end CFSG.Quasithin.Chapter14.Section02
