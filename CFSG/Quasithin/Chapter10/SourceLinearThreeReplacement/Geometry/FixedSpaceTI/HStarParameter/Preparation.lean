module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient

/-!
# The actual omega-module quotient of an original H-star subgroup

The qrc omega module is reduced. Its centralizer quotient therefore has trivial
two-core, and generation two makes the original group minimal parabolic. The
quotient is again minimal parabolic, with kernel in the literal maximal-overgroup
core. Intersecting that kernel with the prescribed Sylow gives precisely O₂(H).
The original weak closure has nontrivial image in this quotient.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756, using B.6.8 and 10.2.13.
This supplies quotient geometry; it does not identify the quotient as a wreath
product or assert the deleted-module classification.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open Chapter3.Section02 ChapterB ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The literal omega orbit regarded inside its original H-star group. -/
abbrev omegaSubgroup (T : Sylow 2 G) (H : Subgroup G) : Subgroup H :=
  (omegaModule T H).subgroupOf H

instance omegaSubgroup_normal (T : Sylow 2 G) (H : Subgroup G) :
    (omegaSubgroup T H).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

/-- The centralizer kernel is relative to H. -/
abbrev omegaKernel (T : Sylow 2 G) (H : Subgroup G) : Subgroup H :=
  centralizer (omegaSubgroup T H : Set H)

/-- The original quotient H/C_H(U), with no identification or order assumption. -/
abbrev OmegaQuotient (T : Sylow 2 G) (H : Subgroup G) := H ⧸ omegaKernel T H

theorem omegaModule_le {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) : omegaModule T H ≤ H := by
  apply conjugateSpanBy_le_self
  intro z hz
  exact hH.1.1.2 ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1

/-- The actual qrc construction gives reducedness, including the quotient core. -/
theorem omegaSubgroup_reduced {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsPReduced 2 (omegaSubgroup T H) :=
  (D.qrcHypotheses (uniqueness D) hH).sylowOmega_reduced
    (D.simpleQTKE.evenCharacteristic T)

/-- Relative centralization agrees with the ambient centralizer restricted to H. -/
theorem omegaKernel_eq {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaKernel T H = (centralizer (omegaModule T H : Set G)).subgroupOf H := by
  ext x
  constructor
  · intro hx u hu
    exact congrArg Subtype.val (hx (⟨u,omegaModule_le D hH hu⟩ : H) hu)
  · intro hx u hu
    exact Subtype.ext (hx u hu)

/-- The centralizer quotient is reduced on the actual carrier. -/
theorem omegaQuotient_twoCore_eq_bot {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    pCore 2 (OmegaQuotient T H) = ⊥ :=
  (omegaSubgroup_reduced D hH).quotient_pCore_eq_bot

/-- Nonzero original fixed space forces the relative kernel into the overlap. -/
theorem omegaKernel_le_overlap
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaKernel T H ≤ D.maximalLocal.subgroupOf H := by
  rw [omegaKernel_eq D hH]
  exact comap_mono (omegaModule_centralizer_le D hfix H)

/-- In particular H does not centralize its omega module. -/
theorem omegaKernel_ne_top
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaKernel T H ≠ ⊤ := by
  intro he
  exact hH.1.2 (subgroupOf_eq_top.mp (top_unique (he ▸ omegaKernel_le_overlap D hfix hH)))

/-- Generation two supplies the source minimal parabolic on the prescribed Sylow. -/
theorem hstar_minimal (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ :=
  source_hstar_minimal_parabolic_of_generation_gt_one D hH
    (by rw [s.generation H hH]; decide)

/-- The full centralizer kernel lies in the core of the actual maximal overlap. -/
theorem omegaKernel_le_parabolicCore (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaKernel T H ≤ minimalParabolicCore (T.subtype hH.1.1.2) (hstar_minimal D s hH) := by
  have hh := (minimalParabolic_reduced_image (T.subtype hH.1.1.2) (hstar_minimal D s hH)
    (QuotientGroup.mk' (omegaKernel T H)) (QuotientGroup.mk'_surjective _)
    (omegaQuotient_twoCore_eq_bot D hH)
    (by simpa only [QuotientGroup.ker_mk'] using omegaKernel_ne_top D hfix hH)).1
  simpa only [QuotientGroup.ker_mk'] using hh

/-- The quotient inherits minimal parabolicity through its genuine kernel. -/
theorem omegaQuotient_minimal (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsMinimalParabolicOver
      ((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H))) ⊤ := by
  apply minimalParabolic_surjective_core (T.subtype hH.1.1.2) (hstar_minimal D s hH)
  simpa only [QuotientGroup.ker_mk'] using omegaKernel_le_parabolicCore D s hfix hH

/-- The maximal Sylow overgroup in the quotient is the image of the literal overlap. -/
theorem omegaQuotient_maximal (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (D.maximalLocal.subgroupOf H).map (QuotientGroup.mk' (omegaKernel T H)) =
      minimalParabolicMax
        ((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H)))
        (omegaQuotient_minimal D s hfix hH) := by
  rw [← source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)]
  exact minimalParabolicMax_map_core (T.subtype hH.1.1.2) (hstar_minimal D s hH)
    (QuotientGroup.mk' (omegaKernel T H)) (QuotientGroup.mk'_surjective _)
    (by simpa only [QuotientGroup.ker_mk'] using omegaKernel_le_parabolicCore D s hfix hH)

/-- Only the Sylow intersection of the kernel is identified with the two-core. -/
theorem sylow_inf_omegaKernel (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    (T.subtype hH.1.1.2 : Subgroup H) ⊓ omegaKernel T H = pCore 2 H := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (omegaKernel_le_parabolicCore D s hfix hH)).trans
      (minimalParabolic_sylow_inf_core (T.subtype hH.1.1.2) (hstar_minimal D s hH)).le
  · exact le_inf (pCore_isPGroup.le_sylow_of_normal _)
      (le_centralizer_iff.mp (omegaSubgroup_reduced D hH).le_centralizer_pCore)

/-- The movement already proved by Frattini is nontriviality of the exact quotient image. -/
theorem weakClosure_quotient_image_ne_bot (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ((indexedWeakClosure D.fullModule (T : Subgroup G) 0).subgroupOf H).map
      (QuotientGroup.mk' (omegaKernel T H)) ≠ ⊥ := by
  intro he
  have hk := (Subgroup.map_eq_bot_iff _).mp he
  rw [QuotientGroup.ker_mk', omegaKernel_eq D hH] at hk
  apply weakClosure_not_centralizes_omegaModule D s hfix hH
  intro w hw
  exact hk (show (⟨w,hH.1.1.2 (indexedWeakClosure_le _ _ _ hw)⟩ : H) ∈
    (indexedWeakClosure D.fullModule (T : Subgroup G) 0).subgroupOf H from hw)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
