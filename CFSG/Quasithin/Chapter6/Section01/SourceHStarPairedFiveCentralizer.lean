module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarPairLinearExcluded
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.NonsolvableKernel
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMarking
public import Theory.GroupTheory.CComponent.OrbitCorrespondence

/-!
# The full centralizer kernel in the paired marked-five H-star row

Both original marked alternating axes lift to actual C-components. A normal
generating component would contain every C-component in its Sylow conjugacy
orbit, identifying these two distinct marked images. The generating component
is therefore nonnormal, and the original paired-core theorem gives that the
minimal-parabolic core is the two-core. The nonsolvable reduced-action kernel
theorem identifies that same core with the full original orbit centralizer.

The argument retains the entire odd central kernel until the paired-core
theorem removes it. It establishes the kernel equality, not a row exclusion.
Source: Aschbacher--Smith E.2.2--3 and 6.1.5, pp.215--217 and666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterE.ThompsonAction
open CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The original paired marked S5 row has exactly the original two-core as
its full omega-orbit centralizer. No factor exchange or replacement quotient
is assumed. -/
theorem hstar_paired_five_centralizer_eq_core
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hns : ¬ Group.IsSolvable H)
    (hpair :
      let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
      letI : U.Normal := (RankOneGeneric.Input.hstar_omega_orbit_reduced
        (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
      letI : IsElementaryAbelian 2 U := (RankOneGeneric.Input.hstar_omega_orbit_reduced
        (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
      let C := centralizer (U : Set H)
      let q := QuotientGroup.mk' C
      let α : Representation (ZMod 2) (H ⧸ C) (Additive U) :=
        NormalElementaryQuotient.representation U q
          (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      let Y := offenderSubgroup α
      ∃ d : SourceTwoFactorCase (α.comp Y.subtype),
        Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) :
    centralizer
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H : Set H) =
        pCore 2 H := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hi.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α : Representation (ZMod 2) (H ⧸ C) (Additive U) :=
    NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hp := hi.hstar_minimal_parabolic hH'
  have hJ := hi.hstar_thompson_moves_omega_orbit hH' hZH
  have hsq : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  obtain ⟨d, ⟨c⟩⟩ := hpair
  let e := c.action.groupEquiv
  let e' := e.trans MulEquiv.prodComm
  let A := (alternatingGroup (Fin 5)).map (ChapterC.SymmetricFive.Paired.leftFactorMap Y e)
  let B := (alternatingGroup (Fin 5)).map (ChapterC.SymmetricFive.Paired.leftFactorMap Y e')
  have hA : IsComponent (H ⧸ C) A := ChapterC.SymmetricFive.Paired.leftFactorMap_component Y e
  have hB : IsComponent (H ⧸ C) B := ChapterC.SymmetricFive.Paired.leftFactorMap_component Y e'
  let eA : A ≃* alternatingGroup (Fin 5) :=
    ((alternatingGroup (Fin 5)).equivMapOfInjective _
      (ChapterC.SymmetricFive.Paired.leftFactorMap_injective Y e)).symm
  let eB : B ≃* alternatingGroup (Fin 5) :=
    ((alternatingGroup (Fin 5)).equivMapOfInjective _
      (ChapterC.SymmetricFive.Paired.leftFactorMap_injective Y e')).symm
  have hAB : A ≠ B := by
    intro hab
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    have hx : ChapterC.SymmetricFive.Paired.leftFactorMap Y e (a : Equiv.Perm (Fin 5)) ∈ B :=
      hab ▸ mem_map_of_mem _ a.property
    obtain ⟨b, _, hb⟩ := hx
    change ((e.symm (1, b) : Y) : H ⧸ C) =
      ((e.symm ((a : Equiv.Perm (Fin 5)), 1) : Y) : H ⧸ C) at hb
    have heq := e.symm.injective (Subtype.ext hb)
    exact ha (Subtype.ext (congrArg Prod.fst heq).symm)
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  obtain ⟨K₁, hK₁, hm₁, _, _, _⟩ := exists_five_component_of_reduced_module
    h36 hsq S hp U hU hJ q (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C) hns A hA eA
  obtain ⟨K₂, hK₂, hm₂, _, _, _⟩ := exists_five_component_of_reduced_module
    h36 hsq S hp U hU hJ q (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C) hns B hB eB
  obtain ⟨K, hK, hqK, hgen, _⟩ := ChapterE.Structure.source_original_component hsq S hp hns
  have hn : ¬ K.Normal := by
    intro hn
    let := hn
    have hu (D : Subgroup H) (hD : D.IsCComponent) : D = K := by
      obtain ⟨s, hs⟩ := hK.conjugate_of_pGroup_generated hD S.isPGroup' hgen
      apply hs.trans
      apply mem_normalizer_iff_map_conj_eq.mp
      rw [normalizer_eq_top]
      exact mem_top _
    apply hAB
    rw [← hm₁, ← hm₂, hu K₁ hK₁, hu K₂ hK₂]
  have hcore := ChapterE.Structure.PairedCore.source
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    hsq S hp hns hK hqK hgen hn
  exact (nonsolvable_core_eq_centralizer hsq S hp U hU hns hJ).symm.trans hcore

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
