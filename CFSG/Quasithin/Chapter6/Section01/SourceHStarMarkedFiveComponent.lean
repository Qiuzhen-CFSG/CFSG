module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarPairLinearExcluded
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarNonsolvableComponent
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarResidualExtraction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveComponent
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveWhole

/-!
# Actual components in the marked symmetric-five H-star rows

The marked single row is first converted to the whole original `S₅` quotient.
The selected-rank-one component theorem is then applied to that quotient.  The
kernel in the resulting quotient map is the literal centralizer of the
original omega orbit, so no odd central kernel is discarded.  The paired row
is retained as the paired marked source; its cubic and terminal exclusions
belong to the next source step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.ThompsonAction
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The singleton marked `S₅` row gives the actual residual component in the
original covering group.  The paired marked row is carried forward unchanged.
The component statement is deliberately made before any cubic-factor or
natural-section selection, so those remaining source obligations are visible
to later consumers. -/
theorem hstar_marked_five_component_or_pair
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hns : ¬ Group.IsSolvable H) :
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
    let Y : Subgroup (H ⧸ C) := offenderSubgroup α
    let σ : Representation (ZMod 2) Y (Additive U) := α.comp Y.subtype
    (componentLayer (H ⧸ pCore 2 H) = pResidual 2 (H ⧸ pCore 2 H)) ∧
    ((∃ p : H →* Equiv.Perm (Fin 5),
        p.ker = C ∧ Function.Surjective p ∧ (pResidual 2 H).IsCComponent ∧
          Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
            alternatingGroup (Fin 5)) ∧ C = pCore 2 H) ∨
      ∃ d : SourceTwoFactorCase σ,
        Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
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
  let Y : Subgroup (H ⧸ C) := offenderSubgroup α
  let σ : Representation (ZMod 2) Y (Additive U) := α.comp Y.subtype
  have hp := hi.hstar_minimal_parabolic hH'
  have hJ := hi.hstar_thompson_moves_omega_orbit hH' hZH
  have hsq : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  have hsource := h.hstar_nonsolvable_component_structure hout hH hZH hns
  refine ⟨hsource.1, ?_⟩
  have hrows := h.e23_nonsolvable_symmetric_five_rows hout hH hZH hns
  rcases hrows with hsingle | hpair
  · rcases hsingle with ⟨hqs, ⟨c, ⟨e⟩⟩⟩
    let e0 : MarkedActionEquiv c.sectionData.action
        (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
        (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)) := e
    obtain ⟨p, hpSurj, hpk, f, hf, he, hfk⟩ :=
      quasisimple_five_whole_quotient S hp U hU hJ q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs
        c.sectionData e0
    have hfive :=
      CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.symmetric_five_residual_component
        (ChapterA.SQTKStructure.a36Input_of_theoremsAC
          (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
          (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
        hsq S hp U hU hJ
        p hpSurj hpk
    obtain ⟨eQ⟩ := hfive.2
    let : IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
      IsQuasisimple.of_mulEquiv eQ.symm
    have him : (pResidual 2 H).map p = alternatingGroup (Fin 5) := by
      rw [map_pResidual_of_surjective 2 p hpSurj, Equiv.Perm.twoResidual_eq_alternating]
    let rmap : pResidual 2 H →* alternatingGroup (Fin 5) :=
      (MulEquiv.subgroupCongr him).toMonoidHom.comp (p.subgroupMap (pResidual 2 H))
    have hrmap : Function.Surjective rmap :=
      (MulEquiv.subgroupCongr him).surjective.comp
        (p.subgroupMap_surjective (pResidual 2 H))
    obtain ⟨eR, heR⟩ :=
      CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.five_core_quotient_equiv
        rmap hrmap
    have hRC : (pResidual 2 H) ⊓ C ≤ pCore 2 H := by
      intro x hx
      let xr : pResidual 2 H := ⟨(x : H), hx.1⟩
      have hxC : (xr : H) ∈ C := hx.2
      have hpx : p (xr : H) = 1 := by
        exact MonoidHom.mem_ker.mp (hpk.symm ▸ hxC)
      have hmk : QuotientGroup.mk' (pCore 2 (pResidual 2 H)) xr = 1 := by
        apply eR.injective
        calc
          eR (QuotientGroup.mk' (pCore 2 (pResidual 2 H)) xr) = rmap xr := heR xr
          _ = 1 := by
            have hsub : (p.subgroupMap (pResidual 2 H)) xr = 1 := by
              apply Subtype.ext
              exact hpx
            change (MulEquiv.subgroupCongr him) ((p.subgroupMap (pResidual 2 H)) xr) = 1
            rw [hsub]
            exact (MulEquiv.subgroupCongr him).map_one
          _ = eR 1 := (eR.map_one).symm
      have hxr : xr ∈ pCore 2 (pResidual 2 H) :=
        (QuotientGroup.eq_one_iff (N := pCore 2 (pResidual 2 H)) xr).mp hmk
      have hpc : pCore 2 (pResidual 2 H) =
          (pCore 2 H).comap (pResidual 2 H).subtype :=
        pCore_subnormal_eq_comap 2 hfive.1.subnormal
      have hxrH : (xr : H) ∈ pCore 2 H := by
        change xr ∈ (pCore 2 H).comap (pResidual 2 H).subtype
        rw [← hpc]
        exact hxr
      simpa [xr] using hxrH
    let X := (pResidual 2 C).map C.subtype
    have hXle : X ≤ pCore 2 H := by
      apply (le_inf (map_pResidual_le 2 C.subtype) (map_subtype_le (pResidual 2 C))).trans
      exact hRC
    have hCeq : C = pCore 2 H := by
      apply le_antisymm
      · by_contra hne
        have hne' : C ≠ pCore 2 H := fun heq => hne heq.le
        obtain ⟨hYne, _, _, _, _, _, _⟩ :=
          h.hstar_omega_orbit_residual_extraction hout hH hZH
            (by simpa [C, U] using hne')
        have hXne : X ≠ ⊥ := by
          intro hXbot
          apply hYne
          exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mpr hXbot
        have hXbot : X = ⊥ := by
          have hfX := IsPPerfect.hom_eq_one_of_isPGroup
            (isPPerfect_embedded_pResidual 2 C) pCore_isPGroup
            (Subgroup.inclusion hXle)
          apply _root_.eq_bot_iff.mpr
          intro x hx
          have hx0 : (Subgroup.inclusion hXle) ⟨x, hx⟩ = 1 := by
            rw [hfX]
            rfl
          exact congrArg Subtype.val hx0
        exact hXne hXbot
      · exact le_centralizer_iff.mp hU.le_centralizer_pCore
    exact Or.inl ⟨p, hpk, hpSurj, hfive.1, hfive.2, hCeq⟩
  · exact Or.inr hpair

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
