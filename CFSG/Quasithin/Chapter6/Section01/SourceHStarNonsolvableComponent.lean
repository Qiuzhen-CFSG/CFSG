module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarReduction
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOmegaNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHStar
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNormalizer
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.NonsolvableKernel
public import Theory.GroupTheory.PResidual.SylowKernelCentralizer
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# An actual moved component in the nonsolvable H-star branch

For the original noncentral H-star member, set C=C_H(U_H), X=O²(C)
and R=O₂(XT). The natural quotient is produced from the noncentral
H-star hypothesis. It places T∩L inside the ambient image of R, hence
the original rank-one normalizer bound forces N_G(R)≤M. Consequently
R is not contained in O₂(H).

In the nonsolvable case C is the actual minimal-parabolic core, whose
image in H/O₂(H) is the Fitting subgroup. The Sylow-kernel calculation
shows that R centralizes this image. Thus its nontrivial image moves
an ordinary component, and that component lifts to an actual C-component
of H. The quotient and selected image retain the full original two-core.

This supplies a component in the remaining initial S₅ cases of 6.1.5;
it does not exclude those cases or claim the full H-star centralization.
Source: Aschbacher--Smith 6.1.5, p.666, and B.6.8(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem hstar_nonsolvable_component_structure
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let C := centralizer (U : Set H)
    let X := (pResidual 2 C).map C.subtype
    let R := (X ⊔ (T.subtype hH.1.1.2 : Subgroup H)).pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 H)
    componentLayer (H ⧸ pCore 2 H) = pResidual 2 (H ⧸ pCore 2 H) ∧
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (H ⧸ pCore 2 H) (K.map q) ∧ ⁅K.map q, R.map q⁆ ≠ ⊥ := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let hp := hi.hstar_minimal_parabolic hH'
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let hu := hi.hstar_omega_orbit_reduced hH'
  let := hu.normal
  let C := centralizer (U : Set H)
  let X := (pResidual 2 C).map C.subtype
  let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
  let XG := X.map H.subtype
  let RG := (XG ⊔ (T : Subgroup G)).pCoreIn 2
  let TL := (T : Subgroup G) ⊓ L
  have hm := h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH
  have hTC : (S : Subgroup H) ⊓ C = pCore 2 H :=
    h.hstar_omega_orbit_sylow_centralizer_eq_core hout hH hZH
  obtain ⟨hQR,hRT,_,hRC⟩ := residual_sylow_core_centralizes S C hTC
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hRmap : R.map H.subtype = RG := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective]
    congr 1
    rw [Subgroup.map_sup,hSmap]
  have hXTL : XG ≤ normalizer (TL : Set G) :=
    (map_mono (map_subtype_le (pResidual 2 C))).trans
      ((h.hstar_omega_orbit_centralizer_normalizes hH hm hZH).trans inf_le_left)
  have hTTL : (T : Subgroup G) ≤ normalizer (TL : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes_L).trans
      inf_normalizer_le_normalizer_inf
  have hTLR : TL ≤ RG := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans le_sup_right) (sup_le hXTL hTTL)
  have hRGT : RG ≤ (T : Subgroup G) := by
    rw [←hRmap,←hSmap]
    exact map_mono hRT
  have hTR : (T : Subgroup G) ≤ normalizer (RG : Set G) :=
    (show (T : Subgroup G) ≤ XG ⊔ (T : Subgroup G) from le_sup_right).trans
      ((XG ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 ↥(XG ⊔ (T : Subgroup G)))))
  have hNR : normalizer (RG : Set G) ≤ M :=
    h.maximal_eq_normalizer_L.symm ▸ hi.normalizer_le_of_sylow_normalizes hRGT hTLR hTR
  have hRnot : ¬ R ≤ pCore 2 H := by
    intro hr
    have he : R = pCore 2 H := le_antisymm hr hQR
    have heG : RG = H.pCoreIn 2 := by rw [←hRmap,he]; rfl
    have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    rw [heG] at hNR
    exact hH.1.2 (hHN.trans hNR)
  have hsq := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  have hkernel : ChapterB.minimalParabolicCore S hp = C :=
    ChapterE.ThompsonAction.nonsolvable_core_eq_centralizer hsq S hp U hu hns
      (hi.hstar_thompson_moves_omega_orbit hH' hZH)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hCF : C.map q = fittingSubgroup (H ⧸ pCore 2 H) := by
    rw [←hkernel]
    exact ChapterB.minimalParabolic_nonsolvable_coreImage_eq_fitting S hp hns
  have hRF : R.map q ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
    rw [←hCF]
    exact map_le_iff_le_comap.mpr (hRC.trans inf_le_right)
  have hne : R.map q ≠ ⊥ := by
    intro he
    exact hRnot (by simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨K,hK,hKi,hmove⟩ :=
    exists_cComponent_moved_in_twoCore_quotient R (isPGroup_pCoreIn 2 _) hne hRF
  let Q := H ⧸ pCore 2 H
  let E := componentLayer Q
  have hEne : E ≠ ⊥ := by
    intro he
    have hKb : K.map q = ⊥ := bot_unique ((show K.map q ≤ E from le_sSup hKi).trans he.le)
    exact hmove (by rw [hKb,commutator_bot_left])
  have hRE : pResidual 2 Q ≤ E := by
    rcases ChapterB.minimalParabolic_quotient_normal_dichotomy S hp E with he | he
    · have hEF : E ≤ fittingSubgroup Q :=
        he.trans (ChapterB.minimalParabolic_nonsolvable_coreImage_eq_fitting S hp hns).le
      let : Group.IsPerfect E := componentLayer_isPerfect
      let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
      exact (Group.IsPerfect.not_isSolvable E
        (Group.isSolvable_of_isSolvable_injective (inclusion_injective hEF))).elim
    · exact he
  have hER : E ≤ pResidual 2 Q := by
    let : Group.IsPerfect E := componentLayer_isPerfect
    let : Group.IsNilpotent (Q ⧸ pResidual 2 Q) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient _ _
  exact ⟨le_antisymm hER hRE,K,hK,hKi,hmove⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
