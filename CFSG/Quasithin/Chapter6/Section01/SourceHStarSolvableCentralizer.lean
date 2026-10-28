module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarCubicCentralizer
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNormalizer
public import Theory.GroupTheory.PResidual.SylowKernelCentralizer

/-!
# The solvable H-star orbit centralizer and overlap

For the original noncentral H-star member, solvability suffices to prove
`C_H(⟨Ω₁(Z(T))ᴴ⟩) = O₂(H)` and `H ∩ M = T`. The cubic E.2.1 models are
constructed here from the ambient hypotheses rather than assumed.

Put `X = O²(C_H(U_H))` and `R = O₂(XT)`. The orbit centralizer normalizes
`T ∩ L`, so `T ∩ L ≤ R`. Also T normalizes R. The original rank-one
normalizer bound gives `N_G(R) ≤ M`. If R were contained in O₂(H), the
residual Sylow-kernel calculation would give equality and force `H ≤ M`,
contrary to H-star membership. E.2.3 identifies the action kernel with the
minimal-parabolic core, making this the exact second E.2.1 escape. The
resulting cubic models discharge the residual-commutator and full
centralizer inputs in the original 6.1.5 consumer.

The original natural fixed quotient from 6.1.4 and solvability remain
explicit earlier source inputs.
Source: Aschbacher--Smith 6.1.5, printed p.666; E.2.1--3 and 4.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The ambient normalizer bound supplies the precise E.2.1 escape. -/
theorem hstar_cubic_residual_models_of_solvable
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hs : Group.IsSolvable H) :
    ChapterE.SolvableMinimalParabolic.CubicResidualModels H := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let hp := hi.hstar_minimal_parabolic hH'
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let hu := hi.hstar_omega_orbit_reduced hH'
  let := hu.normal
  let := hu.elementary
  let := hs
  let C := centralizer (U : Set H)
  let X := (pResidual 2 C).map C.subtype
  let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
  let XG := X.map H.subtype
  let RG := (XG ⊔ (T : Subgroup G)).pCoreIn 2
  let TL := (T : Subgroup G) ⊓ L
  have hTC : (S : Subgroup H) ⊓ C = pCore 2 H :=
    h.hstar_omega_orbit_sylow_centralizer_eq_core hout hH hZH
  have hCN : (⊤ : Subgroup H) ≤ normalizer (C : Set H) :=
    (le_normalizer_of_normal : (⊤ : Subgroup H) ≤ normalizer (U : Set H)).trans
      (normalizer_le_normalizer_centralizer U)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hCN)
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
  have hmove := hi.hstar_thompson_moves_omega_orbit hH' hZH
  have hsmall := ChapterE.ThompsonAction.source_solvable_whole_actor S hp U hu hmove
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance
  let q := QuotientGroup.mk' C
  let : IsElementaryAbelian 3 (pResidual 2 (H ⧸ C)) := hsmall.wreath.residual_elementary
  have hkernel : ChapterB.minimalParabolicCore S hp = C :=
    (ChapterB.minimalParabolic_core_eq_kernel_of_elementary_residual S hp q
      (QuotientGroup.mk'_surjective C) hu.quotient_pCore_eq_bot
      (by rw [QuotientGroup.ker_mk']; exact fun he => hmove (le_top.trans_eq he.symm))
      inferInstance (p := 3)).trans (QuotientGroup.ker_mk' C)
  have hcoreC : C.pCoreIn 2 = pCore 2 H := by
    rw [←hkernel]
    exact ChapterE.SolvableMinimalParabolic.core_pCoreIn_eq S hp
  have hescape : ¬ centralizerModulo (S : Subgroup H)
      (ChapterB.minimalParabolicCore S hp)
      ((ChapterB.minimalParabolicCore S hp).pCoreIn 2) ≤ pCore 2 H := by
    intro hc
    have hc' : centralizerModulo (S : Subgroup H) C (pCore 2 H) ≤ pCore 2 H := by
      simpa only [hkernel,hcoreC] using hc
    exact hRnot (hRC.trans hc')
  apply ChapterE.SolvableMinimalParabolic.source_cubic_models_of_centralizer_quotient
    hsq S hp hs (Or.inr hescape) U
  rcases hsmall.wreath with ⟨_,e,_⟩ | ⟨e,_,_⟩
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

/-- The full orbit-centralizer equality with no additional cubic-model premise. -/
theorem hstar_omega_orbit_centralizer_eq_core_of_solvable
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hs : Group.IsSolvable H) :
    centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H :=
  h.hstar_omega_orbit_centralizer_eq_core_of_cubic_models hout hH hm hZH hs
    (h.hstar_cubic_residual_models_of_solvable hout hH hm hZH hs)

/-- The original p.666 overlap follows from solvability and the natural quotient. -/
theorem hstar_inf_maximal_eq_sylow_of_solvable
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hs : Group.IsSolvable H) : H ⊓ M = (T : Subgroup G) :=
  h.hstar_inf_maximal_eq_sylow_of_solvable_centralizer hout hH hZH hs
    (h.hstar_omega_orbit_centralizer_eq_core_of_solvable hout hH hm hZH hs)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
