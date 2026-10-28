module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableSylowMaximal

/-!
# The original H-star overlap after the full centralizer reduction

For a solvable noncentral H-star member, E.2.3 gives the elementary cubic
residual of the faithful omega-orbit actor. If its centralizer is O₂(H),
the original Sylow subgroup is maximal in H. Since H is not contained in
M, its literal overlap with M is precisely T.

Solvability and the earlier full centralizer equality remain explicit
source premises. Neither follows merely from the Sylow-centralizer bound.

Source: Aschbacher--Smith 6.1.5, printed p.666, last sentence.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The original quotient by O₂(H) is the single or paired solvable actor
used in the remaining 6.1.5 argument. -/
theorem hstar_core_quotient_models_of_solvable_centralizer
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
  let hinput := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hinput.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  let := hsolv
  have hsq := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  have hsmall := ChapterE.ThompsonAction.source_solvable_whole_actor
    (T.subtype hH.1.1.2) (hinput.hstar_minimal_parabolic hH') U hU
    (hinput.hstar_thompson_moves_omega_orbit hH' hZH)
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance
  let eC := (QuotientGroup.quotientMulEquivOfEq hcentral).symm
  rcases hsmall.wreath with ⟨_,e,_⟩ | ⟨e,_,_⟩
  · exact Or.inl ⟨eC.trans e⟩
  · exact Or.inr ⟨eC.trans e⟩

/-- The source centralizer equality makes the actual Sylow maximal in H. -/
theorem hstar_sylow_isCoatom_of_solvable_centralizer
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    IsCoatom (T.subtype hH.1.1.2 : Subgroup H) := by
  let hinput := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  have hsq := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  apply ChapterE.ThompsonAction.sylow_isCoatom_of_solvable_reduced_kernel_le
    (T.subtype hH.1.1.2) (hinput.hstar_minimal_parabolic hH') _
    (hinput.hstar_omega_orbit_reduced hH')
    (hinput.hstar_thompson_moves_omega_orbit hH' hZH)
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) hsolv
  rw [hcentral]
  exact pCore_isPGroup.le_sylow_of_normal _

/-- The overlap is the original ambient Sylow, with no residual-disjointness
or subgroup-model premise. -/
theorem hstar_inf_maximal_eq_sylow_of_solvable_centralizer
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    H ⊓ M = (T : Subgroup G) := by
  have hmax := h.hstar_sylow_isCoatom_of_solvable_centralizer hout hH hZH hsolv hcentral
  have hTM : (T.subtype hH.1.1.2 : Subgroup H) ≤ M.subgroupOf H :=
    fun _ ht => h.sylow_le ht
  have hne : M.subgroupOf H ≠ ⊤ := by
    intro he
    apply hH.1.2
    intro x hx
    exact (show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from he.symm ▸ mem_top _)
  have he : M.subgroupOf H = (T.subtype hH.1.1.2 : Subgroup H) := by
    apply le_antisymm _ hTM
    by_contra hn
    exact hne (hmax.2 _ (lt_of_le_of_ne hTM (fun e => hn e.ge)))
  apply le_antisymm _ (le_inf (show (T : Subgroup G) ≤ H from hH.1.1.2)
    (show (T : Subgroup G) ≤ M from h.sylow_le))
  intro x hx
  exact (show (⟨x,hx.1⟩ : H) ∈ (T.subtype hH.1.1.2 : Subgroup H) from
    he ▸ (show (⟨x,hx.1⟩ : H) ∈ M.subgroupOf H from hx.2))

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
