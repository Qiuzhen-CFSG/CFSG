module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterTransvection
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.Commutator.SylowFixedSeed

/-!
# Residual generation by the actual moving A₅ actor

The HStar group in the positive fixed-center case is minimal parabolic.
A moving Sylow actor cannot have its normal closure inside the parabolic
core: its intersection with the Sylow subgroup is the two-core, which
centralizes the reduced module. The minimal-parabolic residual dichotomy
therefore places O²(H) inside that normal closure. Since the Sylow center
is fixed by the Sylow supplement, both actors have the same displacement
on its H-orbit span.

The final theorem applies this to the transvection selected from the actual
FundamentalSetup; no normalization of the original A₅ block is assumed.
Source: Aschbacher--Smith, proof of 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The actual HStar group is intrinsically minimal parabolic over its Sylow. -/
theorem source_a5_HStar_minimal_parabolic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hNT : normalizer ((T : Subgroup G) : Set G) ≤ D.maximalLocal :=
    source_a5_normalizer_le_of_orbit_intersection_le D e hn T le_rfl
      (T : Subgroup G).le_normalizer inf_le_left
  apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
  refine ⟨?_,?_⟩
  · obtain ⟨B,⟨hBc,hBT⟩,hb⟩ := Chapter3.HStar.unique_maximal_subgroup T
      (le_normalizer_componentOrbit L T) hH
    refine ⟨B,⟨hBc,?_⟩,?_⟩
    · intro s hs
      obtain ⟨b,hb,he⟩ := hBT hs
      exact H.subtype_injective he ▸ hb
    · intro C hC
      apply hb C
      refine ⟨hC.1,?_⟩
      intro t ht
      exact ⟨⟨t,hH.1.1.2 ht⟩,hC.2 ht,rfl⟩
  · exact ((ChapterB.isMinimalParabolicOver_iff T H).mp
      (Chapter3.HStar.minimalParabolic T (le_normalizer_componentOrbit L T) hH (Or.inl hNT))).2

/-- A moving Sylow actor generates the odd residual normally and all displacement. -/
theorem source_a5_moving_actor_residual_generation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (W : Subgroup G) (hW : W = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hred : IsPReduced 2 (W.subgroupOf H)) (g : H) (hg : (g:G) ∈ (T : Subgroup G))
    (hmove : ∃ x ∈ W, ⁅(g:G),x⁆ ≠ 1) :
    pResidual 2 H ≤ normalClosure ({g} : Set H) ∧
      ⁅W,H⁆ = ⁅W,(normalClosure ({g} : Set H)).map H.subtype⁆ := by
  let S := T.subtype hH.1.1.2
  have hP := source_a5_HStar_minimal_parabolic D e hn H hH
  let N := normalClosure ({g} : Set H)
  have hgN : g ∈ N := subset_normalClosure (Set.mem_singleton _)
  have hnot : ¬ N ≤ ChapterB.minimalParabolicCore S hP := by
    intro hh
    have hgcore : g ∈ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hP]
      exact ⟨hg,hh hgN⟩
    obtain ⟨x,hx,hxne⟩ := hmove
    have hWH : W ≤ H := by
      rw [hW]
      exact conjugateSpanBy_le_self
        ((map_subtype_le _).trans hH.1.1.2)
    have hh := (hred.le_centralizer_pCore (show (⟨x,hWH hx⟩ : H) ∈ W.subgroupOf H from hx)) g hgcore
    apply hxne
    exact commutatorElement_eq_one_iff_mul_comm.mpr (congrArg H.subtype hh)
  have hres := (ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy S hP N).resolve_left hnot
  refine ⟨hres,?_⟩
  have hgen : H ≤ N.map H.subtype ⊔ (T : Subgroup G) := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top S)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rw [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    exact hh.ge.trans (sup_le_sup (map_mono hres) le_rfl)
  rw [hW]
  apply commutator_conjugateSpan_eq_of_fixed_supplement _ H H (N.map H.subtype) T
    ((map_subtype_le _).trans hH.1.1.2) (map_subtype_le _) hH.1.1.2
    H.le_normalizer ?_ (map_subtype_le _) hgen
  · intro z hz t ht
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht
  · intro x hx
    apply N.le_normalizer_map H.subtype
    exact ⟨⟨x,hx⟩,by rw [N.normalizer_eq_top]; trivial,rfl⟩
/-- The source transvection comes with its actual residual-generation contract. -/
theorem source_exists_fixed_center_transvection_with_residual_generation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
      H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
       W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
       IsPReduced 2 (W.subgroupOf H) ∧
       ∃ g : H, (g : G) ∈ (T : Subgroup G) ⊓ localOrbit T L ∧
         ∃ v ∈ W, v ≠ 1 ∧
         (∀ x ∈ W, ⁅(g:G),x⁆ = 1 ∨ ⁅(g:G),x⁆ = v) ∧
         (∃ x ∈ W, ⁅(g:G),x⁆ = v) ∧
         pResidual 2 H ≤ normalClosure ({g} : Set H) ∧
         ⁅W,H⁆ = ⁅W,(normalClosure ({g} : Set H)).map H.subtype⁆) := by
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,v,hv,hvne,hline,x,hx,he⟩ :=
    source_exists_fixed_center_transvection D e hn hne hout
  let gH : H := ⟨g,hH.1.1.2 hg.1⟩
  obtain ⟨hres,hdisp⟩ := source_a5_moving_actor_residual_generation D e hn H hH
    _ rfl hred gH hg.1 ⟨x,hx,fun hh => hvne (he.symm.trans hh)⟩
  exact ⟨H,hH,hHN,hWE,hred,gH,hg,v,hv,hvne,hline,⟨x,hx,he⟩,hres,hdisp⟩
end CFSG.Quasithin.Chapter10
