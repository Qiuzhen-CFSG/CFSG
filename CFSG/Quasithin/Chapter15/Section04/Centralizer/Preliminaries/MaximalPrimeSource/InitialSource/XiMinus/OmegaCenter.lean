module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Setup
public import Theory.GroupTheory.ReducedNormal.SylowCentralizer
public import Stellmacher.OmegaOneCenterMap

/-!
# The omega-center and original normalizer in the Xi-minus argument

The exact Sylow centralizer C_T(V)=O₂(XT) transfers reducedness from V to
Ω₁(Z(O₂(XT))). Maximality of R₂(XT) then gives equality. Consequently the
original module [R₂(XT),X], embedded in G, is preserved by
N_G(X) ∩ N_G(O₂(XT)). All core inclusions and conjugations are the literal ones.

The earlier reducedness and Sylow-centralizer premises remain with the
ReducedAction source owner. The factor decomposition and Frattini-normalizer
transport are separate steps of the full Xi-minus assembly.
Source: Aschbacher–Smith, Lemma 3.2.13, printed pp.584–585.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Theory.GroupTheory Stellmacher
universe u
variable {G : Type u} [Group G]

private theorem normalizes_omegaCenter (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (omegaOneCenterAmbient Q : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    (mem_normalizer_iff_map_conj_eq).mp hg]

private theorem reduced_le_omegaCenter :
    reducedTwoSubgroup G ≤ omegaOneCenterAmbient (pCore 2 G) := by
  let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
  intro v hv
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨reducedPSubgroup_le_pCore 2 G hv,
      elemPow_eq_one_of_isElementaryAbelian v hv,
      reducedPSubgroup_le_centralizer_pCore 2 G hv⟩

variable [Finite G] (T : Sylow 2 G) (X : Subgroup G)

/-- The original reduced subgroup equals the omega-center of O₂(XT), using
the reducedness and exact Sylow centralizer supplied by the earlier module step. -/
theorem source_reduced_eq_omegaCenter
    (hV : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hC : (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
        centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
      pCore 2 (sourceGroup (T : Subgroup G) X)) :
    reducedTwoSubgroup (sourceGroup (T : Subgroup G) X) =
      omegaOneCenterAmbient (pCore 2 (sourceGroup (T : Subgroup G) X)) := by
  let J := sourceGroup (T : Subgroup G) X
  let R := pCore 2 J
  let W := omegaOneCenterAmbient R
  let : W.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (by simpa only [normalizer_eq_top] using normalizes_omegaCenter R))
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian R
  have hr : reducedTwoSubgroup J ≤ W := reduced_le_omegaCenter
  have hW : IsPReduced 2 W := hV.of_le_of_sylow_centralizer_le
    (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    ((sourceModule_le_reduced _ _).trans hr) (by
      change (T : Subgroup G).subgroupOf J ⊓
        centralizer (sourceModule (T : Subgroup G) X : Set J) ≤ centralizer (W : Set J)
      rw [hC]
      intro r hr w hw
      exact ((mem_omegaOneCenterAmbient_iff R w).mp hw).2.2 r hr |>.symm)
  exact le_antisymm hr hW.le_reducedPSubgroup

/-- The original module, embedded in G, is the commutator of the actual
ambient omega-center with X. -/
theorem sourceModule_map_eq_omega_commutator
    (hV : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hC : (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
        centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
      pCore 2 (sourceGroup (T : Subgroup G) X)) :
    (sourceModule (T : Subgroup G) X).map (sourceGroup (T : Subgroup G) X).subtype =
      ⁅omegaOneCenterAmbient ((sourceGroup (T : Subgroup G) X).pCoreIn 2), X⁆ := by
  rw [sourceModule, source_reduced_eq_omegaCenter T X hV hC, map_commutator,
    ← omegaOneCenterAmbient_map_injective _ (sourceGroup (T : Subgroup G) X).subtype_injective,
    map_subgroupOf_eq_of_le (show X ≤ sourceGroup (T : Subgroup G) X from le_sup_left)]
  rfl

/-- The original H = N_G(X) ∩ N_G(O₂(XT)) normalizes the original module.
No normalization of T or XT by H is required. -/
theorem source_normalizer_core_normalizes_module
    (hV : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hC : (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
        centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
      pCore 2 (sourceGroup (T : Subgroup G) X)) :
    normalizer (X : Set G) ⊓
        normalizer ((sourceGroup (T : Subgroup G) X).pCoreIn 2 : Set G) ≤
      normalizer ((sourceModule (T : Subgroup G) X).map
        (sourceGroup (T : Subgroup G) X).subtype : Set G) := by
  rw [sourceModule_map_eq_omega_commutator T X hV hC]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    (mem_normalizer_iff_map_conj_eq).mp (normalizes_omegaCenter _ hg.2),
    (mem_normalizer_iff_map_conj_eq).mp hg.1]

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
