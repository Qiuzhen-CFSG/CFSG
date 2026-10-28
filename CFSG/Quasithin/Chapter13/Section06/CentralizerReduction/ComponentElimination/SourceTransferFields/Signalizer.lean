module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Normalizer
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Comparison
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families

/-!
# Signalizer transfer into the centralizer two-core

A.4.8 gives A.4.9 for the literal embedded cores of a subnormal pair.
In the join K O₂(C_G(a)), this detects a moving omega-center once the
intrinsic K-module is nontrivial. Characteristic two in C_G(a) places
that omega-center inside Ω₁(Z(O₂(C_G(a)))), transferring the movement.

The application consumes the proved small-index normalizer calculation.
The earlier intrinsic-module nontriviality and characteristic-two facts
remain explicit. It does not assert the later faithful-component
construction or the final noncentrality conclusion of 13.6.17.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.4.9,
printed p.60, and Lemma 13.6.17, printed pp.930–931.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ChapterA.Section04 Chapter1.Section02.Adequate A5Module ComponentSelection
variable {G : Type*} [Group G] [Finite G]

theorem intrinsic_ne_bot_iff_core_module_ne_bot (X H : Subgroup G)
    (hXH : X ≤ H) (hs : (X.subgroupOf H).IsSubnormal) (hX : IsPPerfect 2 X) :
    intrinsicSignalizerModule X ≠ ⊥ ↔ signalizerModule X (H.pCoreIn 2) ≠ ⊥ := by
  have hn : X ≤ normalizer (H.pCoreIn 2 : Set G) := hXH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore H))
  have hsig : IsTwoSignalizer X H (H.pCoreIn 2) :=
    (isTwoSignalizer_iff _ _ _).mpr ⟨pCoreIn_le 2 H, isPGroup_pCoreIn 2 H, hn⟩
  exact (signalizerModule_ne_bot_iff_intrinsic X (H.pCoreIn 2) hX
    (isPGroup_pCoreIn 2 H) hn
    (pCoreAmbient_mono_of_isSubnormalIn X H 2 hXH hs)
    (signalizer_commutator_le_pCore X H (H.pCoreIn 2) hXH hs hX hsig)).symm

omit [Finite G] in
private theorem core_omega_le_of_selfCentralizing (H M : Subgroup G)
    (hHM : H ≤ M) (hQH : M.pCoreIn 2 ≤ H)
    (hM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    omegaOneCenterAmbient (H.pCoreIn 2) ≤ omegaOneCenterAmbient (M.pCoreIn 2) := by
  have hn : H ≤ normalizer (M.pCoreIn 2 : Set G) := hHM.trans
    (M.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore M))
  have hQQ : M.pCoreIn 2 ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) hQH hn
  intro x hx
  obtain ⟨hxH, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
  have hxM := hHM (pCoreIn_le 2 H hxH)
  have hfix : (⟨x, hxM⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
    intro y hy
    exact Subtype.ext (hxc (y : G) (hQQ (mem_map_of_mem _ hy)))
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨mem_map.mpr ⟨⟨x, hxM⟩, hM hfix, rfl⟩, hx2, fun y hy => hxc y (hQQ hy)⟩

/-- A.4.9 in the actual join, followed by characteristic two in C_G(a).
The intrinsic-module premise is earlier source data; it is not a
noncentrality or component-transfer premise. -/
theorem moves_centralizer_core_of_intrinsic_module
    (T : Sylow 2 G) (L K : Subgroup G) (z v : G) (a : Gv v)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hv : v ^ 2 = 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (ha : checkedQuotientMap v a ∈ centralizer
      (checkedImage v (Tv (T : Subgroup G) v) : Set (Gcheck v)))
    (hKa : K ≤ Gv (a : G))
    (hfaith : intrinsicSignalizerModule K ≠ ⊥)
    (hchar : centralizer (pCore 2 (Gv (a : G)) : Set (Gv (a : G))) ≤
      pCore 2 (Gv (a : G))) :
    ¬ K ≤ centralizer (omegaOneCenterAmbient (Qv (a : G)) : Set G) := by
  let H := K ⊔ Qv (a : G)
  have hnorm : (K.subgroupOf H).Normal :=
    normal_in_sup_twoCore_of_checked_centralizes T L K z v a hK hv hidx hTK ha hKa
  have hmove := (intrinsic_ne_bot_iff_core_module_ne_bot K H le_sup_left
    hnorm.isSubnormal (mem_L_isPPerfect hK.1.2)).mp hfaith
  have hle := core_omega_le_of_selfCentralizing H (Gv (a : G))
    (sup_le hKa (pCoreIn_le 2 (Gv (a : G)))) le_sup_right hchar
  intro hc
  apply hmove
  rw [signalizerModule_eq_commutator_omegaCenter]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (centralizer_le hle))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
