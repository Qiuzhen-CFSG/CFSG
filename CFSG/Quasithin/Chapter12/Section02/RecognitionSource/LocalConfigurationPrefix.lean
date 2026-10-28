module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.WeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# The original local weak-closure control in 12.2.17

T-normalization identifies the Fundamental Setup's Sylow orbit with the
unchanged chosen V. The proved local-action kernel theorem then gives
C_T(V)=O₂(LT). The source uniqueness theorem controls the normalizer of
this nonzero core. Together with global TI and the elementary two-group
TI argument this supplies the full weak-closure normalizer conclusion.
An escaping H-star member therefore has a conjugate of V inside T outside
its own two-core, the first reduction of 12.2.18.
The H-star corollary uses normality of its own core only inside H.

All earlier uniqueness inputs are discharged by the proved A/C theorems.
No module model, H-star analysis or later split configuration is assumed.
Source: Aschbacher--Smith, 12.2.17, printed p.800, using 3.2.2(8) and E.3.34.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_sylow_centralizer_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
      (((structural G T L h).2.2 V D).1)) (le_componentOrbit V T)
  rw [D.fundamentalSetup_module, ho] at he
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he

theorem chosen_core_normalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (L : Set G) := by
  apply D.normal_subgroup_normalizer_le h.toHypothesis1221 (pCoreIn_le _ _) _
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  intro he
  exact D.ne_bot (bot_unique (D.le_core.trans_eq he))

theorem chosen_kernel_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) =
      {normalizer (L : Set G)} := by
  rw [chosen_sylow_centralizer_eq_core h D structural]
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  ext N
  constructor
  · rintro ⟨hN, hle⟩
    exact Set.mem_singleton_iff.mpr (huniq N hN
      (((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans hle))
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst N
    exact ⟨hm, chosen_core_normalizer_le h D⟩

theorem chosen_weakClosure_zero_local_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := D.elementary
  have hw := chosen_weakClosure_zero_centralizes h D structural hTI
  have hc := chosen_sylow_centralizer_eq_core h D structural
  refine ⟨hw.1.trans_eq hc, hc, ?_⟩
  exact SourceContainment.normalizer_weakClosure_zero_le
    ⟨D.ne_bot, D.le_sylow, ((structural G T L h).2.2 V D).1⟩ hw.2
    (chosen_kernel_unique h D structural)

/-- The first contradiction in 12.2.18: the weak closure cannot lie in
O₂(H) for an escaping H-star subgroup. -/
theorem chosen_weakClosure_not_le_hstar_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  intro hw
  have he : indexedWeakClosure V (T : Subgroup G) 0 =
      indexedWeakClosure V (H.pCoreIn 2) 0 :=
    SubgroupFamily.span_eq_in_p_overgroup (conjugateCorankFamily_invariant V 0)
      T (H.pCoreIn 2) (isPGroup_pCoreIn 2 H) hw
  have hn : H ≤ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
    rw [he]
    exact (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      (normalizer_le_weakClosure_normalizer V (H.pCoreIn 2) 0)
  exact hH.1.2 (hn.trans (chosen_weakClosure_zero_local_control h D structural hTI).2.2)

/-- Thus the original conjugacy family supplies an A=Vᵍ inside T whose
image in H/O₂(H) is nontrivial, as used in 12.2.18. -/
theorem exists_chosen_conjugate_outside_hstar_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2 := by
  classical
  by_contra hn
  apply chosen_weakClosure_not_le_hstar_core h D structural hTI hH
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra he
  exact hn ⟨g, hg, he⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
