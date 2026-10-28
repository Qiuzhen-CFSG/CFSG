module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.ChapterE.Section06.Basic

/-!
# E.6.1 for the original chosen module

The original local uniqueness theorem, the structural TI conclusion and
the exact equality C_T(U)=O₂(KT) give E.6.1 with M=N_G(K). This prepares
the contained-centralizer branch of 12.7.10 without assuming a rank bound.
The construction applies to every chosen module in the original setup.

Source: Aschbacher–Smith, 12.2.2, 12.2.6 and 12.7.10(2), using E.6.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal original U and N_G(K) satisfy the earlier obstruction setup. -/
theorem original_chosen_hypothesisE61_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (K : Set G)) U := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hTU := ((structural K h).2.2 U D).1
  have ho : componentOrbit U (T : Subgroup G) = U :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer U T U le_rfl hTU)
      (le_componentOrbit U T)
  have hc : (T : Subgroup G) ⊓ centralizer (U : Set G) =
      (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
    have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
    rw [D.fundamentalSetup_module, ho] at he
    simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he
  have hm : IsMaximalTwoLocal (normalizer (K : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  refine ⟨h.simpleQTKE, hm, D.sylow_normalizes_component, D.ne_bot,
    D.elementary, D.le_sylow, (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr hTU,
    ((structural K h).2.2 U D).2.2.1, ?_⟩
  intro N hN hle
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      K ⊔ (T : Subgroup G) ≤ N → N = normalizer (K : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  apply huniq N hN
  apply le_trans ?_ hle
  refine le_inf (le_inf (sup_le K.le_normalizer D.sylow_normalizes_component)
    (sup_le D.normalizes hTU)) ?_
  change K ⊔ (T : Subgroup G) ≤ normalizer
    (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G)
  rw [hc]
  exact (K ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

end CFSG.Quasithin.Chapter12.Section07
