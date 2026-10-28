module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Transfers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure.ConjugateSpan

/-!
# Normalizer control after zeroth centralization

The original chosen module and the Sylow marking identify C_T(V) with
O₂(LT). If W₀ centralizes V, its weak closure inside that characteristic
core equals W₀(T,V). Thus LT normalizes the nontrivial W₀, and the earlier
local uniqueness theorem puts its full normalizer in M=N_G(L). The same
centralization excludes zero from the defining minimum of w.

The centralization premise is supplied by Zero after the exterior geometry
and symmetry argument. No numerical parameter premise is used here.
Source: Aschbacher--Smith, 12.5.7, printed p.820, using E.3.34(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The literal source kernel C_T(V)=O₂(LT), using the given aligned marking. -/
theorem exterior_sylow_centralizer_eq_core (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
      (le_sup_right.trans s.normalizes)) (le_componentOrbit V T)
  rw [D.fundamentalSetup_module, ho] at he
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he

/-- Positive w and the full W₀-normalizer bound follow from zeroth centralization. -/
theorem zero_bounds_of_centralizes (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G)) :
    0 < globalW V (T : Subgroup G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ s.marking.M := by
  have hwT := indexedWeakClosure_le V (T : Subgroup G) 0
  have hwC := le_inf hwT hw
  have hWQ : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← exterior_sylow_centralizer_eq_core s h]
    exact hwC
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [← exterior_sylow_centralizer_eq_core s h]
    exact inf_le_left
  have heQ := weakClosure_eq_of_le_of_closure_le V
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) (T : Subgroup G) 0 hQT hWQ
  have hn : L ⊔ (T : Subgroup G) ≤
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
    rw [← heQ]
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans
      (normalizer_le_weakClosure_normalizer _ _ _)
  have hne : indexedWeakClosure V (T : Subgroup G) 0 ≠ ⊥ := by
    intro he
    exact D.ne_bot (bot_unique (he ▸ self_le_weakClosure_zero D.le_sylow))
  refine ⟨?_, D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hwT.trans le_sup_right) hne hn⟩
  apply bot_lt_iff_ne_bot.mpr
  intro he
  exact globalW_attained (n := 0) he hwC

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
