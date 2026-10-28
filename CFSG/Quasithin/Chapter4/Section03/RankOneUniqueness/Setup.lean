module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter4.Section01.OutsideSylowSelection
public import Theory.GroupTheory.SylowLocalCore

/-!
# The original rank-one uniqueness setup

The source hypotheses give uniqueness over LT and the normalized pushing-up
hypothesis 4.1.1. Failure of uniqueness over L produces C.2.8 with component
literally L; its perfect residual is not an additional subgroup. The full
omega-center module retains its section-Sylow marking and the inclusion of
the original chosen module. It is not identified with that chosen module.

Source: Aschbacher--Smith 4.2.1--4 and the opening of 4.3.2, pp.608--613.
The component exclusions in 4.3.6--16 remain separate obligations.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The genuine 1.2.7 conclusion, before the stronger 4.3.2 assertion. -/
theorem unique_sylow_join (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  have hm := hu.normalizer_maximal
  have hu := hu.normalizer_unique
  rw [he] at hm hu
  exact ⟨hm, sup_le L.le_normalizer D.sylow_normalizes_component, hu⟩

/-- The Sylow restriction in the source is the literal intersection T ∩ L. -/
theorem exists_sylow_component (D : ChosenModule T L V) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from
    le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact ⟨P, by simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hP⟩

/-- Failure over L gives the actual full-module C.2.8 counterexample. -/
theorem exists_source_C28 (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2)
        (Section02.Unitary.fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤
          Section02.Unitary.fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  have hcover : (L : Set G) ⊆ (L : Set G) * (L.pCoreIn 2 : Set G) := by
    intro x hx
    exact ⟨x, hx, 1, one_mem _, mul_one x⟩
  have hcore : L.pCoreIn 2 ≠ ⊥ :=
    fun he => D.ne_bot (bot_unique (D.le_componentCore.trans_eq he))
  obtain ⟨J,H,S,hJ,hLJ,hH,hJH,hout,hlt,hRS,hC,hm⟩ :=
    Section02.Unitary.exists_source_C28_of_not_unique h D
      (unique_sylow_join D h) L.le_normalizer hcover hcore hnot
  have hLJ' : L ≤ J := fun x hx => (hLJ.2 ⟨hx,hx⟩).1
  have hLH := hLJ'.trans hJH
  have he : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L := by
    rw [inf_eq_left.mpr hLH]
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [he] at hC
  exact ⟨J,H,S,hJ,hLJ',hH,hJH,hout,hlt,hRS,hC,hm⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
