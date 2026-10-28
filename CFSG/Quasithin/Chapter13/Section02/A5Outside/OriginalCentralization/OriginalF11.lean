module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCenters
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel

/-!
# The actual original alternating-five pair satisfies F.1.1

The two original omega splittings make each local Borel centralize the
whole Sylow omega-center. When that center has order four, each component
has a nontrivial fixed line. Uniqueness of its maximal two-local overgroup
therefore makes the opposite Borel normalize that component.

The whole two-core of the generated group is a common normal subgroup of
the original Sylow and is trivial. Each full parabolic normalizes the
nontrivial original component core; even characteristic supplies its
characteristic-two property. These are all the literal F.1.1 fields.
No Borel is assumed to normalize the Sylow, and no core order is bounded.

Source: Aschbacher--Smith 13.2.4(2b), 13.2.8(1), 1.1.4(6), and 1.2.7,
printed pp.879--880 and 505--507, with Hypothesis F.1.1, p.259.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

private theorem borel_centralizes_omega
    (d : Context T L V V₁ V₂ V₃)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterF.Source.borel L (T : Subgroup G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mp
  rw [omega_decomposition_of_thompson_moves d hJ]
  apply sup_le
  · rw [d.borel_eq_point_centralizer]
    exact le_centralizer_iff.mp inf_le_right
  · exact inf_le_right.trans (centralizer_le
      ((d.borel_eq_point_centralizer.le).trans inf_le_left))

private theorem fixed_omega_ne_bot
    (d : Context T L V V₁ V₂ V₃)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hz
  have he := omega_decomposition_of_thompson_moves d hJ
  rw [hz,sup_bot_eq] at he
  have hc := congrArg (fun A : Subgroup G => Nat.card A) he
  rw [hfour,d.flag.one_card] at hc
  contradiction

private theorem cross_borel
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    ChapterF.Source.borel K (T : Subgroup G) ≤ normalizer (L : Set G) := by
  let C := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hCT : C ≤ (T : Subgroup G) := fun _ hx =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).1
  have hTC : (T : Subgroup G) ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (fun _ hx =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).2.2)
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le hCT) (fixed_omega_ne_bot d hJd hfour)
    ((sup_le hLC hTC).trans (Subgroup.centralizer_le_normalizer _))
  exact ((borel_centralizes_omega e hJe).trans (centralizer_le inf_le_left)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

/-- Both original Borels normalize the opposite components. The four-group
omega-center is the actual original center, and no first-member choice is needed. -/
theorem original_pair_cross_borels
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    ChapterF.Source.borel K (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ChapterF.Source.borel L (T : Subgroup G) ≤ normalizer (K : Set G) :=
  ⟨cross_borel d e hJd hJe hfour,cross_borel e d hJe hJd hfour⟩

/-- The actual generated group has trivial whole two-core. -/
theorem original_pair_generated_core_eq_bot
    (d : Context T L V V₁ V₂ V₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    pCore 2 (ChapterF.Source.generated ![L,K] (T : Subgroup G)) = ⊥ := by
  let M := ChapterF.Source.generated ![L,K] (T : Subgroup G)
  have hTM : (T : Subgroup G) ≤ M := le_sup_right
  have hCM : M ≤ normalizer (M.pCoreIn 2 : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hCT : M.pCoreIn 2 ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hTM))
  have hLM : L ⊔ (T : Subgroup G) ≤ M :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hHM : H ≤ M := by
    rw [←hjoin]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hz : M.pCoreIn 2 = ⊥ := by
    by_contra hne
    have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      (T.isPGroup'.to_le hCT) hne (hLM.trans hCM)
    exact hH.1.2 ((hHM.trans hCM).trans hN)
  exact ((pCore 2 M).map_eq_bot_iff_of_injective M.subtype_injective).mp hz

private theorem characteristic_of_normalizes_component
    (d : Context T L V V₁ V₂ V₃) (P : Subgroup G)
    (hTP : (T : Subgroup G) ≤ P) (hLP : L ≤ P)
    (hPN : P ≤ normalizer (L : Set G)) :
    generalizedFitting P = pCore 2 P := by
  let := d.elementary
  have hVL : V ≤ L.pCoreIn 2 := by
    rw [←d.centralizer_eq_core]
    exact le_inf d.chosen.le_component (le_centralizer V)
  have hQN : P ≤ normalizer (L.pCoreIn 2 : Set G) :=
    hPN.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQP : L.pCoreIn 2 ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 L) ((pCoreIn_le 2 L).trans hLP) hQN
  have hne : P.pCoreIn 2 ≠ ⊥ := fun hz =>
    d.chosen.ne_bot (bot_unique ((hVL.trans hQP).trans_eq hz))
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) ⟨hne,hTP⟩))

/-- The original pair itself supplies every field of Hypothesis F.1.1,
including both full parabolics and the whole generated two-core. -/
theorem original_pair_hypothesisF11
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    ChapterF.Source.HypothesisF11 ![L,K] (T : Subgroup G) := by
  obtain ⟨hcross₀,hcross₁⟩ := original_pair_cross_borels d e hJd hJe hfour
  refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,
    original_pair_generated_core_eq_bot d hjoin hH,?_⟩
  · intro i
    fin_cases i
    · exact d.normalizes_L
    · exact e.normalizes_L
  · intro i
    fin_cases i
    · exact d.local_sylow
    · exact e.local_sylow
  · intro i
    fin_cases i
    · exact d.quotient_rankOneModel
    · exact e.quotient_rankOneModel
  · intro i
    fin_cases i
    · exact hcross₀
    · exact hcross₁
  · intro i
    fin_cases i
    · apply characteristic_of_normalizes_component d _
        (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
      exact sup_le (sup_le L.le_normalizer d.normalizes_L) hcross₀
    · apply characteristic_of_normalizes_component e _
        (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
      exact sup_le (sup_le K.le_normalizer e.normalizes_L) hcross₁

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
