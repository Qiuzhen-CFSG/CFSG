module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.SylowMaximal
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.MovedAlternating
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# The corank-one block argument for natural hyperplanes

For an escaping hyperplane with characteristic-two centralizer, a faithful
cubic actor forces the E.6.7 decomposition to have one block. Corank one
excludes the larger rank-one fields, leaving an alternating-three or
alternating-five block. Retain the actual Thompson movement equation and
apply the proved local C.5.7 calculation. Thus the maximal block-normalizer
has index two, contradicting the hyperplane stabilizer geometry.

This proves the entire pointwise E.6.14 block argument used by 11.2.2.
The natural-module owner still constructs its characteristic-two centralizer,
cubic actor and maximal stabilizer; none is asserted by this conditional
application. No universal block-selection or index callback remains.

Source: Aschbacher--Smith, E.6.14 and 11.2.2, printed pp.251 and 767--768.
-/

public section
open Subgroup
open CFSG.Quasithin CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal corank-one decomposition includes the movement equation
needed by the local index theorem, as well as the residual identity. -/
theorem hyperplane_singleBlock
    {T : Sylow 2 G} {M V U : Subgroup G}
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V) (hcor : subgroupCorank V U = 1)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (ha : HasFaithfulThreeAction U) :
    ∃ J : Subgroup G, SingleBlock T M V U J ∧
      (ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5) ∧
      J = ⁅J, Stellmacher.elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆ := by
  have hSyl := hE.sylow_obstruction hU
  have hQH := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  obtain ⟨d⟩ := e67Input_knownSimple hE U hU (centralizer (U : Set G)) hQH le_rfl hc
  have hcount := d.toBlockFamily.count_eq_one_of_faithful_three hE hU hc fixedNineInput ha
  let i : Fin d.count := ⟨0, by omega⟩
  have hi := faithfulIndexInput_of_commutation_and_quotient_rank
    conjugateChiZeroCommutationInput normalChiZeroQuotientRankInput hE U hU hc ha d hcount i
  have hr := chiZero_eq_primeToResidual_of_index (d.le i) (d.type i) (d.subnormal i) hi
  have hn : ((d.block i).subgroupOf (centralizer (U : Set G))).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hr]
    exact (centralizer (U : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  refine ⟨d.block i, ⟨d.le i, d.toBlockFamily.generated_of_count_eq_one hcount i,
    d.type i, hr, blockSylowMaximalInput _ _ _ hc hSyl (d.le i) hn (d.type i)⟩,
    ?_, d.thompson i⟩
  rcases d.type i with ⟨n, hn⟩ | hAlt
  · obtain ⟨X, _, _, _, _, _, _, _, _, hbound⟩ := d.rankOne i n hn
    have hge := hn.1
    rw [hcor] at hbound
    omega
  · exact hAlt


omit [Finite G] in
private theorem characteristicTwo_of_sylow_overgroup {Q H J : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 Q H) (hQJ : Q ≤ J) (hJH : J ≤ H)
    (hc : HasCharacteristicTwo H) : HasCharacteristicTwo J := by
  obtain ⟨P, hP⟩ := hS
  have hPJ : (P : Subgroup H) ≤ J.subgroupOf H := by
    intro x hx
    exact hQJ (hP ▸ mem_map_of_mem H.subtype hx)
  exact (show HasCharacteristicTwo (J.subgroupOf H) from
    centralizer_pCore_le_of_sylow_le P (J.subgroupOf H) hPJ hc).of_equiv
      (subgroupOfEquivOfLe hJH)

omit [Finite G] in
private theorem block_normalized {T : Sylow 2 G} {M V W L : Subgroup G}
    (hL : SingleBlock T M V W L) : normalizer (W : Set G) ≤ normalizer (L : Set G) := by
  rw [hL.residual_three]
  exact (normalizer_le_normalizer_centralizer W).trans
    (normalizer_le_normalizer_characteristic_image (centralizer (W : Set G))
      (primeToResidual 3 (centralizer (W : Set G))))


/-- E.6.14 for a hyperplane, with every block and local-index input proved.
Its remaining assumptions are the genuine geometric hypotheses on the
original hyperplane and overgroup, not block-theoretic callbacks. -/
theorem centralizer_le_of_hyperplane_stabilizer
    {T : Sylow 2 G} {M V W M₀ : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hne : W ≠ ⊥) (hWV : W ≤ V) (hodd : oddCentralizerCondition M V W)
    (hcor : subgroupCorank V W = 1)
    (hchar : HasCharacteristicTwo (centralizer (W : Set G))) (hthree : HasFaithfulThreeAction W)
    (hTM₀ : (T : Subgroup G) ≤ M₀)
    (hM₀Q : M₀ ≤ normalizer (sylowCentralizer (T : Subgroup G) V : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hmax : localNormalizer M₀ W ⋖ M₀) (hindex : (localNormalizer M₀ W).relIndex M₀ ≠ 2) :
    centralizer (W : Set G) ≤ M := by
  by_contra hescape
  have hW : W ∈ obstructionFamily M V := ⟨hWV, hne, hescape, hodd⟩
  obtain ⟨L, hL, hAlt, hmove⟩ := hyperplane_singleBlock h hW hcor hchar hthree
  have hLM : ¬ L ≤ M := by
    intro hLM
    apply hescape
    rw [hL.generated]
    exact sup_le inf_le_right hLM
  have hbetween : localNormalizer M₀ W ≤ localNormalizer M₀ L :=
    inf_le_inf_left M₀ (block_normalized hL)
  rcases hmax.eq_or_eq hbetween inf_le_left with heq | heq
  · let Q := sylowCentralizer (T : Subgroup G) V
    let H₁ := L ⊔ Q
    have hSyl := show Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (W : Set G)) from h.sylow_obstruction hW
    have hQH : Q ≤ centralizer (W : Set G) := (Chapter1.isSylowIn_iff.mp hSyl).2.1
    have hH₁H : H₁ ≤ centralizer (W : Set G) := sup_le hL.le_centralizer hQH
    have hQ2 : IsPGroup 2 Q := (Chapter1.isSylowIn_iff.mp hSyl).1
    have hQNL : Q ≤ normalizer (L : Set G) :=
      hQH.trans ((Subgroup.centralizer_le_normalizer _).trans (block_normalized hL))
    have hres : (pResidual 2 H₁).map H₁.subtype = L :=
      embedded_pResidual_join_pGroup L Q hL.type.chi.short.twoPerfect hQ2 hQNL
    have hH₁Syl : Chapter1.IsSylowIn 2 Q H₁ := hSyl.restrict le_sup_right hH₁H
    have hH₁char : HasCharacteristicTwo H₁ :=
      characteristicTwo_of_sylow_overgroup hSyl le_sup_right hH₁H hchar
    have hW2 : IsPGroup 2 W :=
      T.isPGroup'.of_injective (inclusion (hWV.trans h.le_sylow))
        (inclusion_injective (hWV.trans h.le_sylow))
    have hSQTKW := h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (W : Set G)) from ⟨W, hne, hW2, rfl⟩)
    have hSQTKH₁ : IsSQTK KnownSimple.IsKnownSimple H₁ :=
      ⟨hSQTKW.stronglyQuasithin.of_injective
        (inclusion (hH₁H.trans (Subgroup.centralizer_le_normalizer _)))
        (inclusion_injective (hH₁H.trans (Subgroup.centralizer_le_normalizer _))),
       hSQTKW.isKGroup.of_injective
        (inclusion (hH₁H.trans (Subgroup.centralizer_le_normalizer _)))
        (inclusion_injective (hH₁H.trans (Subgroup.centralizer_le_normalizer _)))⟩
    have hSQTKQ := h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q, h.sylowCentralizer_ne_bot, hQ2, rfl⟩)
    have hSQTKM₀ : IsSQTK KnownSimple.IsKnownSimple M₀ :=
      ⟨hSQTKQ.stronglyQuasithin.of_injective (inclusion hM₀Q) (inclusion_injective hM₀Q),
       hSQTKQ.isKGroup.of_injective (inclusion hM₀Q) (inclusion_injective hM₀Q)⟩
    have hnocommon := Chapter3.no_common_normal_of_unique_maximal hQ2 hunique
      (show ¬ H₁ ≤ M from fun hh => hLM (le_sup_left.trans hh))
    have hcfg : LocalIndex.Configuration KnownSimple.IsKnownSimple M₀ H₁ Q L :=
      ⟨hSQTKM₀, hSQTKH₁, hH₁char, hH₁Syl, hL.unique_maximal,
        inf_le_left.trans hTM₀, hM₀Q, hnocommon, hres, hL.type, heq.symm ▸ hmax⟩
    have hi := LocalIndex.index_of_moved_alternating hcfg hmove hAlt
    exact hindex (heq ▸ hi)
  · let W₁ := V ⊓ centralizer (L : Set G)
    have hWW₁ : W ≤ W₁ := le_inf hWV (le_centralizer_iff.mp hL.le_centralizer)
    have hW₁ne : W₁ ≠ ⊥ := fun hb => hne (le_bot_iff.mp (hb ▸ hWW₁))
    have hW₁V : W₁ ≤ V := inf_le_left
    have hM₀NL : M₀ ≤ normalizer (L : Set G) := heq ▸ inf_le_right
    have hTNW₁ : (T : Subgroup G) ≤ normalizer (W₁ : Set G) :=
      (le_inf h.sylow_le_normalizer
        ((hTM₀.trans hM₀NL).trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
    have hW₁normal : (W₁.subgroupOf (T : Subgroup G)).Normal :=
      (normal_subgroupOf_iff_le_normalizer (hW₁V.trans h.le_sylow)).mpr hTNW₁
    have hc := centralizer_le_of_normal_in_sylow_knownSimple h hW₁ne hW₁V
      (oddCentralizerCondition_mono hWW₁ hodd) hW₁normal
    exact hLM ((le_centralizer_iff.mpr (show W₁ ≤ centralizer (L : Set G) from inf_le_right)).trans hc)


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
