module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonSource
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The reduced conjugate span and the three-free local centralizer

The quotient-action centralizer of L_v in G_v has order prime to three.
Its three-rank adds to the rank-two A₆ quotient of L_v, whereas the
involution centralizer G_v is strongly quasithin. This argument keeps the
literal two-core quotient and does not require component recognition.

In the small Thompson case, T_v is Sylow in G_v. The already elementary
G_v-conjugate span of V_v is therefore two-reduced: transport the proved
reducedness inside C_LT(v), apply Sylow-overgroup inheritance, and identify
the intrinsic normal closure with the original ambient conjugate span.
These are the actual module inputs to SmallThompson, which excludes this
branch of 12.6.11. T-invariance retains its earlier source owner qt-d-1222-source.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.11, printed p.825, using A.1.11 and B.2.14.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original involution centralizer has three-rank at most two. -/
theorem SourceHypothesis.nonsingular_point_three_rank
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    primeRank 3 (Gv (v : G)) ≤ 2 := by
  have hp : (v : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ v.property
  have ho : orderOf (v : G) = 2 := orderOf_eq_prime_iff.mpr
    ⟨hp,fun he => nonsingular_ne_one D hv (Subtype.ext he)⟩
  exact H.source.simpleQTKE.toIsQTKE.involution_centralizer_stronglyQuasithin ho
    3 (by decide) (by decide)

/-- The actual centralizer of L_v/O₂(L_v) inside G_v has no three-part. -/
theorem SourceHypothesis.nonsingular_quotient_centralizer_three_free
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Nat.Coprime 3 (Nat.card (Gv (v : G) ⊓ coreQuotientCentralizer (Lv L (v : G)) : Subgroup G)) := by
  let A := Lv L (v : G)
  let C := Gv (v : G) ⊓ coreQuotientCentralizer A
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hz : center (A ⧸ pCore 2 A) = ⊥ := Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e
  have hCA : C ≤ normalizer (A : Set G) := fun x hx =>
    ((mem_coreQuotientCentralizer_iff A x).mp hx.2).1
  have hc : ⁅(pResidual 2 C).map C.subtype,A⁆ ≤ A.pCoreIn 2 := by
    apply commutator_le.mpr
    intro c hc a ha
    exact ((mem_coreQuotientCentralizer_iff A c).mp ((map_subtype_le _ hc).2)).2 a ha
  have hrA : 2 ≤ primeRank 3 A := by
    have he := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    rw [←primeRank_congr 3 e,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup] at he
    exact he
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) C A hCA hc (by simp [hz])
  have hb : primeRank 3 (C ⊔ A : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le inf_le_left (Lv_le_Gv L _))).trans
      (H.nonsingular_point_three_rank D v hv)
  exact Nat.prime_three.coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 3 C = 0))
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem componentOrbit_eq_span (W A : Subgroup G) :
    componentOrbit W A = conjugateSpanBy W A := by
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer W A _ (le_conjugateSpanBy W A)
      (le_normalizer_conjugateSpanBy W A)
  · exact conjugateSpanBy_le (le_componentOrbit W A) (le_normalizer_componentOrbit W A)

/-- The actual conjugate span is reduced in G_v, with its intrinsic centralizer quotient. -/
theorem SourceHypothesis.small_thompson_closure_reduced
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (heq : Lv L (v : G) = Kv (v : G)) :
    IsPReduced 2 ((componentOrbit (Vv L V (v : G)) (Gv (v : G))).subgroupOf (Gv (v : G))) := by
  let A := Gv (v : G)
  let B := LT T L ⊓ A
  let W := Vv L V (v : G)
  let X := componentOrbit W A
  have hBA : B ≤ A := inf_le_right
  have hWB : W ≤ B := (Vv_le_Rv H.chosen v).trans (pCoreIn_le 2 _)
  have hWA : W ≤ A := hWB.trans hBA
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,_,_,_,_⟩ := H.nonsingular_small_thompson D v hv hTv hJ S hTS
  have hSB : (S : Subgroup A) ≤ B.subgroupOf A := by
    intro s hs
    have ht : (s : G) ∈ Tv T (v : G) := hS ▸ mem_map_of_mem A.subtype hs
    exact ⟨mem_sup_right ht.1,ht.2⟩
  let e := (subgroupOfEquivOfLe hBA).symm
  let W' := (W.subgroupOf B).map e.toMonoidHom
  have hred : IsPReduced 2 W' := (H.local_moved_isReduced D v hv hTV).map_equiv e
  have hmap : W'.map (B.subgroupOf A).subtype = W.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_map,map_map]
    have he : (A.subtype.comp (B.subgroupOf A).subtype).comp e.toMonoidHom = B.subtype := rfl
    rw [he,map_subgroupOf_eq_of_le hWB,map_subgroupOf_eq_of_le hWA]
  have hcl : normalClosure (W'.map (B.subgroupOf A).subtype : Set A) = X.subgroupOf A := by
    rw [hmap,normalClosure_subgroupOf_eq_conjugateSpanBy W A hWA,←componentOrbit_eq_span]
  have hXA : X ≤ A := iSup_conjugates_le_of_le_normalizer W A A hWA A.le_normalizer
  let : IsElementaryAbelian 2 X := H.small_thompson_closure_elementary_of_normalizer
    H.core_thompson_normalizer D v hv hTV hTv hJ heq
  have hel : IsElementaryAbelian 2 (normalClosure (W'.map (B.subgroupOf A).subtype : Set A)) := by
    rw [hcl]
    exact IsElementaryAbelian.subgroupOf hXA
  rw [←hcl]
  exact hred.normalClosure_of_sylow_le S (B.subgroupOf A) hSB W' hel
end CFSG.Quasithin.Chapter12.Section06