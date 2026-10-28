module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveOuter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveScalar

/-!
# Source 6.2.7 on the original Chapter12 natural layer

The original scalar cubic and escaping A5 component coincide: a distinct
moved component would commute with the component containing the offender.
The field-action contradiction therefore applies with the same quotient
coordinates and intrinsic two-core maps. It proves that a layer normalizing
a conjugate centralizes it, without assuming mutual normalization.

Every conjugate in T normalizes the original layer, so the zeroth weak
closure lies in C_T(V)=O2(LT). The existing weak-closure transport and
uniqueness over LT then put its full ambient normalizer in M. This
establishes both source clauses with the actual chosen module. The 6.2.8
graph escape and order-eight intersection are still needed for LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, printed pp.682--684, applied to
[R2(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative

open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The genuine one-sided consequence of source 6.2.7 on the original layer:
if the layer normalizes a conjugate, the two layers centralize each other. -/
theorem source_local_one_sided_centralizes
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) := by
  by_contra hnon
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := LocalFieldQuotientAction.Centralizer U
  let π := (LocalFieldQuotientAction.action B U).rangeRestrict
  let I := (A.subgroupOf H).map π
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  obtain ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,hmark,
      J,hJ,hJI,⟨eJ⟩,hcomm,hsyl,hcompl,F,hF,a,z,hz0,hz1,hz3,hscalar⟩ :=
    source_local_one_sided_cubic_scalar D h h611 hnatural g hBA hnon
  obtain ⟨J',hJ',hJI',⟨eJ'⟩,K,hK,hKJ,⟨eK,heK⟩,hescape⟩ :=
    source_local_one_sided_five_normalizer_escape D h h611 hnatural g hBA hnon
  have hIJ : I ≤ J := by
    obtain ⟨S,hS⟩ := hsyl
    exact (show I = (S : Subgroup J).map J.subtype from hS).le.trans (map_subtype_le _)
  have heq : J' = J := by
    by_contra hne
    have hb : J' = ⊥ := by
      apply le_bot_iff.mp
      rw [←hJI']
      exact (commutator_mono le_rfl hIJ).trans_eq (hJ'.commutator_eq_bot_of_ne hJ hne)
    have hh := Nat.card_congr eJ'.toEquiv
    rw [hb,card_bot,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  cases heq.symm
  exact LocalFieldQuotientAction.five_scalar_impossible h611 hnatural hE hfield hUc
    J eJ K hK hKJ eK heK hescape ρ η hrestrict d hd F hF a z hz0 hz1 hscalar

/-- The reverse orientation of the one-sided normalization consequence,
with the original layer fixed. -/
theorem source_local_normalizing_conjugate_centralizes
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hAB : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      normalizer (commutatorLayer T L : Set G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) := by
  by_contra hnon
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAB
  rw [fusion_map_conj_inverse,map_equiv_normalizer_eq] at hh
  exact fusion_inverse_noncentralizing hnon
    (source_local_one_sided_centralizes D h h611 hnatural g⁻¹ hh)

/-- Source 6.2.7 in full on the original Chapter12 layer: its zeroth weak
closure lies in the Sylow centralizer, that centralizer is O2(LT), and the
ambient normalizer of the weak closure lies in the original maximal subgroup. -/
theorem source_local_zero_weak_closure
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    W (commutatorLayer T L) (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (commutatorLayer T L : Set G) ∧
    (T : Subgroup G) ⊓ centralizer (commutatorLayer T L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    normalizer (W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hw : W (commutatorLayer T L) (T : Subgroup G) 0 ≤
      centralizer (commutatorLayer T L : Set G) := by
    change sSup (ChapterE.gamma (commutatorLayer T L) (T : Subgroup G) 0) ≤ _
    apply sSup_le
    intro A hA
    obtain ⟨g,rfl,hAT⟩ := (ChapterE.mem_gamma_zero_iff _ _ _).mp hA
    exact source_local_normalizing_conjugate_centralizes D h h611 hnatural g
      (hAT.trans h611.sylow_normalizes_layer)
  exact ⟨le_inf (W_le _ _ _) hw,sylow_layer_centralizer_eq_core h611 hnat,
    normalizer_W_zero_le_of_centralizes h611 hnat
      (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2 hw⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
