module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeFullSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeResidualApplication
public import Theory.GroupAction.ConjugationSectionIndex

/-!
# Residual denominator bounds and selected contradictions in DGS 8.4

The full neighboring-span bound puts the original denominator
D = (W intersect Q_alpha') V_beta inside the fixed subgroup of W/V_beta
under V_alpha'. The literal conjugation formula therefore bounds fixed
index by |W:D|. Residual movement gives the opposite lower bound: two in
all cases, and the defining field order for a linear beta quotient.

In the linear terminal case the original graph conjugation transports its
marking to beta. The terminal Sylow order bounds its omega-center, so the
strict upper index contradicts the linear lower bound. A terminal quotient
of two-rank at most one gives the same contradiction with lower bound two.
Every use of the full-span bound retains its proved placement cases.

Source: DGS, *Groups and Graphs* (1985), 8.2, 5.7 and the final paragraph
of 8.4, p.138. RadiusThreeDistance supplies the actual model-case consumers.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Bounds for the actual residual denominator, with its centralization
proved from 8.3 and both transitivity witnesses retained in residual movement. -/
theorem reduced_radius_three_fixed_index_bounds
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5)) :
    let F := Reduction.reducedFamily J S₀
    let W := V F beta 3
    let D := (W ⊓ Q F a') ⊔ V F beta 1
    2 ≤ D.relIndex W ∧
      ∀ (K : Type*) [Field K] [Finite K] [CharP K 2] (n : ℕ),
        0 < n → Nat.card K = 2^n →
        (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta)) ≃* SL(2,K) →
        Nat.card K ≤ D.relIndex W := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let W := V F beta 3
  let V₀ := V F beta 1
  let I := W ⊓ Q F a'
  let D := I ⊔ V₀
  let A := V F a' 1
  let L := graphLocalGroup F beta
  let : ∀ i, Finite (F i) := finite_endpoints ht
  change 3 < b F at hb
  have hWP : W ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    beta beta 3 (by simpa using hb.le)
  let : Finite W := Finite.of_injective (inclusion hWP) (inclusion_injective _)
  have hVW : V₀ ≤ W := V_mono F beta (by decide)
  have hnV : W ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    hWP.trans (stabilizer_normalizes_V F beta 1)
  have hnA : A ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    (radius_one_mutual_normalization F ht.generate beta a' hd.le).2
  have hH : ⁅V₀ ⊓ Q F a',A⁆ ≤ V₀ :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hI : ⁅I,A⁆ ≤ V₀ :=
    (reduced_radius_three_full_span_bound h hob models hc hab hd hb hcomm w hm R hR hcase).trans hH
  have hD : ⁅A,D⁆ ≤ V₀ := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal W I V₀ A V₀ hnV inf_le_left hVW hI
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hne : ⁅V₀ ⊓ Q F a',A⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  obtain ⟨hnW,hN,α,hα,_,_,hi2,hlin⟩ := reduced_radius_three_residual_section
    h hob models hc hab hd hb hcomm hne
  let _ := hN
  have hi := quotient_conjugation_fixedIndex_le L W V₀ D A hnW α hα le_sup_right hD
  exact ⟨hi2.trans hi,fun K _ _ _ n hn hK e => (hlin K n hn hK e).trans hi⟩

/-- The original strict denominator index contradicts the field-order
lower bound when the terminal quotient is genuinely SL₂. -/
theorem reduced_radius_three_linear_contradiction
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5))
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K)) : False := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let := Fintype.ofFinite K
  change 3 < b F at hb
  have hb1 : 1 < b F := by omega
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨r,hr⟩ := (source_critical_geometry ht d hc hab hd hb1 hcomm).1
    change b F = 2*r+1 at hr
    change (graph F).dist beta a' + 1 = b F at hd
    refine ⟨r,?_⟩
    have he : (graph F).dist beta a' = 2*r := Nat.add_right_cancel (hd.trans hr)
    simpa only [two_mul] using he
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ((even_dist_iff F ht.generate beta a').mp heven)
  have heq : (d.localGroup beta).map (MulAut.conj g).toMonoidHom = d.localGroup a' := by
    rw [←d.conjugate,hg]
  let f := ((d.localGroup beta).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr heq)
  let eβ := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  have hl := (reduced_radius_three_fixed_index_bounds h hob models hc hab hd hb hcomm
    w hm R hR hcase).2 K n hn hK eβ
  obtain ⟨prev,T,_,_,_,_,_,_,_,hu⟩ := reduced_radius_three_section_index h hob models
    hc hab hd hb hcomm hne
  let L := d.localGroup a'
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  change (L ⧸ pCore 2 L) ≃* SL(2,K) at e
  change Sylow 2 L at T
  let q := QuotientGroup.mk' (pCore 2 L)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card S = Nat.card K := by
    calc
      Nat.card S = Nat.card S' := Nat.card_congr
        ((S : Subgroup (L ⧸ pCore 2 L)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card K := (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 S').toEquiv).symm
  have hO : Nat.card (omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L))) ≤ Nat.card K := by
    rw [←hcard]
    exact Nat.card_le_card_of_injective (inclusion (map_subtype_le _)) (inclusion_injective _)
  exact (not_lt_of_ge hl) (hu.trans_le hO)

/-- A terminal quotient of two-rank at most one contradicts the universal
fixed-index lower bound of two. -/
theorem reduced_radius_three_rank_one_contradiction
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5))
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≤ 1) : False := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite (d.localGroup a') :=
    Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  have hl := (reduced_radius_three_fixed_index_bounds.{_,0} h hob models hc hab hd hb hcomm
    w hm R hR hcase).1
  obtain ⟨prev,T,_,_,_,_,_,_,_,hu⟩ := reduced_radius_three_section_index h hob models
    hc hab hd hb hcomm hne
  let L := d.localGroup a'
  change Sylow 2 L at T
  change primeRank 2 (L ⧸ pCore 2 L) ≤ 1 at hr
  have hO := (primeRank_le_iff_elementary_card_le (L ⧸ pCore 2 L)).mp hr
    (omegaCenterIn ((T : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)))) inferInstance
  norm_num only [pow_one] at hO
  exact (not_lt_of_ge hl) (hu.trans_le hO)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
