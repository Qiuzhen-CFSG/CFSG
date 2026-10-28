module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorCatalogueApplication

/-!
# Closing the field-two unitary ending cases of DGS 8.2

The starting center has a nontrivial action on the ending neighbor span:
otherwise the span-centralizer theorem puts it in the full ending kernel,
contrary to criticality. When the ending quotient has two-rank one, the
starting center's elementary image has order at most two. Its core index
is therefore bounded by the nontrivial centralizer index on the original
span. This handles SU₃(2) and PSU₃(2) without a faithfulness claim about an
arbitrarily selected composition factor or the special-unitary scalar kernel.

The complete ending catalogue now supplies the numerical premise of 8.2
for every source model, and the literal reduced linear-start application
discharges this premise. Source: DGS, Groups and Graphs (1985), 8.2,
printed pp.134–135, using the span-centralizer statement of 8.1(c).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Two-rank one at the ending quotient gives the required original index
bound directly. No faithfulness of a factor representation is assumed. -/
theorem source_ending_two_rank_one_bound
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≃* D)
    (hr : primeRank 2 D ≤ 1) :
    (Q (family P) a').relIndex (Z (family P) a) ≤
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  have hZP : Z F a ≤ stabilizer F a' :=
    Z_le_stabilizer_of_dist_le_b F h.generate a a' hc.1.le
  have hZL : Z F a ≤ d.localGroup a' := pGroup_le_localGroup F d a' (Z F a)
    (IsElementaryAbelian.isPGroup 2 _) hZP
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a')))
  let A := ((Z F a).subgroupOf (d.localGroup a')).map q
  let : IsElementaryAbelian 2 ((Z F a).subgroupOf (d.localGroup a')) :=
    IsElementaryAbelian.subgroupOf hZL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hcard : Nat.card A = (Q F a').relIndex (Z F a) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex _ _ _ q
      (local_quotient_kernel F d a' e) hZL
  have htwo : (Q F a').relIndex (Z F a) ≤ 2 := by
    rw [← hcard]
    simpa only [pow_one] using
      (primeRank_le_iff_elementary_card_le D).mp hr A inferInstance
  have hVP : V F a' 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F h.generate a' a' 1 (by
      simp only [SimpleGraph.dist_self, zero_add]; exact hb.le)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion hVP) (inclusion_injective _)
  have hnz : (centralizer (Z F a : Set G)).relIndex (V F a' 1) ≠ 0 :=
    ((centralizer (Z F a : Set G)).subgroupOf (V F a' 1)).index_ne_zero_of_finite
  have hne : (centralizer (Z F a : Set G)).relIndex (V F a' 1) ≠ 1 := by
    intro he
    have hcentral : Z F a ≤ centralizer (V F a' 1 : Set G) :=
      le_centralizer_iff.mp (relIndex_eq_one.mp he)
    obtain ⟨_, _, _, _, w, hw, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
    exact hc.2 ((le_inf hZP hcentral).trans (source_span_centralizer_le_kernel h hw))
  have hlo : 2 ≤ (centralizer (Z F a : Set G)).relIndex (V F a' 1) := by omega
  exact htwo.trans hlo

/-- Both field-two unitary ending quotients satisfy the original bound;
the special-unitary scalar kernel is retained through the two-rank transport. -/
theorem source_ending_small_unitary_bound
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≃* D)
    (hm : ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) :
    (Q (family P) a').relIndex (Z (family P) a) ≤
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1) := by
  rcases hm with hm | hm
  · obtain ⟨K, _, _, J, hK, hconj, ⟨f⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    exact source_ending_two_rank_one_bound h d hc hab hd hb hcomm (e.trans f)
      (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
  · obtain ⟨K, _, _, J, hK, hconj, ⟨f⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply source_ending_two_rank_one_bound h d hc hab hd hb hcomm (e.trans f)
    rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le

variable {L J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The full ending catalogue gives the original bound with no remaining
field-two unitary alternative. -/
theorem reduced_ending_catalogue_bound
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type u} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* D)
    (hm : IsRankOneModel D) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (Z Γ a) ≤
        (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  rcases reduced_ending_factor_bound_or_small_unitary h hc hab hd hb hcomm e hm with
    hbound | hbound | hsmall
  · exact hbound
  · exact (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hbound
  · exact source_ending_small_unitary_bound (Reduction.reduced_triple h)
      (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm e hsmall

/-- DGS 8.2 for a linear starting quotient and every ending source model.
The graph, original indices, quotient markings and either critical orientation
are retained; the ending bound has no remaining model exception. -/
theorem reduced_reciprocal_escape_of_linear_start
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
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (eK : (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) ≃* SL(2, K))
    : ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤
      Q (Reduction.reducedFamily J S₀) beta := by
  let : ∀ i, Finite (Reduction.reducedFamily J S₀ i) :=
    finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup (Reduction.reducedFamily J S₀) a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact source_reciprocal_linear_escape_of_factor_bound (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hne hn hK eK
    (reduced_ending_catalogue_bound h hob hc hab hd hb hcomm
      (MulEquiv.refl _) (models a'))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
