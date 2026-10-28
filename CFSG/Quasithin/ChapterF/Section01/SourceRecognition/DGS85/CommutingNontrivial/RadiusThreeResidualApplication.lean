module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication
public import Theory.Representation.SL2.TwoGroupFixedIndex

/-!
# Residual movement and the source linear lower bound on W/V_beta

Apply 8.2 to the original reciprocal span V_alpha'. Its escape from Q_beta,
together with the proved action-kernel control, makes it move the Frattini
quotient of W/V_beta. If the beta quotient is SL₂(2^n), the fixed index is
at least 2^n. For n=1 nontrivial movement itself gives the bound; for n>1
it follows from the irreducible-section field-degree estimate.
The same movement gives index at least two for every model, which is the
required lower bound in all field-two cases.

This application works at either orientation of the reduced F1.11 graph.
It retains the exact conjugation formula and uses no arbitrary faithful
section. The second omega placement, full neighboring-span commutator and
nonlinear lower bounds are still needed to contradict the strict upper
index and complete 8.4; no b=3 or 8.5--8.7 conclusion is asserted here.

Source: DGS, *Groups and Graphs* (1985), 5.7, 8.2 and 8.4, pp.108,134--138.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]
variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
open scoped MatrixGroups

/-- The original nontrivial commuting configuration supplies a residually
moving action on W/V_beta. Its actual reciprocal span moves the Frattini
quotient. In the linear row its fixed index is at least the defining field
order, including the binary field; all maps and quotient denominators
remain literal. No intersection centralization premise is assumed. -/
theorem reduced_radius_three_residual_section
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
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    :
    let F := Reduction.reducedFamily J S₀
    let W := V F beta 3
    let V₀ := V F beta 1
    let L := graphLocalGroup F beta
    let A := (V F a' 1).subgroupOf L
    ∃ (hnW : L ≤ normalizer (W : Set (Reduction.G₀ J S₀)))
      (hN : (V₀.subgroupOf W).Normal),
      let _ := hN
      ∃ α : L →* MulAut (W ⧸ V₀.subgroupOf W),
        (∀ l : L, ∀ x : W,
          α l (QuotientGroup.mk' (V₀.subgroupOf W) x) =
            QuotientGroup.mk' (V₀.subgroupOf W)
              ⟨(l : Reduction.G₀ J S₀) * (x : Reduction.G₀ J S₀) *
                (l : Reduction.G₀ J S₀)⁻¹,
                (mem_normalizer_iff.mp (hnW l.property) x).mp x.property⟩) ∧
        (¬ pResidual 2 L ≤ α.ker) ∧
        (¬ A ≤ ((quotientAut (frattini (W ⧸ V₀.subgroupOf W))).comp α).ker) ∧
        (let _ := MulDistribMulAction.compHom (W ⧸ V₀.subgroupOf W) (α.comp A.subtype);
          2 ≤ (FixedPoints.subgroup A (W ⧸ V₀.subgroupOf W)).index) ∧
        ∀ (K : Type*) [Field K] [Finite K] [CharP K 2]
          (n : ℕ), 0 < n → Nat.card K = 2^n →
          (L ⧸ pCore 2 L) ≃* SL(2,K) →
          let _ := MulDistribMulAction.compHom (W ⧸ V₀.subgroupOf W) (α.comp A.subtype)
          Nat.card K ≤ (FixedPoints.subgroup A (W ⧸ V₀.subgroupOf W)).index := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let W := V F beta 3
  let V₀ := V F beta 1
  let L := graphLocalGroup F beta
  let A := (V F a' 1).subgroupOf L
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  change 3 < b F at hb
  have hWP : W ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    beta beta 3 (by simp only [SimpleGraph.dist_self,zero_add]; omega)
  let : Finite W := Finite.of_injective (inclusion hWP) (inclusion_injective _)
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F beta)).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      beta beta 3 (by simp only [SimpleGraph.dist_self,zero_add]; omega) (d.kernel_sylow beta))
  obtain ⟨hnW,hN,α,hα,hr,_,hkern⟩ := source_radius_three_quotient_action ht
    (Reduction.reduced_borel_core_sylow h) d hab hb (models beta)
  change (V₀.subgroupOf W).Normal at hN
  let _ := hN
  let X := W ⧸ V₀.subgroupOf W
  change L →* MulAut X at α
  change ¬ pResidual 2 L ≤ α.ker at hr
  change ∀ A : Subgroup L, IsPGroup 2 A →
    A ⊓ ((quotientAut (frattini X)).comp α).ker ≤ pCore 2 L at hkern
  let : Finite X := Finite.of_surjective _ (QuotientGroup.mk'_surjective (V₀.subgroupOf W))
  have hA' : IsPGroup 2 (V F a' 1) := (isPGroup_pCoreIn 2 (stabilizer F a')).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      a' a' 1 (by simp only [SimpleGraph.dist_self,zero_add]; omega) (d.kernel_sylow a'))
  have hAP : V F a' 1 ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    a' beta 1 (by rw [SimpleGraph.dist_comm]; exact hd.le)
  have hAL : V F a' 1 ≤ L := pGroup_le_localGroup F d beta _ hA' hAP
  have hA : IsPGroup 2 A := hA'.comap_subtype
  have hAQ : ¬ A ≤ pCore 2 L := by
    intro hAQ
    apply reduced_reciprocal_escape h hob models hc hab hd (by change 1 < b F; omega) hcomm hne
    rw [←localGroup_core_eq F d beta]
    intro x hx
    exact ⟨⟨x,hAL hx⟩,hAQ hx,rfl⟩
  have hφ : ¬ A ≤ ((quotientAut (frattini X)).comp α).ker := by
    intro hh
    apply hAQ
    have hh' := hkern A hA
    rwa [inf_eq_left.mpr hh] at hh'
  let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
  have hi2 : 2 ≤ (FixedPoints.subgroup A X).index := by
    apply Nat.succ_le_iff.mpr
    apply Subgroup.one_lt_index_of_ne_top
    intro he
    apply hφ
    intro a ha
    have hfix : α a = 1 := by
      apply MulEquiv.ext
      intro x
      have hx : x ∈ FixedPoints.subgroup A X := he ▸ mem_top x
      exact hx ⟨a,ha⟩
    change quotientAut (frattini X) (α a) = 1
    rw [hfix,map_one]
  refine ⟨hnW,hN,α,hα,hr,hφ,hi2,?_⟩
  intro K _ _ _ n hn hK e
  by_cases hn2 : 1 < n
  · let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : π.ker = pCore 2 L := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
      rw [←e.map_one,e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hneπ : A.map π ≠ ⊥ := fun he => hAQ (hk ▸ (map_eq_bot_iff A).mp he)
    exact Representation.SL2.twoGroup_fixedIndex_lower_of_residual_moves π hπ
      (hk ▸ pCore_isPGroup) (hpW.to_quotient _) α hr A hA hneπ hn2 hK
  · have hn1 : n = 1 := by omega
    rw [hK,hn1,pow_one]
    exact hi2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
