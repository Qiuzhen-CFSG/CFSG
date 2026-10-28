module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.GroupTheory.AmalgamGraph.RelativeOvergroups
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The actual Chapter 6 enlargement and its two-residual

The source local group is L = G* O₂(B), with the original starred endpoint
and the full Borel core. It is normal in the full endpoint, has the same
embedded two-core, and the join is the literal source product. The marked
starred Sylow has full-vertex normalizer B. Therefore an overgroup of that
Sylow either contains G* or lies in B.

A non-two-closed subgroup N of L supplements O₂(B). When N is normal in the
full vertex group, L/N is a two-group, proving O²(L) ≤ N, source 6.2(a).
Under 6.4's contrary intersection-normality assumption the actual opposite-core
closure is not two-closed, lies in L, contains this residual, and supplements
O₂(B). The SL₂ quotient and opposite-core Sylow conclusions remain separate
6.4 obligations; this file does not assert the 6.1 model enlargement theorem.

The reduced F1.11 application uses the constructed starred local data and
identifies L literally with the original starred endpoint enlarged by the
original full Borel core. Its embedded core is the original parabolic core.
A second application retains the actual closure in the reduced completion.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, notation 6.0 and 6.2(a), pp.118--119; 6.4, pp.120--121.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The Chapter 6 local group, distinct from the original F1.11 local factor. -/
def localEnlargement (d : LocalRankOneData P B) : Subgroup G := d.Pstar ⊔ B.pCoreIn 2

theorem localEnlargement_le (d : LocalRankOneData P B) : localEnlargement d ≤ P :=
  sup_le d.Pstar_le ((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le))

private theorem star_normalized (d : LocalRankOneData P B) :
    P ≤ normalizer (d.Pstar : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal

/-- The source product S G* is the literal product of the indicated subgroups. -/
theorem localEnlargement_product (d : LocalRankOneData P B) :
    (localEnlargement d : Set G) = (B.pCoreIn 2 : Set G) * (d.Pstar : Set G) := by
  rw [localEnlargement, sup_comm]
  exact coe_mul_of_left_le_normalizer_right _ _
    (((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le)).trans (star_normalized d))

/-- The enlarged source group is normal in the full vertex group. -/
theorem localEnlargement_normalized (d : LocalRankOneData P B) :
    P ≤ normalizer (localEnlargement d : Set G) := by
  apply d.supplement.ge.trans
  refine sup_le (le_sup_left.trans (localEnlargement d).le_normalizer) ?_
  exact (le_inf ((le_sup_right.trans d.supplement.le).trans (star_normalized d))
    (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Enlargement preserves the actual embedded vertex core. -/
theorem localEnlargement_core (d : LocalRankOneData P B) :
    (localEnlargement d).pCoreIn 2 = P.pCoreIn 2 := by
  apply le_antisymm (pCoreIn_mono_of_normalizes (localEnlargement_le d) (localEnlargement_normalized d))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 P)
    ((source_core_le_star d).trans le_sup_left)
    ((localEnlargement_le d).trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))

/-- The marked starred Sylow lies in the original full Borel. -/
theorem source_star_sylow_le_borel (d : LocalRankOneData P B) :
    (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B := by
  intro x hx
  have hh : x ∈ d.Pstar ⊓ normalizer
      ((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype : Set G) :=
    ⟨map_subtype_le _ hx, ((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype).le_normalizer hx⟩
  rw [← d.borel_eq] at hh
  exact hh.2

private theorem star_sylow_proper (d : LocalRankOneData P B)
    (H : Subgroup d.Pstar) (hT : (d.sylow : Subgroup d.Pstar) ≤ H) (hne : H ≠ ⊤) :
    H ≤ normalizer (d.sylow : Set d.Pstar) := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  exact (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).unique_maximal H hT
    (lt_top_iff_ne_top.mpr hne)

/-- The full Borel, including outer factors, is the full-vertex normalizer of
the same marked starred Sylow. -/
theorem source_full_normalizer_star_sylow (d : LocalRankOneData P B) :
    P ⊓ normalizer ((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype : Set G) = B := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  let T := (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  have hnB : B ≤ normalizer (T : Set G) := by
    rcases relative_rankOne_overgroup d.Pstar B (hBP.trans (star_normalized d)) d.sylow
      (star_sylow_proper d) (source_star_sylow_le_borel d) with hstar | hn
    · have ht : B.subgroupOf d.Pstar = ⊤ := subgroupOf_eq_top.mpr hstar
      rw [source_star_borel d] at ht
      exact ((rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).proper.ne ht).elim
    · exact hn
  apply le_antisymm _ (le_inf hBP hnB)
  intro x hx
  have hp : x ∈ (d.Pstar : Set G) * (B : Set G) := by
    rw [← source_star_product d]
    exact hx.1
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  have han : a ∈ normalizer (T : Set G) := by
    have hh := (normalizer (T : Set G)).mul_mem hx.2 ((normalizer (T : Set G)).inv_mem (hnB hb))
    simpa only [mul_inv_cancel_right] using hh
  have hab : a ∈ B := by
    have hh : a ∈ d.Pstar ⊓ normalizer (T : Set G) := ⟨ha, han⟩
    rw [← d.borel_eq] at hh
    exact hh.2
  exact B.mul_mem hab hb

/-- A full-vertex overgroup of the marked starred Sylow either contains G*
or lies in the actual full Borel. -/
theorem source_overgroup_star_or_borel (d : LocalRankOneData P B)
    (M : Subgroup G) (hMP : M ≤ P)
    (hTM : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ M) :
    d.Pstar ≤ M ∨ M ≤ B := by
  rcases relative_rankOne_overgroup d.Pstar M (hMP.trans (star_normalized d)) d.sylow
    (star_sylow_proper d) hTM with hs | hn
  · exact Or.inl hs
  · exact Or.inr ((le_inf hMP hn).trans_eq (source_full_normalizer_star_sylow d))

/-- A normal non-two-closed subgroup of L supplements the actual Borel core.
The argument uses the starred rank-one overgroup theorem and the two-closed Borel. -/
theorem source_nonclosed_sup_borel_core (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (N : Subgroup G) (hNL : N ≤ localEnlargement d)
    (hclosed : ¬ ∃ T : Sylow 2 N, (T : Subgroup N) = pCore 2 N) :
    N ⊔ B.pCoreIn 2 = localEnlargement d := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hTS : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  rcases source_overgroup_star_or_borel d (N ⊔ B.pCoreIn 2)
    (sup_le (hNL.trans (localEnlargement_le d)) ((pCoreIn_le 2 B).trans hBP))
    (hTS.trans le_sup_right) with hs | hb
  · exact le_antisymm (sup_le hNL le_sup_right) (sup_le hs le_sup_right)
  · exact (hclosed (core_sylow_of_le B N (le_sup_left.trans hb) hB)).elim

/-- Source 6.2(a), with O² of the literal Chapter 6 enlargement and relative
normality in the full vertex group. No classification of the enlargement is assumed. -/
theorem source_nonclosed_contains_residual (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (N : Subgroup G) (hNL : N ≤ localEnlargement d)
    (hn : P ≤ normalizer (N : Set G))
    (hclosed : ¬ ∃ T : Sylow 2 N, (T : Subgroup N) = pCore 2 N) :
    (pResidual 2 (localEnlargement d)).map (localEnlargement d).subtype ≤ N := by
  let := d.finite_P
  let : Finite (localEnlargement d) :=
    Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let : (N.subgroupOf (localEnlargement d)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNL).mpr ((localEnlargement_le d).trans hn)
  have hs : N.subgroupOf (localEnlargement d) ⊔
      (B.pCoreIn 2).subgroupOf (localEnlargement d) = ⊤ := by
    rw [← subgroupOf_sup hNL (show B.pCoreIn 2 ≤ localEnlargement d from le_sup_right),
      source_nonclosed_sup_borel_core d hB N hNL hclosed, subgroupOf_self]
  have hr := (pResidual_le_iff_isPGroup_quotient 2 (N.subgroupOf (localEnlargement d))).mpr
    (isPGroup_quotient_of_sup_eq_top _ _ (isPGroup_pCoreIn 2 B).comap_subtype hs)
  exact (map_mono hr).trans_eq (map_subgroupOf_eq_of_le hNL)

/-- The opposite-core closure lies in the genuine local enlargement. -/
theorem core_closure_le_localEnlargement
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B) :
    conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) ≤ localEnlargement d := by
  let := d.finite_P
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  apply conjugateSpanBy_le _ (localEnlargement_normalized d)
  exact (pGroup_le_core_of_core_sylow B _
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB).trans le_sup_right

/-- Under 6.4's contrary normality assumption, the actual opposite-core
closure is not two-closed. Otherwise its normal Sylow traps the opposite
core in the second vertex core, contradicting full-overlap faithfulness. -/
theorem core_closure_not_closed_of_inter_normal
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))) =
        pCore 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) := by
  let d := Classical.choice (h.local_data (other i))
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans hBP)
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  intro hclosed
  exact core_not_le_of_inter_normal h i hn
    ((pGroup_le_core_of_core_sylow X _ (le_conjugateSpanBy _ _) (isPGroup_pCoreIn 2 _) hclosed).trans
      (pCoreIn_mono_of_normalizes hXP (le_normalizer_conjugateSpanBy _ _)))

/-- The residual and Sylow supplement premises for the literal 6.4 closure.
The SL₂ quotient and Sylow status of the opposite core remain further 6.4 obligations. -/
theorem core_closure_residual_of_inter_normal
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    (pResidual 2 (localEnlargement d)).map (localEnlargement d).subtype ≤ X ∧
      X ⊔ B.pCoreIn 2 = localEnlargement d := by
  have hXL := core_closure_le_localEnlargement h hB i d
  have hclosed := core_closure_not_closed_of_inter_normal h i hn
  exact ⟨source_nonclosed_contains_residual d hB _ hXL (le_normalizer_conjugateSpanBy _ _) hclosed,
    source_nonclosed_sup_borel_core d hB _ hXL hclosed⟩

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal Chapter 6 endpoint inside the original completion: the original
starred endpoint enlarged by the original full Borel's actual two-core. -/
def enlargedEndpoint (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) : Subgroup G :=
  starredParabolic L S i ⊔ (commonBorel L S).pCoreIn 2

/-- The constructed reduced local data give precisely the marked original
starred factor and full-Borel core, with no choice of a new model. -/
theorem reduced_localEnlargement_eq (h : HypothesisF11 L S) (i : Fin 2) :
    localEnlargement ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i) =
      enlargedEndpoint L S i := by
  rw [localEnlargement, HypothesisF11.starredLocalRankOneData_Pstar,
    SuzukiContainment.reduced_starredParabolic h i]
  change starredParabolic L S i ⊔ twoCore (commonBorel L (SuzukiContainment.reducedSylow L S)) =
    starredParabolic L S i ⊔ twoCore (commonBorel L S)
  rw [SuzukiContainment.reduced_borel_core h]
  rfl

/-- The enlarged endpoint retains the original parabolic's embedded core. -/
theorem enlargedEndpoint_core (h : HypothesisF11 L S) (i : Fin 2) :
    (enlargedEndpoint L S i).pCoreIn 2 = (parabolic L S i).pCoreIn 2 := by
  rw [← reduced_localEnlargement_eq h i, localEnlargement_core]
  exact SuzukiContainment.reduced_parabolic_core h i

/-- Actual source 6.2(a), with all local and Borel data constructed from F1.11.
The residual and N live inside the original completion, not a replacement carrier. -/
theorem reduced_nonclosed_contains_residual (h : HypothesisF11 L S) (i : Fin 2)
    (N : Subgroup G) (hNL : N ≤ enlargedEndpoint L S i)
    (hn : P₀ L S i ≤ normalizer (N : Set G))
    (hclosed : ¬ ∃ T : Sylow 2 N, (T : Subgroup N) = pCore 2 N) :
    (pResidual 2 (enlargedEndpoint L S i)).map (enlargedEndpoint L S i).subtype ≤ N := by
  let d := (SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i
  have hB : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup (commonBorel L (SuzukiContainment.reducedSylow L S))) =
        pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
    exact (normal_subgroupOf_iff_le_normalizer (show SuzukiContainment.reducedSylow L S ≤
      commonBorel L (SuzukiContainment.reducedSylow L S) from le_sup_right)).mp
      (SuzukiContainment.reduced_sylow_normal h)
  have hnd : parabolic L (SuzukiContainment.reducedSylow L S) i ≤ normalizer (N : Set G) := by
    rw [← P₀_eq_source h i]
    exact hn
  have hNLd : N ≤ localEnlargement d := hNL.trans (reduced_localEnlargement_eq h i).ge
  have hr := source_nonclosed_contains_residual d hB N hNLd hnd hclosed
  change (pResidual 2 (localEnlargement ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i))).map
    (localEnlargement ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i)).subtype ≤ N at hr
  rw [reduced_localEnlargement_eq h i] at hr
  exact hr

/-- The literal opposite-core closure in the reduced completion satisfies
the 6.4 residual and supplement premises under its stated contrary normality.
All graph, finite-local and normal-Sylow data are supplied by F1.11 reduction. -/
theorem reduced_core_closure_residual_of_inter_normal (h : HypothesisF11 L S) (i : Fin 2)
    (hn : (P₀ L S (other i)).subgroupOf (G₀ L S) ≤ normalizer
      ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    let d := Classical.choice ((reduced_triple h).local_data (other i))
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    (pResidual 2 (localEnlargement d)).map (localEnlargement d).subtype ≤ X ∧
      X ⊔ ((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2 = localEnlargement d :=
  core_closure_residual_of_inter_normal (reduced_triple h) (reduced_borel_core_sylow h) i
    (Classical.choice ((reduced_triple h).local_data (other i))) hn

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
