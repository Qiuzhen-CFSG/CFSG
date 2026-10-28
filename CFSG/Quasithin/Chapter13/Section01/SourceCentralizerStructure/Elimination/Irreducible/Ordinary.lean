module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryEven
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PSL3Parameters

/-!
# Ordinary components in the irreducible branch of original 13.1.12

The even linear-three rows, including all central covers, were excluded in
`OrdinaryEven`. In the odd row the original central Sylow involution supplies
a genuine marked action on the ordinary component. The proved odd PSL₃
parameter theorem forces p=3, contradicting the actual canonical prime.
Thus the source model list excludes the entire ordinary branch. Only that
model list is retained as an independent earlier input; its construction
belongs to the A.3.15 sieve, not to a model tag or exclusion callback.

Source: Aschbacher–Smith, 1.1.5(3), p.503; 13.1.12(3), p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding Chapter1.QuasisimpleInvolutions
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- A marked ordinary component cannot have the odd source linear-three quotient. -/
theorem Context.not_ordinary_odd_linear_three (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hq : IsQuasisimple K) : ¬ LinearThreeModel p (XiQuotient K) := by
  intro hm
  have hp := h.prime_gt_three
  have hp4 : p ≠ 4 := by
    obtain ⟨a,ha⟩ := h.odd
    omega
  have hmodel := e.ordinary_linear_three_model hq (by omega) hp4 hm
  obtain ⟨S,z,_,_,_,_,h115,_,_,_⟩ := h.ordinary_model_action c s e hq
  let H := centralizer ({u} : Set G)
  let D := K.subgroupOf H
  let : IsQuasisimple D := hq.of_mulEquiv (subgroupOfEquivOfLe e.component.1).symm
  have hD : IsComponent H D := ⟨e.component.2.subnormal,inferInstance⟩
  obtain ⟨_,α,P,_,d,_⟩ := h115.component_inputs D hD
  have hmodelD : ClassicalGroup.IsPSL D 3 p :=
    hmodel.of_mulEquiv (subgroupOfEquivOfLe e.component.1)
  have heq := d.linear_three_parameters p (Fact.out : p.Prime) h.odd
    (projective_center_model (by decide) hmodelD)
  omega

/-- The actual model sieve leaves no ordinary component in the irreducible branch. -/
theorem Context.not_ordinary_of_models (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hm : IrreducibleComponentModels p K) :
    ¬ IsQuasisimple K := by
  intro hq
  exact h.not_ordinary_odd_linear_three c s e hq (h.ordinary_model_odd s e hi hq hm)

/-- Hence an irreducible escape satisfying the source model sieve is characteristic two. -/
theorem Context.characteristic_two_of_models (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hm : IrreducibleComponentModels p K) :
    generalizedFitting K = pCore 2 K :=
  e.ordinary_or_characteristic_two.resolve_left (h.not_ordinary_of_models c s e hi hm)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
