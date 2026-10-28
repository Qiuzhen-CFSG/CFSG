module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorInnerWeakClosure
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOuterWeakClosure.NonFF
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOuterWeakClosure

/-!
# The tensor weak-closure contradiction from original point normality

Whole conjugates of the full module lying in the original Sylow subgroup
centralize it: otherwise the non-FF automizer obstruction E.3.11 supplies
reverse nonnormalization, and the inner and outer tensor actor branches
both give a contradiction. This proves the zero-corank weak-closure case
before it is used anywhere in the corank-one argument.

The zero case gives the normalization equivalences of E.3.25. These yield
the same reverse nonnormalization for any noncentralizing corank-at-most-one
actor in the Sylow subgroup, so the two actor branches prove centralization
again. The first two weak closures therefore centralize the full module,
and the extended weak-closure parameter is greater than one.

The actual H-star generation bound then excludes a generation-one tensor
model. These results retain original nonsingular-point normality as their
one independent earlier-source premise. Its guarded source producer must
use the same H-star subgroup and generation-one hypothesis as the final
contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 9.4.4–5, printed pp.736–737; E.3.11 and E.3.25;
the original generation bound E.3.35–36, printed pp.238–239.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

section PointNormality

variable (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
  centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G))
include m hpoint

private theorem tensor_actor_centralizes_of_not_normalizes (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAT : A ≤ (T : Subgroup G))
    (hnot : ¬ D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G)) :
    A ≤ centralizer (D.fullModule : Set G) := by
  have hr := m.tensor_globalR_gt_three_of_point_normality hpoint
  by_cases hinner : (A.subgroupOf D.maximalLocal).map m.maximalAction ≤ Binary.linearAction.range
  · exact m.tensor_inner_actor_centralizes hr g hAW hcor hAT hinner
  · exact (m.tensor_outer_actor_false hpoint hr g hAW hcor hAT hnot hinner).elim

/-- Whole conjugates in the original Sylow centralize the original full module. -/
theorem tensor_weakClosure_zero_centralizes_of_point_normality :
    indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤ centralizer (D.fullModule : Set G) := by
  let := m.fullModule_elementary
  have hTN : (T : Subgroup G) ≤ normalizer (D.fullModule : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hWT⟩ := (mem_gamma_zero_iff D.fullModule (T : Subgroup G) A).mp hA
  by_contra hn
  have hcomm : ⁅D.fullModule, D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro h
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h))
  have hnot := lemma_E_3_11 D.fullModule g m.fullModule_automizer_notFF
    (hWT.trans hTN) hcomm
  exact hn (m.tensor_actor_centralizes_of_not_normalizes hpoint g le_rfl
    (by simp [subgroupCorank]) hWT hnot)

/-- The zero weak closure supplies the reverse-normalization exclusion for
any noncentralizing subgroup of a conjugate. -/
theorem tensor_corank_one_actor_centralizes_of_point_normality (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAT : A ≤ (T : Subgroup G)) : A ≤ centralizer (D.fullModule : Set G) := by
  let := m.fullModule_elementary
  have hTN : (T : Subgroup G) ≤ normalizer (D.fullModule : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  have hzero := m.tensor_weakClosure_zero_centralizes_of_point_normality hpoint
  by_contra hn
  have hnot : ¬ D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro h
    have he := conjugate_normalization_equivalences_of_weakClosure_zero hTN hzero g
    exact hn (hAW.trans (he.2.1.mpr (he.2.2.mpr h)))
  exact hn (m.tensor_actor_centralizes_of_not_normalizes hpoint g hAW hcor hAT hnot)

/-- The first weak closure also centralizes the original full module. -/
theorem tensor_weakClosure_one_centralizes_of_point_normality :
    indexedWeakClosure D.fullModule (T : Subgroup G) 1 ≤ centralizer (D.fullModule : Set G) := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g, hAW, hi⟩, hAT⟩
  apply m.tensor_corank_one_actor_centralizes_of_point_normality hpoint g hAW _ hAT
  change Nat.log 2 (A.relIndex (D.fullModule.map (MulAut.conj g).toMonoidHom)) ≤ 1
  rw [hi]
  decide

/-- The original weak-closure parameter is strictly greater than one. -/
theorem tensor_globalW_gt_one_of_point_normality :
    1 < globalW D.fullModule (T : Subgroup G) := by
  apply lt_of_not_ge
  intro h
  rcases Order.le_one_iff.mp h with hzero | hone
  · have he := globalW_attained (n := 0) hzero
    exact he (le_inf (indexedWeakClosure_le D.fullModule (T : Subgroup G) 0)
      (m.tensor_weakClosure_zero_centralizes_of_point_normality hpoint))
  · have he := globalW_attained (n := 1) hone
    exact he (le_inf (indexedWeakClosure_le D.fullModule (T : Subgroup G) 1)
      (m.tensor_weakClosure_one_centralizes_of_point_normality hpoint))

/-- A generation-one H-star subgroup contradicts the original tensor
model once point normality is available. -/
theorem tensor_generation_one_false_of_point_normality
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) : False := by
  have hb := source_overgroup_generation_bound D hH.1.1.2 hH.1.2
    (show 0 < generationParameter H by omega)
  rw [hgen, Nat.cast_one] at hb
  have hr := m.tensor_globalR_gt_three_of_point_normality hpoint
  have hw := m.tensor_globalW_gt_one_of_point_normality hpoint
  have hmin : (1 : ℕ∞) < min (globalW D.fullModule (T : Subgroup G))
      (globalR D.fullModule) :=
    lt_min hw ((by norm_num : (1 : ℕ∞) < 3).trans hr)
  exact (not_le_of_gt hmin) hb

end PointNormality

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
