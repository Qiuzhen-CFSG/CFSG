module
public import Theory.SpecificGroups.Triality.RadicalCoordinates.PositiveNormalization
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.RootCurves
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus

/-!
# Normality of the triality radical root products

Each Levi simple reflection permutes the positive roots outside its subsystem.
The actual Geck Weyl conjugation formula therefore makes its Weyl word normalize
both radical root products. Conjugating a positive simple curve by that word
gives the negative simple curve, so positive normalization also supplies the
negative Levi action. Coroot words scale root parameters without changing their
support. Together these generator actions prove normality inside the original
split parabolic, for every characteristic-two parameter including q = 2.

Source: the Chevalley relations in GLS3 §2.4 and the radical and parabolic
of Definition 2.6.4 and Theorem 2.6.5(g)
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat

private theorem reflected_support (a : Node) (i : Fin 4) (hi : i ∈ a.support)
    (j : Fin 12) (hj : rootSupport a j) :
    ∃ k, rootSupport a k ∧ rootReflection i (rootIndex j) = rootIndex k := by
  have htable : ∀ (i : Fin 4) (j : Fin 12), i ∈ a.support → rootSupport a j →
      ∃ k, rootSupport a k ∧ reflectionTable i (positiveIndex j) = positiveIndex k := by
    cases a <;> unfold Node.support rootSupport <;> decide +kernel
  obtain ⟨k, hk, he⟩ := htable i j hi hj
  refine ⟨k, hk, ?_⟩
  rw [← rootEnumeration_positiveIndex j, rootReflection,
    ← rootEnumeration_reflectionTable, he, rootEnumeration_positiveIndex]

/-- The Weyl words at Levi nodes preserve the radical root subgroup. -/
theorem weylWord_mem_rootSubgroup_normalizer (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i : Fin 4) (hi : i ∈ a.support) :
    weylWord P i 1 ∈ Subgroup.normalizer (rootSubgroup P a) := by
  apply mem_rootSubgroup_normalizer_of_curve_conj
  intro j hj t
  obtain ⟨k, hk, he⟩ := reflected_support a i hi j hj
  have hc : weylWord P i 1 * curve P j t * (weylWord P i 1)⁻¹ = curve P k t := by
    apply Subtype.ext
    change (weylWord P i 1).val * _ * (weylWord P i 1).val⁻¹ = _
    rw [curve_unit, RootConjugation.weylWord_rootCurveUnit_conjugation P hp, he]
    rfl
  rw [hc]
  exact curve_mem_rootSubgroup P a k hk t

private theorem weylWord_positive_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : ExtensionField P) :
    weylWord P i 1 * positiveRoot P i t * (weylWord P i 1)⁻¹ = negativeRoot P i t := by
  apply Subtype.ext
  have h := RootConjugation.weylWord_rootCurveUnit_conjugation P hp i
    (typeDSimpleRootIndex 2 i) t
  dsimp only [rootReflection] at h
  simp only [← typeDRootPairing_baseEquiv_val, ← RootPairing.indexNeg_neg,
    rootCurveUnit_simple, rootCurveUnit_neg_simple] at h
  exact h

/-- Negative Levi curves normalize the radical by Weyl transport of positive curves. -/
theorem negativeRoot_mem_rootSubgroup_normalizer (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i : Fin 4) (hi : i ∈ a.support) (s : ExtensionField P) :
    negativeRoot P i s ∈ Subgroup.normalizer (rootSubgroup P a) := by
  rw [← weylWord_positive_conjugate P hp i s]
  have hw := weylWord_mem_rootSubgroup_normalizer P hp a i hi
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw
    (positiveSubgroup_le_rootSubgroup_normalizer P hp a
      (positiveRoot_mem_positiveSubgroup P i s))) (Subgroup.inv_mem _ hw)

/-- The source root product is normal relative to its split parabolic. -/
theorem rootSubgroup_normal (P : Parameters) (hp : P.prime = 2) (a : Node) :
    ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal := by
  apply rootSubgroup_normal_of_generator_actions P hp a
  · intro i hi s j hj t
    exact (Subgroup.mem_normalizer_iff.mp
      (negativeRoot_mem_rootSubgroup_normalizer P hp a i hi s) _).mp
        (curve_mem_rootSubgroup P a j hj t)
  · intro i s j hj t
    rw [torusWord_curve_conjugate P hp]
    exact curve_mem_rootSubgroup P a j hj _
end Triality.Standard.RadicalCoordinates
