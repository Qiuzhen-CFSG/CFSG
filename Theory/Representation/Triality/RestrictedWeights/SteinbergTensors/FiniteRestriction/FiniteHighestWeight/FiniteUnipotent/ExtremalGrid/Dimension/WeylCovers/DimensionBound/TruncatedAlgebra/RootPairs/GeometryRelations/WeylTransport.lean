module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.GeometryRelations.D4Combinatorics
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.SimpleRootOrbits.PointGeneration
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore

/-!
# Actual Weyl transport of chosen root parameters

Root-subgroup uniqueness identifies the conjugates under chart-derived words.
The algebraic one-parameter isomorphism theorem compares the supplied parameters
with the conjugated parameters by a nonzero scalar. Products of these same words
therefore transport all roots simultaneously, with their individual rescalings.
No compatible Chevalley parametrizations are assumed.

Sources: GLS3, Propositions 1.3.5(a), 1.9.2 and Theorem 1.12.1(h).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
open ClassBound ClassBound.FixedOpposition.AmbientNormalizer
open CorootRealization
public noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [CharP k 2] in
theorem conjugate_parameter (X Y : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety) (g : K.Point)
    (h : X.conjugate g = Y) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      g * X.includePoint (x.value t) * g⁻¹ = Y.includePoint (y.value (c * t)) := by
  subst Y
  obtain ⟨c, hc, _⟩ := oneParameterParametrization_eq_rescale y ((X.conjugateIso g).comp x)
  refine ⟨c, hc.1, fun t => ?_⟩
  rw [← hc.2 t]
  exact (X.conjugateIso_hom_inclusion_apply g (x.value t)).symm

@[expose] def wordAction (S : Geometry K) (w : List (Fin 4)) : Equiv.Perm S.roots.Root :=
  (S.rootIndex.trans (d4Word w)).trans S.rootIndex.symm

omit [IsAlgClosed k] in
theorem wordAction_nil (S : Geometry K) (a : S.roots.Root) : wordAction S [] a = a :=
  S.rootIndex.symm_apply_apply a

omit [IsAlgClosed k] in
theorem wordAction_cons (S : Geometry K) (i : Fin 4) (w : List (Fin 4))
    (a : S.roots.Root) :
    wordAction S (i :: w) a = S.roots.reflect (S.simpleRoot i).val (wordAction S w a) := by
  apply S.rootIndex.injective
  simp only [wordAction, Equiv.trans_apply, Equiv.apply_symm_apply, d4Word]
  rw [S.based.2.1, S.simpleRoot_index]
  simp only [Equiv.apply_symm_apply]

@[expose] def wordPoint {S : Geometry K} (D : SimpleCorootWordData S) : List (Fin 4) → K.Point
  | [] => 1
  | i :: w => (D.parameters i).word 1 * wordPoint D w

theorem simpleWord_parameter (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (i : Fin 4) (a : S.roots.Root) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      (D.parameters i).word 1 * (rootCurve S a).onPoints (kPlusPoint t) *
        ((D.parameters i).word 1)⁻¹ =
      (rootCurve S (S.roots.reflect (S.simpleRoot i).val a)).onPoints (kPlusPoint (c * t)) := by
  exact conjugate_parameter _ _ (S.rootParameter a) (S.rootParameter _)
    _ (simpleWord_conjugate_rootSubgroup_of_unique S hu D i a)

theorem word_parameter (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (w : List (Fin 4)) (a : S.roots.Root) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      wordPoint D w * (rootCurve S a).onPoints (kPlusPoint t) * (wordPoint D w)⁻¹ =
      (rootCurve S (wordAction S w a)).onPoints (kPlusPoint (c * t)) := by
  induction w with
  | nil => exact ⟨1, one_ne_zero, by simp [wordPoint, wordAction_nil]⟩
  | cons i w ih =>
    obtain ⟨c, hc, he⟩ := ih
    obtain ⟨d, hd, hf⟩ := simpleWord_parameter S hu D i (wordAction S w a)
    refine ⟨d * c, mul_ne_zero hd hc, fun t => ?_⟩
    rw [wordPoint, wordAction_cons]
    calc
      _ = (D.parameters i).word 1 *
          (wordPoint D w * (rootCurve S a).onPoints (kPlusPoint t) * (wordPoint D w)⁻¹) *
            ((D.parameters i).word 1)⁻¹ := by group
      _ = _ := by rw [he, hf, mul_assoc]

omit [IsAlgClosed k] in
theorem wordAction_neg (S : Geometry K) (w : List (Fin 4)) (a : S.roots.Root) :
    wordAction S w (S.roots.neg a) = S.roots.neg (wordAction S w a) := by
  apply S.rootIndex.injective
  simp only [wordAction, Equiv.trans_apply, Equiv.apply_symm_apply, S.based.2.2.1,
    d4Word_neg]

omit [IsAlgClosed k] in
theorem wordAction_sum_iff (S : Geometry K) (w : List (Fin 4)) (a b c : S.roots.Root) :
    RootSum S (wordAction S w a) (wordAction S w b) (wordAction S w c) ↔
      RootSum S a b c := by
  simp only [RootSum, wordAction, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact d4Word_sum_iff w _ _ _

omit [IsAlgClosed k] in
theorem wordAction_to_simple (S : Geometry K) (a : S.roots.Root) :
    ∃ (w : List (Fin 4)) (i : Fin 4), wordAction S w a = (S.simpleRoot i).val := by
  obtain ⟨w, i, hi⟩ := d4Word_to_simple (S.rootIndex a)
  refine ⟨w, i, S.rootIndex.injective ?_⟩
  simpa only [wordAction, Equiv.trans_apply, Equiv.apply_symm_apply, S.simpleRoot_index] using hi


omit [IsAlgClosed k] in
theorem rootSum_ne (S : Geometry K) {a b c : S.roots.Root} (hs : RootSum S a b c) :
    a ≠ b := fun h => d4_sum_ne _ _ _ hs (congrArg S.rootIndex h)

omit [IsAlgClosed k] in
theorem rootSum_nonopposite (S : Geometry K) {a b c : S.roots.Root}
    (hs : RootSum S a b c) : b ≠ S.roots.neg a := by
  intro h
  have hi := congrArg S.rootIndex h
  rw [S.based.2.2.1] at hi
  exact d4_sum_nonopposite _ _ _ hs hi

omit [IsAlgClosed k] in
theorem rootSum_reflection (S : Geometry K) {a b c : S.roots.Root}
    (hs : RootSum S a b c) : S.roots.reflect a b = c := by
  apply S.rootIndex.injective
  rw [S.based.2.1]
  exact d4_sum_reflection _ _ _ hs

omit [IsAlgClosed k] in
theorem rootSum_right_ne (S : Geometry K) {a b c : S.roots.Root}
    (hs : RootSum S a b c) : c ≠ b := by
  intro h
  apply (typeDRootPairing 2).ne_zero (S.rootIndex a)
  have he : (typeDRootPairing 2).root (S.rootIndex a) +
      (typeDRootPairing 2).root (S.rootIndex b) =
      0 + (typeDRootPairing 2).root (S.rootIndex b) := by
    rw [zero_add, ← hs, h]
  exact add_right_cancel he

omit [IsAlgClosed k] in
theorem rootSum_no_difference (S : Geometry K) {a b c : S.roots.Root}
    (hs : RootSum S a b c) : ¬ ∃ d, RootSum S (S.roots.neg a) b d := by
  rintro ⟨d, hd⟩
  apply d4_sum_no_difference _ _ _ hs
  refine ⟨S.rootIndex d, ?_⟩
  change (typeDRootPairing 2).root (S.rootIndex d) =
    (typeDRootPairing 2).root (S.rootIndex (S.roots.neg a)) +
      (typeDRootPairing 2).root (S.rootIndex b) at hd
  rwa [S.based.2.2.1] at hd


end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
