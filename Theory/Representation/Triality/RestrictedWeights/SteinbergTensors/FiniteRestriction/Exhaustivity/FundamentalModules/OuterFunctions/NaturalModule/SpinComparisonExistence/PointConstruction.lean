module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Data
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.PointConstruction.PresentationData
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.PointConstruction.TorusTransport
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.PointConstruction.SpinRelations

/-!
# Descent of root-word evaluation to the marked D4 point group

Root generation makes evaluation of words in arbitrary algebraic root
parametrizations surjective. A kernel inclusion therefore descends the
Clifford root evaluation to a genuine homomorphism on all source points.
Compatible simple coroot words give the complete raw torus formula, and
uniqueness of additive algebraic parametrizations supplies a scalar for every
original root curve.

The final theorem is conditional on three distinct mathematical inputs:
compatible source parameters, the reverse source kernel inclusion, and the
concrete Spin relations. None is asserted to follow merely from generation.
Unconditional existence remains the assembly obligation of this module.

Source: GLS3 Theorems 1.10.7(d), 1.12.1, 1.12.4 and Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg (6.1), `Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
namespace SpinComparisonExistence
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open PointConstruction

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Actual root generation gives surjectivity for any algebraic choices of
parameters. This is independent of their compatibility or relations. -/
theorem PointConstruction.sourceEvaluation_surjective (S : Geometry K)
    (p : ParameterFamily k S) : Function.Surjective (sourceEvaluation k S p) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← ClassBound.AmbientCount.TorusGeometry.rootSubgroupGenerated_eq_top S]
  apply (Subgroup.closure_le _).2
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨r, _, hr⟩ := hy
  obtain ⟨z, hz⟩ := (p r).toMulEquiv.surjective
    ((S.roots.rootSubgroup r).pointEquiv.symm ⟨y, hr⟩)
  obtain ⟨a, rfl⟩ : ∃ a, kPlusPoint a = z := ⟨_, kPlusPoint_coordinate z⟩
  refine ⟨x k (S.rootIndex r) a, ?_⟩
  rw [sourceEvaluation_x]
  change (S.roots.rootSubgroup r).includePoint ((p r).toMulEquiv (kPlusPoint a)) = y
  rw [hz]
  exact congrArg Subtype.val ((S.roots.rootSubgroup r).pointEquiv.apply_symm_apply ⟨y, hr⟩)

/-- Descend root evaluation, then recover the full marked torus and every
original root curve. The kernel inclusion is an explicit remaining premise. -/
def PointConstruction.rootwiseSpinHomOfKernel (S : Geometry K)
    (p : NormalizedParameters k S)
    (hker : (sourceEvaluation k S p.parameter).ker ≤ (spinEvaluation k).ker) :
    RootwiseSpinHom k S := by
  let f : K.Point →* Points k :=
    (sourceEvaluation k S p.parameter).liftOfSurjective
      (sourceEvaluation_surjective k S p.parameter) ⟨spinEvaluation k, hker⟩
  have hf (w : RootWord k) : f (sourceEvaluation k S p.parameter w) = spinEvaluation k w :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have scales : ∀ r : S.roots.Root, ∃ c : k,
      ∀ a, (S.rootParameter r).value a = (p.parameter r).value (c * a) := by
    intro r
    obtain ⟨c, ⟨_, hc⟩, _⟩ :=
      oneParameterParametrization_eq_rescale (p.parameter r) (S.rootParameter r)
    exact ⟨c, hc⟩
  choose c hc using scales
  refine ⟨f, ?_, c, ?_⟩
  · apply torus_eq_of_simpleCoroots S f
    intro i z
    rw [← p.coroot i z, hf, spinEvaluation_h]
  · intro r a
    rw [hc r a]
    simpa only [sourceEvaluation_x, spinEvaluation_x] using hf (x k (S.rootIndex r) (c r * a))

/-- Assemble the point comparison from a source presentation and the verified
Spin relations. Source presentation means the reverse kernel inclusion, not
merely that source evaluation kills the displayed relators. -/
theorem nonempty_rootwiseSpinHom_of_presentation (S : Geometry K)
    (p : NormalizedParameters k S)
    (hsource : (sourceEvaluation k S p.parameter).ker ≤ relationSubgroup k)
    (hspin : ∀ w, Relator k w → spinEvaluation k w = 1) :
    Nonempty (RootwiseSpinHom k S) := by
  have htarget : relationSubgroup k ≤ (spinEvaluation k).ker :=
    Subgroup.normalClosure_le_normal hspin
  exact ⟨rootwiseSpinHomOfKernel k S p (hsource.trans htarget)⟩

end SpinComparisonExistence
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
