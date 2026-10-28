module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.Separation
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.Conventions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft

/-!
# Root-operator density for restricted D4 left highest weights

A rational irreducible representation with zero highest weight is equivalent
to a trivial line. The checked highest-weight uniqueness theorem from the
opposite Borel big cell proves this using the line spanned by the given vector
as the comparison carrier; no universe restriction on the original space is
needed. Its submodules are therefore zero or the whole space, and the checked
Jacobson-density bridge applies to its actual root operators.

For every nonzero binary left highest weight, the actual negative root
coefficients span the representation from its highest vector. The positive
coefficients have that vector's line as their common kernel and are jointly
nilpotent. Thus every nonzero root-invariant subspace contains the highest
line and hence the whole representation. Jacobson density gives the full
endomorphism algebra, uniformly on arbitrary finite-dimensional carriers.

The final theorem discharges all of these inputs using
`RootDensity.NegativeCyclicityLeft` and `RootDensity.PositivePrimitivesLeft`.
It proves the restricted infinitesimal-simplicity input to GLS3,
Theorem 2.8.5 and Corollary 2.8.6(a) / [St2, Theorem 13.1], without assuming
any tensor or finite-restriction theorem. The source references are
`refs/KGroup/GLS3/chapter2.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
The raw character obstruction in `RootDensity.Conventions` remains a
separate diagnostic; it is not used to eliminate nonzero left weights.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

set_option backward.isDefEq.respectTransparency false in
private theorem trivial_rational_any :
    IsRationalRepresentation
      (algebraicAction (Representation.trivial k (Variety.Point K) V)) := by
  let f : Theory.AlgebraicGroup.Morphism K (glVarietyOf k V) :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := fun _ _ => (one_mul _).symm }
  refine ⟨Module.finBasis k V, f, ?_⟩
  intro g
  change glPointEquivOf k V (Module.finBasis k V) 1 = _
  rw [← generalLinearRepresentationPoint_one (Module.finBasis k V),
    glPointEquivOf_generalLinearRepresentationPoint]
  apply Units.ext
  rfl

/-- A rational irreducible module of zero highest weight is a line, on any carrier. -/
theorem finrank_eq_one_of_zero_highWeight (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    (v : V) (hv : HasHighWeight ρ S.borel S.torus v (S.weightEmbedding 0)) :
    Module.finrank k V = 1 := by
  let L := Submodule.span k {v}
  let w : L := ⟨v, Submodule.subset_span (Set.mem_singleton v)⟩
  have hw : w ≠ 0 := fun h => hv.1.1 (congrArg Subtype.val h)
  have hL : Module.finrank k L = 1 := finrank_span_singleton hv.1.1
  let τ := algebraicAction (Representation.trivial k (Variety.Point K) L)
  have hτ : IsIrreducibleRepresentation τ := by
    refine ⟨trivial_rational_any, fun U _ => ?_⟩
    let : IsSimpleOrder (Submodule k L) := is_simple_module_of_finrank_eq_one hL
    exact eq_bot_or_eq_top U
  have hzero : S.weightEmbedding 0 = 1 := S.characters.map_one
  have hhigh : HasHighWeight τ S.borel S.torus w (S.weightEmbedding 0) := by
    refine ⟨⟨hw, fun b _ => ⟨1, ?_⟩⟩, hw, fun t => ?_⟩
    · simp [τ, algebraicAction_apply, Representation.trivial]
    · rw [hzero]
      change w = (1 : k) • w
      rw [one_smul]
  obtain ⟨e, _⟩ := irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus ρ τ hρ hτ v w (S.weightEmbedding 0) hv hhigh
  exact e.finrank_eq.trans hL

/-- The zero restricted weight satisfies root-operator density. The scalar
endomorphisms already form the full endomorphism algebra of this line. -/
theorem rootOperatorAlgebra_eq_top_of_zero_highWeight (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v (S.weightEmbedding 0)) :
    rootOperatorAlgebra S ρ hρ.1 = ⊤ := by
  obtain ⟨v, hv⟩ := hv
  let : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  let : IsSimpleOrder (Submodule k V) := is_simple_module_of_finrank_eq_one
    (finrank_eq_one_of_zero_highWeight S ρ hρ v hv)
  exact adjoin_eq_top_of_irreducible_family _ (fun U _ => eq_bot_or_eq_top U)

open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

/-- Conditional assembly from the two restricted highest-line inputs. The zero
weight is unconditional. The nonzero cyclicity and primitive-action premises
must still be supplied; this is not the unconditional restricted theorem. -/
theorem rootOperatorAlgebra_eq_top_of_left_basic_inputs (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    (a : BasicWeight) (v : V)
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (hspan : a ≠ (fun _ => false) → RootDensity.negativeRootSpan S ρ hρ.1 v = ⊤)
    (hpositive : a ≠ (fun _ => false) → RootDensity.negativeRootSpan S ρ hρ.1 v = ⊤ →
      RootDensity.positiveRootKernel S ρ hρ.1 = Submodule.span k {v} ∧
        RootDensity.HasNilpotentPositiveAction S ρ hρ.1) :
    rootOperatorAlgebra S ρ hρ.1 = ⊤ := by
  by_cases ha : a = fun _ => false
  · apply rootOperatorAlgebra_eq_top_of_zero_highWeight S ρ hρ
    refine ⟨v, ?_⟩
    have hzero : coefficient a = 0 := by
      subst a
      funext i
      rfl
    simpa only [hzero, S.leftWeightEmbedding_eq_raw, neg_zero] using hv
  · obtain ⟨hkernel, hnil⟩ := hpositive ha (hspan ha)
    exact RootDensity.rootOperatorAlgebra_eq_top_of_highest_line S ρ hρ.1 v hv.1.1
      (hspan ha) hkernel hnil

/-- The actual first root coefficients generate every endomorphism of an
irreducible rational D4 representation of restricted left highest weight.
All binary weights, including zero, and arbitrary carrier universes are allowed;
no cyclicity, primitive-line, or nilpotence premise remains. -/
theorem rootOperatorAlgebra_eq_top_of_left_basic_highWeight [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) (a : BasicWeight)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v
      (S.leftWeightEmbedding (coefficient a))) :
    rootOperatorAlgebra S ρ hρ.1 = ⊤ := by
  obtain ⟨v, hv⟩ := hv
  exact rootOperatorAlgebra_eq_top_of_left_basic_inputs S ρ hρ a v hv
    (fun _ => RootDensity.negativeRootSpan_eq_top_of_left_basic_highWeight S ρ hρ hv)
    (fun ha hspan => RootDensity.positivePrimitives_of_left_basic_negative_span
      S ρ hρ ha hv hspan)

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
