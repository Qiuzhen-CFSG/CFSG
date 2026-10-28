module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.Relations

/-!
# Cartan closure from actual D4 coefficient relations

Jacobi expresses the opposite bracket for a root sum as the difference of
its two constituent opposite brackets (their sum in characteristic two).
Induction over the actual D4 base puts every opposite bracket in the span
of the four simple brackets. For the Cartan action on a root coefficient,
Jacobi reduces each nested nonopposite bracket to zero or that same root
coefficient. At the two exceptional roots, square-zero coefficients and
characteristic two make the bracket vanish.

The only additional premise is the exact nonopposite relation for the
published first coefficients. No Cartan containment, normalization, density,
or cyclicity is assumed. The positive roots and raw coroot conventions are
unchanged; the parent coefficient-bracket assembly must still establish the
nonopposite relations from actual root exchanges.

Sources: GLS3 §1.12, especially 1.12.1(b,e); Steinberg,
*Representations of Algebraic Groups* (1963), §§2 and 4.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
attribute [local instance] LieRing.ofAssociativeRing

private def rootVector (S : D4Geometry K) (α : S.roots.Root) : typeDRootSpan 4 :=
  (typeDRootPairing 2).root (S.rootEquiv α)

omit [IsAlgClosed k] in
private theorem rootVector_neg (S : D4Geometry K) (α : S.roots.Root) :
    rootVector S (S.roots.neg α) = -rootVector S α := by
  simp only [rootVector, S.based.2.2.1, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem bracket_of_root_sum (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    {α β γ : S.roots.Root}
    (hadd : rootVector S γ = rootVector S α + rootVector S β) :
    ⁅rootOperator S ρ hρ α, rootOperator S ρ hρ β⁆ = rootOperator S ρ hρ γ := by
  have hne : β ≠ S.roots.neg α := by
    intro he
    rw [he, rootVector_neg, add_neg_cancel] at hadd
    exact (typeDRootPairing 2).ne_zero (S.rootEquiv γ) hadd
  have hs : S.roots.add α β = some γ := (S.addition α β γ).mpr hadd
  simpa only [Ring.lie_def, hs] using hc α β hne

private theorem opposite_bracket_add (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    {α β γ : S.roots.Root}
    (hadd : rootVector S γ = rootVector S α + rootVector S β) :
    ⁅rootOperator S ρ hρ γ, rootOperator S ρ hρ (S.roots.neg γ)⁆ =
      ⁅rootOperator S ρ hρ α, rootOperator S ρ hρ (S.roots.neg α)⁆ -
        ⁅rootOperator S ρ hρ β, rootOperator S ρ hρ (S.roots.neg β)⁆ := by
  have hβ : rootVector S (S.roots.neg α) =
      rootVector S β + rootVector S (S.roots.neg γ) := by
    rw [rootVector_neg, rootVector_neg, hadd]
    abel
  have hα : rootVector S (S.roots.neg β) =
      rootVector S α + rootVector S (S.roots.neg γ) := by
    rw [rootVector_neg, rootVector_neg, hadd]
    abel
  rw [← bracket_of_root_sum S ρ hρ hc hadd, lie_lie,
    bracket_of_root_sum S ρ hρ hc hβ, bracket_of_root_sum S ρ hρ hc hα]

private theorem opposite_mem_of_base (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (j : TypeDRootIndex 4) (hj : j ∈ (typeDRootPairing_base 2).support) :
    ⁅rootOperator S ρ hρ (S.rootEquiv.symm j),
      rootOperator S ρ hρ (S.roots.neg (S.rootEquiv.symm j))⁆ ∈
        cartanOperators S ρ hρ := by
  obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
  have he : S.rootEquiv.symm j = simpleRoot S i := by
    have h := congrArg Subtype.val hi
    simpa only [typeDRootPairing_baseEquiv_val, simpleRoot] using
      congrArg S.rootEquiv.symm h.symm
  rw [he]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Every opposite bracket belongs to the span of the four simple Cartan
brackets, provided the actual nonopposite coefficients satisfy their relations. -/
theorem opposite_commutator_mem_cartan_of_relations [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ) (α : S.roots.Root) :
    rootOperator S ρ hρ α * rootOperator S ρ hρ (S.roots.neg α) -
      rootOperator S ρ hρ (S.roots.neg α) * rootOperator S ρ hρ α ∈
        cartanOperators S ρ hρ := by
  have hall (j : TypeDRootIndex 4) :
      ⁅rootOperator S ρ hρ (S.rootEquiv.symm j),
        rootOperator S ρ hρ (S.roots.neg (S.rootEquiv.symm j))⁆ ∈
          cartanOperators S ρ hρ := by
    apply (typeDRootPairing_base 2).induction_add j
    · intro j hj
      have he : S.rootEquiv.symm ((typeDRootPairing 2).reflectionPerm j j) =
          S.roots.neg (S.rootEquiv.symm j) := by
        apply S.rootEquiv.injective
        simp only [Equiv.apply_symm_apply, S.based.2.2.1]
      rw [he, S.realized.neg_neg, ← lie_skew]
      exact (cartanOperators S ρ hρ).neg_mem hj
    · exact opposite_mem_of_base S ρ hρ
    · intro a b c hab ha hb
      have hv : rootVector S (S.rootEquiv.symm c) =
          rootVector S (S.rootEquiv.symm a) + rootVector S (S.rootEquiv.symm b) := by
        simpa only [rootVector, Equiv.apply_symm_apply] using hab
      rw [opposite_bracket_add S ρ hρ hc hv]
      exact (cartanOperators S ρ hρ).sub_mem ha (opposite_mem_of_base S ρ hρ b hb)
  simpa only [Equiv.symm_apply_apply, Ring.lie_def] using hall (S.rootEquiv α)

private theorem nested_opposite_mem (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    (α γ : S.roots.Root) (hne : γ ≠ α)
    (L : Submodule k (Module.End k V)) (hγ : rootOperator S ρ hρ γ ∈ L) :
    ⁅rootOperator S ρ hρ α,
      ⁅rootOperator S ρ hρ (S.roots.neg α), rootOperator S ρ hρ γ⁆⁆ ∈ L := by
  have hn : γ ≠ S.roots.neg (S.roots.neg α) := by
    simpa only [S.realized.neg_neg] using hne
  have hh := hc (S.roots.neg α) γ hn
  change ⁅rootOperator S ρ hρ (S.roots.neg α), rootOperator S ρ hρ γ⁆ = _ at hh
  rw [hh]
  cases hs : S.roots.add (S.roots.neg α) γ with
  | none => simpa only [lie_zero] using L.zero_mem
  | some δ =>
    have hv : rootVector S δ = rootVector S (S.roots.neg α) + rootVector S γ :=
      (S.addition _ _ _).mp hs
    have hv' : rootVector S γ = rootVector S α + rootVector S δ := by
      rw [hv, rootVector_neg]
      abel
    rwa [bracket_of_root_sum S ρ hρ hc hv']

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem double_bracket_square_zero [CharP k 2]
    (A B : Module.End k V) (hA : A * A = 0) : ⁅⁅A, B⁆, A⁆ = 0 := by
  have htwo (C : Module.End k V) : C + C = 0 := by
    rw [← two_smul k C, show (2 : k) = 0 from CharTwo.two_eq_zero, zero_smul]
  calc
    ⁅⁅A, B⁆, A⁆ = (A * B * A + A * B * A) - (B * (A * A) + (A * A) * B) := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = 0 := by rw [hA, mul_zero, zero_mul, add_zero, sub_zero, htwo]

private theorem opposite_bracket_mem_root_line [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    (α γ : S.roots.Root) (L : Submodule k (Module.End k V))
    (hγ : rootOperator S ρ hρ γ ∈ L) :
    ⁅⁅rootOperator S ρ hρ α, rootOperator S ρ hρ (S.roots.neg α)⁆,
      rootOperator S ρ hρ γ⁆ ∈ L := by
  by_cases he : γ = α
  · subst γ
    rw [double_bracket_square_zero _ _ (rootOperator_square_zero S ρ hρ α)]
    exact L.zero_mem
  by_cases hn : γ = S.roots.neg α
  · subst γ
    rw [← lie_skew (rootOperator S ρ hρ α) (rootOperator S ρ hρ (S.roots.neg α)),
      neg_lie, double_bracket_square_zero _ _ (rootOperator_square_zero S ρ hρ _), neg_zero]
    exact L.zero_mem
  rw [lie_lie]
  apply L.sub_mem (nested_opposite_mem S ρ hρ hc α γ he L hγ)
  simpa only [S.realized.neg_neg] using
    nested_opposite_mem S ρ hρ hc (S.roots.neg α) γ hn L hγ

/-- Simple Cartan brackets preserve the span of the actual negative root
coefficients under the exact nonopposite coefficient relations. -/
theorem cartan_negative_commutator_mem_of_relations [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ) (i : Fin 4) (β : PositiveRoot S) :
    cartanOperator S ρ hρ i * rootOperator S ρ hρ (S.roots.neg β.val) -
      rootOperator S ρ hρ (S.roots.neg β.val) * cartanOperator S ρ hρ i ∈
        negativeOperators S ρ hρ := by
  exact opposite_bracket_mem_root_line S ρ hρ hc (simpleRoot S i) (S.roots.neg β.val)
    (negativeOperators S ρ hρ) (Submodule.subset_span ⟨β, rfl⟩)

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
