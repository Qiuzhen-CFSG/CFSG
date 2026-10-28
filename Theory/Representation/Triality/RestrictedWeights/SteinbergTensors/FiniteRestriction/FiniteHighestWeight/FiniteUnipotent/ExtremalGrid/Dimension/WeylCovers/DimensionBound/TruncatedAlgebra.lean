module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws

/-!
# Assembly tools for the truncated D4 coefficient algebra

The ordered root coefficients belong to the actual algebra, so their span is
contained in its orbit. The zero exponent tuple contains the original vector.
For the other normalization direction, generation reduces transport of the
whole algebra by the whole group to transport of each root coefficient by
signed simple-root points.

The coefficient laws are proved in `TruncatedAlgebra.CoefficientLaws`.
Normalization by root points and the reverse, triangular spanning inclusion
still require opposite-root and distinct-root relations; they are not asserted
here without those inputs. The final PBW assembly belongs in this module.

Source: Steinberg, *Representations of algebraic groups* (1963), §2;
GLS3/St2 13.2(d). The algebra includes all roots and all degrees below q.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Every ordered word is an element of the actual full coefficient algebra. -/
theorem orderedCoefficient_mem (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : Fin 12 → S.roots.Root)
    (q : ℕ) (a : Fin 12 → Fin q) :
    orderedCoefficient S rho hr r q a ∈ coefficientAlgebra S rho hr q := by
  apply list_prod_mem
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact rootCoefficient_mem S rho hr q (r i) (a i) (a i).isLt


/-- The easy inclusion, valid for any ordered twelve roots and any truncation. -/
theorem orderedCoefficientSpan_le_operatorOrbit (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (q : ℕ) (v : V) :
    orderedCoefficientSpan S rho hr r q v ≤
      operatorOrbit (coefficientAlgebra S rho hr q) v := by
  apply Submodule.span_le.mpr
  rintro w ⟨a, rfl⟩
  exact Submodule.subset_span
    ⟨⟨orderedCoefficient S rho hr r q a, orderedCoefficient_mem S rho hr r q a⟩, rfl⟩

/-- The zero tuple gives the original vector whenever the truncation is positive. -/
theorem mem_orderedCoefficientSpan (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (q : ℕ) (hq : 0 < q) (v : V) :
    v ∈ orderedCoefficientSpan S rho hr r q v := by
  have h : orderedCoefficient S rho hr r q (fun _ => ⟨0, hq⟩) = 1 := by
    simp [orderedCoefficient, rootCoefficient]
  exact Submodule.subset_span ⟨fun _ => ⟨0, hq⟩, congrArg (fun L : Module.End k V => L v) h⟩

/-- Global normalization reduces to transport of the actual coefficient
    generators by the actual signed simple-root points. -/
theorem coefficientAlgebra_normalizes_of_simpleRootTransport (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (q : ℕ)
    (hgen : Submonoid.closure (simpleRootPoints S) = ⊤)
    (hroot : ∀ g ∈ simpleRootPoints S, ∀ r : S.roots.Root, ∀ j : Fin q,
      ∃ b ∈ coefficientAlgebra S rho hr q,
        (rho.action g).val * rootCoefficient S rho hr r j = b * (rho.action g).val) :
    Normalizes rho (coefficientAlgebra S rho hr q) := by
  intro g a ha
  have hg : g ∈ Submonoid.closure (simpleRootPoints S) := hgen ▸ Submonoid.mem_top g
  have ht : ∀ a ∈ coefficientAlgebra S rho hr q,
      ∃ b ∈ coefficientAlgebra S rho hr q,
        (rho.action g).val * a = b * (rho.action g).val := by
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      intro a ha
      apply adjoin_intertwine_mem _ _ _ a ha
      rintro _ ⟨⟨r, j⟩, rfl⟩
      exact hroot g hg r j
    | one =>
      intro a ha
      exact ⟨a, ha, by simp⟩
    | mul g h _ _ hg hh =>
      intro a ha
      obtain ⟨b, hb, heb⟩ := hh a ha
      obtain ⟨c, hc, hec⟩ := hg b hb
      refine ⟨c, hc, ?_⟩
      simp only [map_mul, Units.val_mul]
      rw [mul_assoc, heb, ← mul_assoc, hec, mul_assoc]
  exact ht a ha
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
