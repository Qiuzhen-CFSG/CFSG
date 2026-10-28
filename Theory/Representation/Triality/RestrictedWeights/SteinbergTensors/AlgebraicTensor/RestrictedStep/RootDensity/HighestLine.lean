module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.RankOneLeft
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.Separation

/-!+# Highest-line inputs to D4 root-operator density

The negative-word span, positive common kernel, and joint positive nilpotence
are defined using the actual first coefficients of the pinned root actions.
A last nonzero positive word produces a primitive vector in every nonzero
invariant subspace. If the primitive space is the highest line, negative
cyclicity makes that subspace the entire representation. Jacobson density
then gives the full endomorphism algebra.

These are conditional reductions for the infinitesimal argument underlying
GLS3 Theorem 2.8.5 / Steinberg Theorem 13.1. The nonzero restricted cyclicity
and primitive-line inputs remain separate mathematical obligations. Individual
nilpotence of the root operators does not replace joint word nilpotence.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
namespace RootDensity
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The positive roots of the unchanged Borel. -/
abbrev PositiveRoot (S : D4Geometry K) := {α : S.roots.Root // α ∈ S.roots.positive}

/-- All words in negative first root coefficients, including the empty word. -/
def negativeRootSpan (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun l : List (PositiveRoot S) =>
    (l.map fun α => rootOperator S ρ hρ (S.roots.neg α.val)).prod v)

/-- The common kernel of all positive first root coefficients. -/
def positiveRootKernel (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Submodule k V :=
  ⨅ α : PositiveRoot S, LinearMap.ker (rootOperator S ρ hρ α.val)

/-- Uniform vanishing of sufficiently long positive words. -/
def HasNilpotentPositiveAction (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Prop :=
  ∃ n : ℕ, ∀ l : List (PositiveRoot S), l.length = n →
    (l.map fun α => rootOperator S ρ hρ α.val).prod = 0

/-- Stability under the actual first coefficients for every root. -/
def IsRootOperatorInvariant (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (U : Submodule k V) : Prop :=
  ∀ α v, v ∈ U → rootOperator S ρ hρ α v ∈ U

/-- Every genuine highest vector lies in the positive primitive space. -/
theorem highest_mem_positiveRootKernel (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {χ : TorusWeight S.torus} {v : V} (hv : HasHighWeight ρ S.borel S.torus v χ) :
    v ∈ positiveRootKernel S ρ hρ := by
  simp only [positiveRootKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  intro α
  exact positive_rootOperator_eq_zero_of_highWeight S ρ hρ hv α.val α.property

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem word_apply_mem {ι : Type*} (X : ι → Module.End k V)
    (U : Submodule k V) (hU : ∀ i v, v ∈ U → X i v ∈ U)
    (l : List ι) {v : V} (hv : v ∈ U) : (l.map X).prod v ∈ U := by
  induction l with
  | nil => simpa using hv
  | cons i l ih => simpa using hU i _ ih

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem exists_primitive_of_word_annihilation {ι : Type*}
    (X : ι → Module.End k V) (U : Submodule k V)
    (hU : ∀ i v, v ∈ U → X i v ∈ U)
    (n : ℕ) {v : V} (hvU : v ∈ U) (hv : v ≠ 0)
    (hkill : ∀ l : List ι, l.length = n → (l.map X).prod v = 0) :
    ∃ w ∈ U, w ≠ 0 ∧ ∀ i, X i w = 0 := by
  induction n generalizing v with
  | zero =>
    have hz := hkill [] rfl
    exact (hv (by simpa using hz)).elim
  | succ n ih =>
    by_cases h : ∀ i, X i v = 0
    · exact ⟨v, hvU, hv, h⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      apply ih (hU i v hvU) hi
      intro l hl
      have hz := hkill (l ++ [i]) (by simp [hl])
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Module.End.mul_apply] using hz

/-- The highest-line inputs force simplicity for the actual root operators. -/
theorem rootOperatorInvariant_eq_bot_or_top_of_highest_line (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) (v : V)
    (hspan : negativeRootSpan S ρ hρ v = ⊤)
    (hkernel : positiveRootKernel S ρ hρ = Submodule.span k {v})
    (hnil : HasNilpotentPositiveAction S ρ hρ)
    (U : Submodule k V) (hU : IsRootOperatorInvariant S ρ hρ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨z, hzU, hz0, hz⟩ := exists_primitive_of_word_annihilation
    (fun α : PositiveRoot S => rootOperator S ρ hρ α.val) U
    (fun α => hU α.val) n hw hw0 (fun l hl => by rw [hn l hl]; rfl)
  have hzk : z ∈ positiveRootKernel S ρ hρ := by
    simpa only [positiveRootKernel, Submodule.mem_iInf, LinearMap.mem_ker] using hz
  rw [hkernel] at hzk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzk
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hz0
    simpa [hzero] using hc.symm
  have hvU : v ∈ U := by
    have h := U.smul_mem c⁻¹ hzU
    rw [← hc, inv_smul_smul₀ hc0] at h
    exact h
  right
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact word_apply_mem (fun α : PositiveRoot S => rootOperator S ρ hρ (S.roots.neg α.val))
    U (fun α => hU (S.roots.neg α.val)) l hvU

/-- Jacobson density assembles the highest-line inputs into the desired
endomorphism-algebra equality. This theorem retains those inputs explicitly. -/
theorem rootOperatorAlgebra_eq_top_of_highest_line (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (v : V) (hv : v ≠ 0)
    (hspan : negativeRootSpan S ρ hρ v = ⊤)
    (hkernel : positiveRootKernel S ρ hρ = Submodule.span k {v})
    (hnil : HasNilpotentPositiveAction S ρ hρ) : rootOperatorAlgebra S ρ hρ = ⊤ := by
  let : Nontrivial V := ⟨⟨v, 0, hv⟩⟩
  exact adjoin_eq_top_of_irreducible_family _
    (rootOperatorInvariant_eq_bot_or_top_of_highest_line S ρ hρ v hspan hkernel hnil)

end
end RootDensity
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
