module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.WeightNilpotence
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep.PolynomialExpansion

/-!
# Joint negative nilpotence on the actual cyclic quotient

All canonical root operators shift integral coroot weights. Hence their
algebra preserves the sum of the integral weight spaces, and the cyclic
submodule of a genuine highest vector lies in that sum. Only finitely many
integral weights occur in the ambient finite-dimensional factor. Negative
words strictly lower height, so a uniform sufficiently long word kills this
entire sum. Transport through the actual quotient map proves joint negative
nilpotence, and therefore properness of the sum of negative-root images.

No weight decomposition or negative cyclicity of the whole factor is assumed;
no rational action on the quotient is constructed or assumed.

Source: the integral-height argument of Steinberg, *Representations of
Algebraic Groups*, Nagoya Math. J. 22 (1963), §2, (2.8)–(2.9);
DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

namespace HighestLine

/-- The integral weight spaces need only span the cyclic submodule. -/
@[expose] def integralWeightSpan (B : AlgebraicFactor F) : Submodule F B.Space :=
  ⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ

private theorem rootOperator_mem_integralWeightSpan (B : AlgebraicFactor F)
    (p : RootExpansion B.action) (r : F4Chevalley.Root) {w : B.Space}
    (hw : w ∈ integralWeightSpan B) :
    EndNode.Multiplicity.rootOperator B r w ∈ integralWeightSpan B := by
  refine Submodule.iSup_induction (EndNode.corootWeightSpace B)
    (motive := fun x => EndNode.Multiplicity.rootOperator B r x ∈ integralWeightSpan B)
    hw ?_ ?_ ?_
  · intro μ x hx
    rw [← p.coeff_one_eq_rootOperator]
    exact Submodule.mem_iSup_of_mem _ (p.coeff_one_mem_corootWeightSpace r hx)
  · simpa only [map_zero] using (integralWeightSpan B).zero_mem
  · intro x y hx hy
    simpa only [map_add] using (integralWeightSpan B).add_mem hx hy

private theorem rootAlgebra_mem_integralWeightSpan (B : AlgebraicFactor F)
    (p : RootExpansion B.action) (a : rootAlgebra B) :
    ∀ w ∈ integralWeightSpan B, (a : Module.End F B.Space) w ∈ integralWeightSpan B := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨r, rfl⟩ := ha
    exact fun _ hw => rootOperator_mem_integralWeightSpan B p r hw
  | algebraMap c =>
    intro w hw
    exact (integralWeightSpan B).smul_mem c hw
  | add a c ha hc iha ihc =>
    intro w hw
    exact (integralWeightSpan B).add_mem (iha w hw) (ihc w hw)
  | mul a c ha hc iha ihc =>
    intro w hw
    exact iha _ (ihc w hw)

/-- Root-algebra cyclic vectors lie in the span of the ambient integral weights. -/
theorem cyclic_mem_integralWeightSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (w : cyclicSubmodule B v) :
    (w : B.Space) ∈ integralWeightSpan B := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp w.property
  rw [← ha]
  exact rootAlgebra_mem_integralWeightSpan B p a v
    (Submodule.mem_iSup_of_mem _ (EndNode.basicHighestWeightVector_mem_corootWeightSpace hv))

/-- A uniform negative-word bound on the entire sum of integral weight spaces. -/
theorem negative_words_vanish_on_integralWeightSpan (B : AlgebraicFactor F)
    (p : RootExpansion B.action) :
    ∃ N : ℕ, ∀ l : List NegativeRoot, l.length = N →
      ∀ w ∈ integralWeightSpan B,
        (l.map fun r => EndNode.Multiplicity.rootOperator B r.val).prod w = 0 := by
  classical
  let H := PositivePrimitives.weightHeight
  have hfinite := Submodule.finite_ne_bot_of_iSupIndep (EndNode.corootWeightSpace_iSupIndep B)
  obtain ⟨hi, hhi⟩ := (hfinite.image H).bddAbove
  obtain ⟨lo, hlo⟩ := (hfinite.image H).bddBelow
  refine ⟨(hi - lo).toNat + 1, ?_⟩
  intro l hl
  have hheight : H ((l.map fun r => PositivePrimitives.rootWeight r.val).sum) ≤
      -(l.length : ℤ) := by
    clear hl
    induction l with
    | nil => simp [H]
    | cons r l ih =>
      have hr : H (PositivePrimitives.rootWeight r.val) < 0 := by
        rw [PositivePrimitives.weightHeight_root]
        exact lt_of_le_of_ne (le_of_not_gt r.property)
          (typeF4RootPairing_base.height_ne_zero r.val)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
        List.sum_cons, map_add]
      omega
  intro w hw
  refine Submodule.iSup_induction (EndNode.corootWeightSpace B)
    (motive := fun y => (l.map fun r => EndNode.Multiplicity.rootOperator B r.val).prod y = 0)
    hw ?_ ?_ ?_
  · intro μ y hy
    by_contra hne
    have hy0 : y ≠ 0 := by intro hz; apply hne; simp [hz]
    have hμ : EndNode.corootWeightSpace B μ ≠ ⊥ := by
      intro hz
      exact hy0 (by simpa [hz] using hy)
    have hword := p.word_mem_corootWeightSpace (l.map Subtype.val) hy
    have hν : EndNode.corootWeightSpace B
        (μ + (l.map fun r => PositivePrimitives.rootWeight r.val).sum) ≠ ⊥ := by
      intro hz
      apply hne
      simpa only [List.map_map, Function.comp_def, p.coeff_one_eq_rootOperator,
        hz, Submodule.mem_bot] using hword
    have hb := hlo ⟨_, hν, rfl⟩
    have ha := hhi ⟨μ, hμ, rfl⟩
    simp only [map_add] at hb
    rw [hl] at hheight
    have hn := Int.self_le_toNat (hi - lo)
    omega
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz, add_zero]

end HighestLine

namespace SimpleCyclicQuotient
open HighestLine
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- The actual quotient inherits uniform negative-word vanishing from its
cyclic source. The bound requires no differential irreducibility of `B`. -/
theorem negative_words_vanish {b : BasicWeight}
    (hv : B.IsBasicHighestWeightVector b v) :
    ∃ N : ℕ, ∀ l : List NegativeRoot, l.length = N →
      (l.map fun r => Q.operator r.val).prod = 0 := by
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  obtain ⟨N, hN⟩ := negative_words_vanish_on_integralWeightSpan B p
  refine ⟨N, fun l hl => ?_⟩
  ext w
  obtain ⟨z, rfl⟩ := Q.surjective w
  let a : rootAlgebra B := (l.map fun r => rootGenerator B r.val).prod
  have ha : (a : Module.End F B.Space) =
      (l.map fun r => EndNode.Multiplicity.rootOperator B r.val).prod := by
    change (rootAlgebra B).val (l.map fun r => rootGenerator B r.val).prod = _
    rw [map_list_prod, List.map_map]
    rfl
  have hq : Q.rootAction a = (l.map fun r => Q.operator r.val).prod := by
    simp only [a, map_list_prod, List.map_map, Function.comp_def, rootAction_rootGenerator]
  have hz : (cyclicSubmodule B v).module.smul a z = 0 := by
    apply Subtype.ext
    change (a : Module.End F B.Space) (z : B.Space) = 0
    rw [ha]
    exact hN l hl z (cyclic_mem_integralWeightSpan p hv z)
  rw [← hq, Q.rootAction_projection, hz, map_zero]
  rfl

/-- The sum of all negative-root images in the actual simple quotient is proper. -/
theorem negativeImage_ne_top {b : BasicWeight}
    (hv : B.IsBasicHighestWeightVector b v) : Q.negativeImage ≠ ⊤ :=
  Q.negativeImage_ne_top_of_word_vanishing (Q.negative_words_vanish hv)

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
