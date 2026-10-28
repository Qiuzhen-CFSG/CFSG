module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RankOne
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation

/-!
# Negative short-root words and local highest-string inputs

The published `shortNegativeSpan` contains its highest vector, is stable under
its negative short-root generators, and has the expected least-subspace
property. Commuting an endomorphism through a word reduces its stability to
its value on the initial vector and its commutators with these generators.

For an exceptional basic highest vector, long negative simple root groups
fix the vector, every negative simple-root orbit is affine in its first
coefficient, and each simple Weyl translate lies in the negative short-word
span. These assertions follow from the local rank-one polynomial argument;
no differential irreducibility or short-root density is assumed.

These are inputs to the negative-cyclicity assembly. Stability of the span
under all root operators and irreducibility under those operators remain
separate restricted-module obligations.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Stability under every actual first-degree root coefficient. -/
@[expose] def RootExpansion.IsRootOperatorInvariant {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (W : Submodule F B.Space) : Prop :=
  ∀ r : F4Chevalley.Root, ∀ w ∈ W, p.coeff r 1 w ∈ W

/-- The empty negative word is the initial vector. -/
theorem RootExpansion.mem_shortNegativeSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) : v ∈ p.shortNegativeSpan v := by
  exact Submodule.subset_span ⟨[], by simp⟩

/-- Prefixing a word proves stability under each negative short-root coefficient. -/
theorem RootExpansion.coeff_mem_shortNegativeSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) (r : ShortNegativeRoot)
    {w : B.Space} (hw : w ∈ p.shortNegativeSpan v) :
    p.coeff r.val 1 w ∈ p.shortNegativeSpan v := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, rfl⟩ := hw
    exact Submodule.subset_span ⟨r :: l, by simp⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (p.shortNegativeSpan v).add_mem ihx ihy
  | smul a w hw ih =>
    simpa only [map_smul] using (p.shortNegativeSpan v).smul_mem a ih

/-- The word span is the least subspace containing `v` and stable under its generators. -/
theorem RootExpansion.shortNegativeSpan_le {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) (W : Submodule F B.Space)
    (hv : v ∈ W)
    (hW : ∀ r : ShortNegativeRoot, ∀ w ∈ W, p.coeff r.val 1 w ∈ W) :
    p.shortNegativeSpan v ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact BasicDensity.word_apply_mem (fun r : ShortNegativeRoot => p.coeff r.val 1) W hW l hv

/-- Starting from a vector already in the word span cannot enlarge it. -/
theorem RootExpansion.shortNegativeSpan_le_of_mem {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) {w : B.Space}
    (hw : w ∈ p.shortNegativeSpan v) : p.shortNegativeSpan w ≤ p.shortNegativeSpan v := by
  exact p.shortNegativeSpan_le w _ hw (fun r _ hz => p.coeff_mem_shortNegativeSpan v r hz)

/-- Commuting an operator past negative words reduces its stability to its
value on the initial vector and its commutators with the generators. -/
theorem RootExpansion.shortNegativeSpan_stable_of_commutators {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) (A : Module.End F B.Space)
    (hv : A v ∈ p.shortNegativeSpan v)
    (hcomm : ∀ r : ShortNegativeRoot, ∀ w ∈ p.shortNegativeSpan v,
      (A * p.coeff r.val 1 - p.coeff r.val 1 * A) w ∈ p.shortNegativeSpan v) :
    ∀ w ∈ p.shortNegativeSpan v, A w ∈ p.shortNegativeSpan v := by
  have hword (l : List ShortNegativeRoot) :
      A ((l.map fun r => p.coeff r.val 1).prod v) ∈ p.shortNegativeSpan v := by
    induction l with
    | nil => simpa using hv
    | cons r l ih =>
      let w := (l.map fun r => p.coeff r.val 1).prod v
      have hw : w ∈ p.shortNegativeSpan v := Submodule.subset_span ⟨l, rfl⟩
      have hc := (p.shortNegativeSpan v).add_mem (hcomm r w hw)
        (p.coeff_mem_shortNegativeSpan v r ih)
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, sub_add_cancel,
        List.map_cons, List.prod_cons, w] using hc
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨l, rfl⟩ := hw; exact hword l
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (p.shortNegativeSpan v).add_mem ihx ihy
  | smul a w hw ih =>
    simpa only [map_smul] using (p.shortNegativeSpan v).smul_mem a ih


namespace NegativeCyclicity

/-- The exceptional basic coefficient vanishes at every geometrically long simple root. -/
theorem basicCoefficient_eq_zero_of_long (b : BasicWeight) (i : Fin 4)
    (hi : IsLongRoot (typeF4SimpleRootIndex i)) : basicCoefficient b i = 0 := by
  have hi' : i.val < 2 := (typeF4SimpleRootIndex_mem_pair_iff i).mp hi
  have h2 : i ≠ 2 := by intro h; subst i; norm_num at hi'
  have h3 : i ≠ 3 := by intro h; subst i; norm_num at hi'
  simp [basicCoefficient, h2, h3]

/-- Every basic simple coefficient is at most one. -/
theorem basicCoefficient_le_one (b : BasicWeight) (i : Fin 4) : basicCoefficient b i ≤ 1 := by
  simp only [basicCoefficient]
  split_ifs <;> omega

variable [CharP F 2]

/-- A long negative simple root group fixes an exceptional basic highest vector. -/
theorem negative_long_simple_fixed {B : AlgebraicFactor F} {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (i : Fin 4)
    (hi : IsLongRoot (typeF4SimpleRootIndex i)) (t : F) :
    (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v := by
  apply negative_simple_fixed_of_zero B i v
  · exact hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i).property)
  · intro s
    simpa only [basicCoefficient_eq_zero_of_long b i hi, pow_zero, one_smul] using hv.2.2 i s

/-- Consequently its first lowering coefficient is zero. -/
theorem negative_long_simple_coeff_one_eq_zero {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (i : Fin 4)
    (hi : IsLongRoot (typeF4SimpleRootIndex i)) :
    p.coeff (-typeF4SimpleRootIndex i) 1 v = 0 :=
  p.coeff_one_eq_zero_of_fixed _ v (negative_long_simple_fixed hv i hi)

/-- Every negative simple-root orbit of a basic highest vector is affine. -/
theorem negative_simple_action_basic {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (i : Fin 4) (t : F) :
    (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v + t • p.coeff (-typeF4SimpleRootIndex i) 1 v := by
  have hp := hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property)
  have hbound := basicCoefficient_le_one b i
  by_cases h0 : basicCoefficient b i = 0
  · have ht : ∀ s : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) s) :
        Module.End F B.Space) v = v := by
      intro s
      simpa only [h0, pow_zero, one_smul] using hv.2.2 i s
    have hfix := negative_simple_fixed_of_zero B i v hp ht
    rw [hfix, p.coeff_one_eq_zero_of_fixed _ v hfix, smul_zero, add_zero]
  · have h1 : basicCoefficient b i = 1 := by omega
    exact negative_simple_action_of_one B p i v hp
      (fun s => by simpa only [h1, pow_one] using hv.2.2 i s) t

/-- The opposite of a short simple root is one of the published negative short roots. -/
@[expose] def shortNegativeSimple (i : Fin 4) (hi : ¬ IsLongRoot (typeF4SimpleRootIndex i)) :
    ShortNegativeRoot :=
  ⟨-typeF4SimpleRootIndex i, (isShortRoot_neg_iff _).mpr hi, by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not.mpr (typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i).property)⟩

/-- Every simple Weyl translate of the highest vector already lies in the
negative short-word span. -/
theorem simple_weyl_mem_shortNegativeSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (i : Fin 4) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
      Module.End F B.Space) v ∈ p.shortNegativeSpan v := by
  have hp := hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property)
  have hbound := basicCoefficient_le_one b i
  by_cases h0 : basicCoefficient b i = 0
  · rw [simple_weyl_fixed_of_zero B i v hp
      (fun s => by simpa only [h0, pow_zero, one_smul] using hv.2.2 i s)]
    exact p.mem_shortNegativeSpan v
  · have h1 : basicCoefficient b i = 1 := by omega
    have hi : ¬ IsLongRoot (typeF4SimpleRootIndex i) := by
      intro hlong
      exact h0 (basicCoefficient_eq_zero_of_long b i hlong)
    rw [simple_weyl_eq_coeff_one B p i v hp
      (fun s => by simpa only [h1, pow_one] using hv.2.2 i s)]
    exact p.coeff_mem_shortNegativeSpan v (shortNegativeSimple i hi) (p.mem_shortNegativeSpan v)

end NegativeCyclicity
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
