module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.WeylTransport.RootTransport
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# Weyl closure of the negative short-word span

Conjugation in the actual algebraic carrier passes to first coefficients by
polynomial uniqueness. A simple Weyl representative is an involution in
characteristic two. Its translate of a basic highest vector belongs to the
negative short-word span by the local highest-string theorem.

If every short coefficient preserves this span, moving a Weyl representative
past each negative word proves Weyl stability. Positive-root stability then
implies stability under all negative roots: positive-root height induction
transports the negative simple-root operators by simple reflections. This is
the Weyl-reflection part of the source argument, retaining actual degree-one
operators throughout. The weight-zero and weight-one strings also determine
the simple Cartan action on the highest vector without another premise.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance spanInvarianceWeylNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

namespace NegativeCyclicity.SpanInvariance

/-- Simple Weyl covariance for the actual first-degree coefficients. -/
theorem coeff_one_simple_weyl {B : AlgebraicFactor F} (p : RootExpansion B.action)
    (i : Fin 4) (r : F4Chevalley.Root) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) *
      p.coeff r 1 =
    p.coeff (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) 1 *
      (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) := by
  rw [p.coeff_one_eq_rootOperator, p.coeff_one_eq_rootOperator]
  let N : Module.End F B.Space :=
    B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1)
  have h := EndNode.Multiplicity.rootOperator_intertwine B r
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) N N (1 : F) (by
      intro t v
      have he := congrArg (fun g => (B.action.action g : Module.End F B.Space) v)
        (EndNode.root_n_commute i
          (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t).symm
      simpa only [map_mul, Units.val_mul, Module.End.mul_apply,
        typeF4RootPairing.reflectionPerm_self, one_mul] using he)
  simpa only [one_smul] using h

/-- A simple Weyl representative acts as an involution in characteristic two. -/
theorem simple_weyl_squared {B : AlgebraicFactor F} (i : Fin 4) (v : B.Space) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space)
      ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) v) =
    v := by
  have hn : (algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1)⁻¹ =
      algebraicNElement (typeF4SimpleRootIndex i) 1 := by
    simp only [algebraicNElement, mul_inv_rev, ZeroAndMiddle.root_inv,
      CharTwo.neg_eq, mul_assoc]
  have hs : algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1 *
      algebraicNElement (typeF4SimpleRootIndex i) 1 = 1 := by
    simpa only [hn] using inv_mul_cancel (algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1)
  rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, hs,
    map_one, Units.val_one, Module.End.one_apply]

/-- The simple Cartan commutator has the prescribed basic eigenvalue on the highest vector. -/
theorem simple_cartan_on_highest {B : AlgebraicFactor F} (p : RootExpansion B.action)
    {b : BasicWeight} {v : B.Space} (hv : B.IsBasicHighestWeightVector b v) (i : Fin 4) :
    (p.coeff (typeF4SimpleRootIndex i) 1 * p.coeff (-typeF4SimpleRootIndex i) 1 -
      p.coeff (-typeF4SimpleRootIndex i) 1 * p.coeff (typeF4SimpleRootIndex i) 1) v =
        (basicCoefficient b i : F) • v := by
  have hp := hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property)
  have hz : p.coeff (typeF4SimpleRootIndex i) 1 v = 0 :=
    p.coeff_one_eq_zero_of_fixed _ v hp
  by_cases h0 : basicCoefficient b i = 0
  · have hm := p.coeff_one_eq_zero_of_fixed _ v
      (negative_simple_fixed_of_zero B i v hp (fun t => by
        simpa only [h0, pow_zero, one_smul] using hv.2.2 i t))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hz, hm, map_zero, sub_self,
      h0, Nat.cast_zero, zero_smul]
  · have h1 : basicCoefficient b i = 1 := by
      have := basicCoefficient_le_one b i
      omega
    have hn := simple_weyl_eq_coeff_one B p i v hp
      (fun t => by simpa only [h1, pow_one] using hv.2.2 i t)
    have he := congrArg (fun A : Module.End F B.Space => A v)
      (coeff_one_simple_weyl p i (-typeF4SimpleRootIndex i))
    simp only [RootPairing.indexNeg_neg, RootPairing.reflectionPerm_self,
      Module.End.mul_apply] at he
    change (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space)
        (p.coeff (-typeF4SimpleRootIndex i) 1 v) =
      p.coeff (typeF4SimpleRootIndex i) 1
        ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) v) at he
    rw [← hn, simple_weyl_squared] at he
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      hz, map_zero, sub_zero, ← hn, ← he, h1, Nat.cast_one, one_smul]

/-- Short-operator stability and the local highest strings imply simple Weyl stability. -/
theorem simple_weyl_stable_of_short_stable {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hshort : ∀ r : F4Chevalley.Root, ¬ IsLongRoot r →
      ∀ w ∈ p.shortNegativeSpan v, p.coeff r 1 w ∈ p.shortNegativeSpan v)
    (i : Fin 4) : ∀ w ∈ p.shortNegativeSpan v,
      (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) w ∈
        p.shortNegativeSpan v := by
  let N : Module.End F B.Space :=
    B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1)
  apply p.shortNegativeSpan_le v ((p.shortNegativeSpan v).comap N)
  · exact simple_weyl_mem_shortNegativeSpan p hv i
  · intro s w hw
    change N (p.coeff s.val 1 w) ∈ p.shortNegativeSpan v
    have he := congrArg (fun A : Module.End F B.Space => A w)
      (coeff_one_simple_weyl p i s.val)
    rw [show N (p.coeff s.val 1 w) =
      p.coeff (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) s.val) 1 (N w) from he]
    exact hshort _ ((WordRelations.ShortOperators.isShortRoot_reflection _ _).mpr s.property.1)
      _ hw

/-- Weyl conjugation transfers stability from one root coefficient to its reflection. -/
theorem reflected_coeff_stable {B : AlgebraicFactor F} (p : RootExpansion B.action)
    (W : Submodule F B.Space) (i : Fin 4) (r : F4Chevalley.Root)
    (hN : ∀ w ∈ W,
      (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) w ∈ W)
    (hr : ∀ w ∈ W, p.coeff r 1 w ∈ W) :
    ∀ w ∈ W, p.coeff (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) 1 w ∈ W := by
  intro w hw
  have h := hN _ (hr _ (hN w hw))
  have he := congrArg (fun A : Module.End F B.Space => A
    ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) : Module.End F B.Space) w))
    (coeff_one_simple_weyl p i r)
  simp only [Module.End.mul_apply, simple_weyl_squared] at he
  exact he ▸ h

private theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) = -(typeF4RootPairing.reflectionPerm i r) := by
  apply typeF4RootPairing.root.injective
  have hn (s : F4Chevalley.Root) : typeF4RootPairing.root (-s) = -typeF4RootPairing.root s := by
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [RootPairing.root_reflectionPerm, hn, hn, map_neg, RootPairing.root_reflectionPerm]

/-- Positive stability suffices: the negative branch follows by simple Weyl reflections. -/
theorem rootOperatorInvariant_of_positive_stable {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hpos : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r →
      ∀ w ∈ p.shortNegativeSpan v, p.coeff r 1 w ∈ p.shortNegativeSpan v) :
    p.IsRootOperatorInvariant (p.shortNegativeSpan v) := by
  have hshort : ∀ r : F4Chevalley.Root, ¬ IsLongRoot r →
      ∀ w ∈ p.shortNegativeSpan v, p.coeff r 1 w ∈ p.shortNegativeSpan v := by
    intro r hr
    by_cases hp : typeF4RootPairing_base.IsPos r
    · exact hpos r hp
    · exact fun _ hw => p.coeff_mem_shortNegativeSpan v ⟨r, hr, hp⟩ hw
  have hN := simple_weyl_stable_of_short_stable p hv hshort
  have hneg (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
      ∀ w ∈ p.shortNegativeSpan v, p.coeff (-r) 1 w ∈ p.shortNegativeSpan v := by
    apply hr.induction_on_reflect
    · intro s hs
      obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨s, hs⟩
      have he : typeF4SimpleRootIndex i = s := congrArg Subtype.val hi
      subst s
      exact reflected_coeff_stable p _ i _ (hN i)
        (hpos _ (typeF4RootPairing_base.isPos_of_mem_support
          (typeF4RootPairing_baseEquiv i).property))
    · intro s j ih hj
      obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨j, hj⟩
      have he : typeF4SimpleRootIndex i = j := congrArg Subtype.val hi
      subst j
      simpa only [reflection_neg] using reflected_coeff_stable p _ i (-s) (hN i) ih
  intro r
  rcases RootPairing.Base.IsPos.or_neg typeF4RootPairing_base r with hr | hr
  · exact hpos r hr
  · simpa only [neg_neg] using hneg (-r) hr

end NegativeCyclicity.SpanInvariance
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor

