module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.LinearAlgebra
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.Coefficients

/-!
# The highest-line reduction for short-root density

Negative short-root words spanning from a vector and a unique primitive line
for the nilpotent positive short-root action imply irreducibility under all
short-root operators. Jacobson density then identifies their associative
algebra with the full endomorphism algebra.

The operators are the coefficients of the actual polynomial root actions.
The spanning, primitive-line, and nilpotence hypotheses below are explicit
remaining restricted-module obligations. In particular, this module does not
yet assert short-root density for every basic highest weight. The zero basic
weight is settled separately using the raw highest-weight uniqueness contract
and the rational one-dimensional trivial representation.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4, and the two parts of the proof of 11.1(1), pp. 52–53,
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Geometrically short positive roots in the fixed F₄ base. -/
abbrev ShortPositiveRoot :=
  {r : F4Chevalley.Root // ¬ IsLongRoot r ∧ typeF4RootPairing_base.IsPos r}

/-- Geometrically short negative roots in the fixed F₄ base. -/
abbrev ShortNegativeRoot :=
  {r : F4Chevalley.Root // ¬ IsLongRoot r ∧ ¬ typeF4RootPairing_base.IsPos r}

/-- The span of all negative short-root monomials on a specified vector,
including the empty word. -/
@[expose] def RootExpansion.shortNegativeSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) : Submodule F B.Space :=
  Submodule.span F (Set.range fun l : List ShortNegativeRoot =>
    (l.map fun r => p.coeff r.val 1).prod v)

/-- The common kernel of the positive short-root infinitesimal operators. -/
@[expose] def RootExpansion.shortPositiveKernel {B : AlgebraicFactor F}
    (p : RootExpansion B.action) : Submodule F B.Space :=
  ⨅ r : ShortPositiveRoot, LinearMap.ker (p.coeff r.val 1)

/-- Every sufficiently long product of positive short-root operators is zero.
Individual square-zero identities alone do not assert this property. -/
@[expose] def RootExpansion.HasNilpotentShortPositiveAction {B : AlgebraicFactor F}
    (p : RootExpansion B.action) : Prop :=
  ∃ n : ℕ, ∀ l : List ShortPositiveRoot, l.length = n →
    (l.map fun r => p.coeff r.val 1).prod = 0

/-- A genuine highest vector is primitive for the positive short-root action. -/
theorem RootExpansion.highest_mem_shortPositiveKernel {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) : v ∈ p.shortPositiveKernel := by
  simp only [shortPositiveKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  intro r
  exact p.coeff_one_eq_zero_of_fixed r.val v (hv.2.1 r.val r.property.2)

/-- The two highest-line inputs and nilpotence rule out every proper nonzero
subspace stable under the short-root coefficients. -/
theorem RootExpansion.shortRootInvariant_eq_bot_or_top_of_highest_line
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (v : B.Space)
    (hspan : p.shortNegativeSpan v = ⊤)
    (hkernel : p.shortPositiveKernel = Submodule.span F {v})
    (hnil : p.HasNilpotentShortPositiveAction)
    (W : Submodule F B.Space)
    (hW : ∀ (r : F4Chevalley.Root), ¬ IsLongRoot r →
      ∀ w ∈ W, p.coeff r 1 w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨u, huW, hu0, hu⟩ := BasicDensity.exists_primitive_of_word_annihilation
    (fun r : ShortPositiveRoot => p.coeff r.val 1) W
    (fun r => hW r.val r.property.1) n hw hw0
    (fun l hl => by rw [hn l hl]; rfl)
  have huk : u ∈ p.shortPositiveKernel := by
    simpa only [shortPositiveKernel, Submodule.mem_iInf, LinearMap.mem_ker] using hu
  rw [hkernel] at huk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huk
  have hc0 : c ≠ 0 := by
    intro hz
    apply hu0
    simpa [hz] using hc.symm
  have hvW : v ∈ W := by
    have h := W.smul_mem c⁻¹ huW
    rw [← hc, inv_smul_smul₀ hc0] at h
    exact h
  right
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact BasicDensity.word_apply_mem (fun r : ShortNegativeRoot => p.coeff r.val 1) W
    (fun r => hW r.val r.property.1) l hvW

/-- Associative-algebra density follows from the concrete highest-line inputs.
The restricted-module argument must establish these inputs before this can
be used for a basic factor. -/
theorem RootExpansion.hasShortRootDensity_of_highest_line
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (v : B.Space)
    (hspan : p.shortNegativeSpan v = ⊤)
    (hkernel : p.shortPositiveKernel = Submodule.span F {v})
    (hnil : p.HasNilpotentShortPositiveAction) : p.HasShortRootDensity := by
  apply BasicDensity.adjoin_eq_top_of_irreducible
  intro W hW
  exact p.shortRootInvariant_eq_bot_or_top_of_highest_line v hspan hkernel hnil W
    (fun r hr => hW ⟨r, hr⟩)

private noncomputable def trivialAction : RationalRepresentation (F4Chevalley.Carrier (k := F)) F := ⟨1⟩

private theorem trivialAction_isRational : IsRationalRepresentation (trivialAction (F := F)) := by
  let e := Module.finBasis F F
  let coefficient : Fin (Module.finrank F F) → Fin (Module.finrank F F) →
      (F4Chevalley.Carrier (k := F)).PolynomialFunction := fun i j =>
    algebraMap F _ (e.repr (e j) i)
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e (trivialAction (F := F)).action coefficient coefficient
    (by
      intro i j g
      rw [polynomialFunction_algebraMap_apply]
      simp [trivialAction])
    (by
      intro i j g
      rw [polynomialFunction_algebraMap_apply]
      simp [trivialAction])
  refine ⟨e, f, ?_⟩
  intro g
  exact glPointEquivOf_generalLinearRepresentationPoint e _

private noncomputable def trivialFactor : AlgebraicFactor F where
  Space := F
  action := trivialAction
  irreducible := ⟨trivialAction_isRational, fun W _ => eq_bot_or_eq_top W⟩

private theorem trivialFactor_highestWeight :
    HasHighestWeight (trivialFactor (F := F)) (basicCoefficient (0, 0)) := by
  refine ⟨(1 : F), (show (1 : F) ≠ 0 from one_ne_zero), ?_, ?_⟩
  · intro r hr t
    rfl
  · intro i t
    change (1 : F) = ((t : F) ^ basicCoefficient (0, 0) i) • (1 : F)
    simp [basicCoefficient]

/-- The zero basic weight is one-dimensional by the raw highest-weight
uniqueness contract, so its short-root operators have full algebraic density.
No differential irreducibility premise is needed for this branch. -/
theorem RootExpansion.hasShortRootDensity_of_zero_highestWeight
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action)
    (hB : Classification.HasBasicHighestWeight B (0, 0)) : p.HasShortRootDensity := by
  obtain ⟨e, _⟩ := hhigh B trivialFactor (basicCoefficient (0, 0)) hB
    trivialFactor_highestWeight
  have hdim : Module.finrank F B.Space = 1 := e.finrank_eq.trans (Module.finrank_self F)
  let : IsSimpleOrder (Submodule F B.Space) := is_simple_module_of_finrank_eq_one hdim
  apply BasicDensity.adjoin_eq_top_of_irreducible
  intro W _
  exact eq_bot_or_eq_top W

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
