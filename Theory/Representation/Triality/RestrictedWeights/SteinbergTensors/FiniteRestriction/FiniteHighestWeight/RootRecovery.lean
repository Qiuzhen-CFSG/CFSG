module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Unipotent
public import Theory.AlgebraicGroup.Representations.Algebraic.SL2HighestWeight

/-!
# Root and coroot conventions in D4 weight recovery

This module checks the rank-one comparison needed for the restricted-weight
separation in GLS3, Definition 2.8.1 and Theorem 2.8.2. It does not yet prove
`HighestVectorWeightRecovery`.

The current `RootWeightEquation` uses inverse conjugation: a chosen coroot
sends its root parameter to `s² t` under `h(s)⁻¹ x(t) h(s)`. The standard
SL2 diagonal sends an upper-root parameter to `s⁻² t` under that same
conjugation. An algebraic SL2 morphism cannot therefore identify both the
upper root and the same coroot. Comparing parameters would force `s⁴ = 1`
for every nonzero field element, contradicting infinitude.

If the diagonal instead maps to the inverse coroot, the standard SL2
highest-weight endpoint theorem applies with exponent `-a i`. It gives
`a i ≤ 0`, and the published restricted range then forces `a i = 0`.
These are convention diagnostics, with the SL2 morphism hypotheses kept
explicit; they neither construct rank-one subgroups nor establish the finite
restriction theorem. In particular, they must not be used to replace its
intended positive restricted weights by a trivial-only classification.

Relevant conventions: `RootSubgroups/Defs.lean`, `RootWeightEquation`;
`Representations/Algebraic/WeightSpaces.lean`, `IsWeightVector`;
GLS3 Chapter 1, §§1.9, 1.11, 1.14; Steinberg, `Chapter2St2.tex`, §13.3(a).
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual point on a parametrized root subgroup. -/
def rootPoint (S : Geometry K) (r : S.roots.Root) (t : k) : Variety.Point K :=
  (S.roots.rootSubgroup r).includePoint ((S.rootParameter r).value t)

/-- The actual coroot point in the ambient algebraic group. -/
def corootPoint (S : Geometry K) (r : S.roots.Root)
    (t : Variety.Point (KMult k)) : Variety.Point K :=
  S.torus.includePoint ((S.roots.rootCocharacter r).onPoints t)

omit [IsAlgClosed k] in
/-- The root parameter is recovered from its ambient group point. -/
theorem rootPoint_injective (S : Geometry K) (r : S.roots.Root) :
    Function.Injective (rootPoint S r) := by
  intro t s h
  have h' := (S.roots.rootSubgroup r).inclusion_injective h
  have h'' := (S.rootParameter r).toMulEquiv.injective h'
  exact congrArg (fun p : Variety.Point (KPlus k) => p.val PUnit.unit) h''

omit [IsAlgClosed k] in
/-- Inverse conjugation by the chosen coroot scales its root by `s²`. -/
theorem corootPoint_conjugate_rootPoint (S : Geometry K) (r : S.roots.Root)
    (s : Variety.Point (KMult k)) (t : k) :
    (corootPoint S r s)⁻¹ * rootPoint S r t * corootPoint S r s =
      rootPoint S r ((dPointEquiv 1 s 0 : k) ^ 2 * t) := by
  have h := (S.realized.2.2.1 r).2 (S.rootParameter r) t
    ((S.roots.rootCocharacter r).onPoints s)
  have hp := S.realized.rootWeight_rootCocharacter r r s
  rw [S.realized.2.2.2.2.2.2.1 r] at hp
  simpa only [rootPoint, corootPoint, hp, zpow_ofNat] using h

omit [IsAlgClosed k] in
/-- Every parametrized positive simple root lies in the positive subgroup. -/
theorem rootPoint_mem_positive (S : Geometry K) (i : Fin 4) (t : k) :
    rootPoint S (S.simpleRoot i).val t ∈ RootSubgroupGenerated S.roots S.roots.positive := by
  apply Subgroup.subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨(S.simpleRoot i).val, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 _).mp (S.simpleRoot i).property).1
  · exact ((S.roots.rootSubgroup (S.simpleRoot i).val).pointEquiv
      ((S.rootParameter (S.simpleRoot i).val).value t)).property

/-- A positive-root SL2 chart with inverse-coroot diagonal makes the published
highest-weight coordinate nonpositive. The chart is an explicit hypothesis. -/
theorem highestVector_coordinate_nonpos_of_inverse_coroot_SL2
    (S : Geometry K) (A : RationalFactor K) {a : Weight} {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (i : Fin 4) (π : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (hupper : ∀ t : k, π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      rootPoint S (S.simpleRoot i).val t)
    (hdiag : ∀ t : Variety.Point (KMult k), π.onPoints (standardSL2DiagonalMorphism.onPoints t) =
      (corootPoint S (S.simpleRoot i).val t)⁻¹) : a i ≤ 0 := by
  have hn := standardSL2_highestWeightExponent_nonneg_of_pullback π A.action
    A.irreducible.1 v (-a i) hv.1.1 (fun t => by
      rw [hupper]
      exact highestVector_fixed_positiveRoots S A hv _ (rootPoint_mem_positive S i t))
  apply neg_nonneg.mp
  apply hn
  intro t
  rw [hdiag]
  change (A.action.action ((S.torus.inclusion.onPoints
    ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t))⁻¹)).1 v = _
  rw [← map_inv]
  change (A.action.action (S.torus.includePoint
    (((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t)⁻¹))).1 v = _
  rw [hv.2.2, map_inv]
  have hp := S.realized.weightPairing_spec (S.coordinateEmbedding a) (S.simpleRoot i).val t
  change (S.coordinateEmbedding a).pointCharacter
    ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t) =
      (dPointEquiv 1 t 0 : k) ^
        S.roots.weightPairing (S.weight (Multiplicative.ofAdd a)) (S.simpleRoot i).val at hp
  rw [S.weight_coordinate] at hp
  rw [hp, zpow_neg]

/-- Under the inverse-coroot chart, the current nonnegative restricted range
contains only the zero coordinate, for every exponent (including one). -/
theorem restricted_coordinate_zero_of_inverse_coroot_SL2
    (S : Geometry K) (A : RationalFactor K) {n : ℕ} {a : Weight}
    (ha : InRestrictedRange n a) {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (i : Fin 4) (π : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (hupper : ∀ t : k, π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      rootPoint S (S.simpleRoot i).val t)
    (hdiag : ∀ t : Variety.Point (KMult k), π.onPoints (standardSL2DiagonalMorphism.onPoints t) =
      (corootPoint S (S.simpleRoot i).val t)⁻¹) : a i = 0 :=
  le_antisymm (highestVector_coordinate_nonpos_of_inverse_coroot_SL2 S A hv i π hupper hdiag)
    (ha i).1

omit [CharP k 2] in
private theorem standardSL2_diagonal_conjugate_upper
    (s : Variety.Point (KMult k)) (t : k) :
    (standardSL2DiagonalMorphism.onPoints s)⁻¹ *
        standardSL2UpperMorphism.onPoints (kPlusPoint t) *
          standardSL2DiagonalMorphism.onPoints s =
      standardSL2UpperMorphism.onPoints
        (kPlusPoint ((dPointEquiv 1 s 0 : k)⁻¹ ^ 2 * t)) := by
  rw [standardSL2UpperMorphism_kPlusPoint, standardSL2UpperMorphism_kPlusPoint]
  have h := typeASLRootPoint_diagonal_conjugation 1 standardSL2UpperRootIndex t
    (standardSL2DiagonalMorphism.onPoints s) (typeASLDiagonalEntries 1 s)
    (typeASLDiagonalPoint_matrix 1 s)
  change _ = typeASLRootPoint 1 standardSL2UpperRootIndex
    ((typeASLDiagonalEntries 1 s 0 : k)⁻¹ * t * (typeASLDiagonalEntries 1 s 1 : k)) at h
  rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl,
    typeASLDiagonalEntries_castSucc,
    show (1 : Fin 2) = Fin.last 1 by rfl, typeASLDiagonalEntries_last] at h
  simp only [Fin.prod_univ_one, Units.val_inv_eq_inv_val] at h
  convert h using 1
  congr 1
  ring

/-- The current root convention rules out an SL2 chart that identifies both
standard upper-root parameters and the same (non-inverted) coroot. -/
theorem no_same_coroot_SL2 (S : Geometry K) (r : S.roots.Root)
    (π : Theory.AlgebraicGroup.Morphism (slVariety k 2) K)
    (hupper : ∀ t : k, π.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      rootPoint S r t)
    (hdiag : ∀ t : Variety.Point (KMult k), π.onPoints (standardSL2DiagonalMorphism.onPoints t) =
      corootPoint S r t) : False := by
  have hfour : ∀ z : k, z ≠ 0 → z ^ 4 = 1 := by
    intro z hz
    let s : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => Units.mk0 z hz)
    have h := congrArg π.onPoints (standardSL2_diagonal_conjugate_upper s 1)
    simp only [map_mul, map_inv, hupper, hdiag, corootPoint_conjugate_rootPoint] at h
    have he := rootPoint_injective S r h
    have hpow : z ^ 2 = z⁻¹ ^ 2 := by simpa [s] using he
    calc
      z ^ 4 = z ^ 2 * z ^ 2 := by ring
      _ = z⁻¹ ^ 2 * z ^ 2 := by rw [← hpow]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hpoly : (Polynomial.X : Polynomial k) ^ 4 = 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({z : k | z ≠ 0} : Set k)ᶜ.Finite)).mono
    intro z hz
    simpa using hfour z hz
  have hcoeff := congrArg (fun p : Polynomial k => p.coeff 4) hpoly
  norm_num [Polynomial.coeff_one] at hcoeff

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
