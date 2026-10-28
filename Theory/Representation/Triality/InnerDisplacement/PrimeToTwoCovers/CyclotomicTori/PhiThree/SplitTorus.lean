module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Data
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Diagonal
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.FixedWords
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The full primary plane in the third cyclotomic split torus

Put q = 2^n and m = p^v_p(q²+q+1). The m-torsion subgroup of the actual
GF(q³) unit group is cyclic of order m. An isomorphism from ZMod m into
that subgroup supplies coefficients for the original simple-coroot product.
The two columns, in node order 0,1,2,3, are (1,1−q,1,1) and (q,0,q²,1).
The central coordinate recovers the first parameter because 1−q is a unit
modulo m; the last arm then recovers the second parameter.

The entire product matrix is diagonal on the Geck lattice. The literal root
permutation of w = (s₁s₀s₂s₃)² gives its integral coroot action, including
its action on the Cartan part of the lattice. Reducing the resulting four
coordinate identities modulo q²+q+1 proves wσ(t) = tw and the marked
conjugations by q² and 1. This includes repeated prime powers in m.

The final theorem constructs every field of `TwistedPlane`, the geometric
input consumed by `PhiThree.exists_sylow_pair_of_twistedPlane`. The separate
Lang equation remains with the descent owner.

Source: GLS3 §2.2 and §6.1 (`refs/KGroup/GLS3/chapter2.tex` and
`refs/KGroup/GLS3/chapter6.tex`). The matrix argument follows the original
coroot conventions of `Triality.Standard.BinarySevenPlane.TorusAction`.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
open Triality.Standard
noncomputable section

/-- Faithful coefficients of the full primary order in the actual extension field. -/
theorem exists_unitHom (n : ℕ) (hn : 0 < n) (p : ℕ) :
    ∃ f : Multiplicative (ZMod (primaryOrder n p)) →*
      (ExtensionField (binaryParameters n hn))ˣ, Function.Injective f := by
  let F := ExtensionField (binaryParameters n hn)
  let m := primaryOrder n p
  have hd : m ∣ Nat.card Fˣ := by
    rw [Nat.card_units, card_extensionField]
    change m ∣ (2 ^ n) ^ 3 - 1
    have hq : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
    have hid : (2 ^ n) ^ 3 - 1 = ((2 ^ n) ^ 2 + 2 ^ n + 1) * (2 ^ n - 1) := by
      zify [hq, one_le_pow₀ hq]
      ring
    rw [hid]
    exact dvd_mul_of_dvd_left (primaryOrder_dvd n p) _
  let H := (powMonoidHom m : Fˣ →* Fˣ).ker
  have hc : Nat.card H = m := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hd]
  have he : Nonempty (Multiplicative (ZMod m) ≃* H) := by
    rw [← hc]
    exact ⟨zmodCyclicMulEquiv inferInstance⟩
  obtain ⟨e⟩ := he
  exact ⟨H.subtype.comp e.toMonoidHom, H.subtype_injective.comp e.injective⟩

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.SplitTorus
open Triality.Standard Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.MatrixRealization
open Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.Parabolics Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open scoped BigOperators
noncomputable section

variable (n : ℕ) (hn : 0 < n) (p : ℕ)
local notation "R" => ZMod (primaryOrder n p)
local notation "P" => binaryParameters n hn
local notation "F" => ExtensionField P

/-- The two specified coroot columns over the full primary residue ring. -/
def planeCoordinates (z : R × R) : Fin 4 → R :=
  ![z.1 + (2 ^ n : R) * z.2, (1 - 2 ^ n) * z.1,
    z.1 + (2 ^ n : R) ^ 2 * z.2, z.1 + z.2]

lemma planeCoordinates_add (z w : R × R) :
    planeCoordinates n p (z+w) = planeCoordinates n p z + planeCoordinates n p w := by
  funext i
  fin_cases i <;> simp [planeCoordinates] <;> ring

lemma planeCoordinates_zero : planeCoordinates n p 0 = 0 := by
  funext i
  fin_cases i <;> simp [planeCoordinates]

lemma planeCoordinates_injective [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    Function.Injective (planeCoordinates n p) := by
  have hu : IsUnit (1 - (2 ^ n : R)) := by
    have hc := Nat.Coprime.of_dvd_right (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)
      (primaryOrder_coprime hp hthree)
    have hh := (ZMod.isUnit_iff_coprime (2 ^ n - 1) (primaryOrder n p)).mpr hc.symm
    rw [Nat.cast_sub (one_le_pow₀ (by decide)), Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat] at hh
    simpa only [neg_sub] using hh.neg
  intro z w h
  have ha : z.1 = w.1 := hu.mul_left_cancel (congrFun h 1)
  have hb : z.2 = w.2 := by
    have hh : z.1 + z.2 = w.1 + w.2 := congrFun h 3
    rw [ha] at hh
    exact add_left_cancel hh
  exact Prod.ext ha hb

variable (coeff : Multiplicative (ZMod (primaryOrder n p)) →*
  (ExtensionField (binaryParameters n hn))ˣ)

def exponents (a : Fin 4 → R) : Coordinates P :=
  fun i => coeff (Multiplicative.ofAdd (a i))

def torusCoordinates : Plane n p →* Coordinates P where
  toFun z := exponents n hn p coeff (planeCoordinates n p z.toAdd)
  map_one' := by
    funext i
    change coeff (Multiplicative.ofAdd (planeCoordinates n p 0 i)) = 1
    rw [planeCoordinates_zero]
    exact map_one coeff
  map_mul' z w := by
    funext i
    change coeff (Multiplicative.ofAdd (planeCoordinates n p (z.toAdd+w.toAdd) i)) = _
    rw [planeCoordinates_add]
    exact map_mul coeff _ _

/-- The primary plane mapped through the original four-coroot product. -/
def splitEmbedding : Plane n p →* SplitGroup P :=
  (productHom P rfl).comp (torusCoordinates n hn p coeff)

lemma splitEmbedding_injective [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) (hu : Function.Injective coeff) :
    Function.Injective (splitEmbedding n hn p coeff) := by
  apply (product_injective P rfl).comp
  intro z w h
  apply Multiplicative.toAdd.injective
  apply planeCoordinates_injective n p hp hthree
  funext i
  exact hu (congrFun h i)

/-- Every point lies in the subgroup generated by the original coroot words. -/
lemma splitEmbedding_mem_splitTorus (z : Plane n p) :
    splitEmbedding n hn p coeff z ∈ splitTorus P :=
  product_mem P (torusCoordinates n hn p coeff z)

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.SplitTorus

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.SplitTorus
open Triality.Standard Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.MatrixRealization
open Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.Parabolics Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open scoped BigOperators
noncomputable section
local instance torusLatticeDecidableEq : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

variable (n : ℕ) (hn : 0 < n) (p : ℕ)
local notation "R" => ZMod (primaryOrder n p)
local notation "P" => binaryParameters n hn
local notation "F" => ExtensionField P
variable (coeff : Multiplicative (ZMod (primaryOrder n p)) →*
  (ExtensionField (binaryParameters n hn))ˣ)

def exponentProduct (a : Fin 4 → R) := product P (exponents n hn p coeff a)
def weight (a : Fin 4 → R) (r : Fin 24) : R :=
  a 0 * (rootPairing r 0 : R) + a 2 * (rootPairing r 2 : R) +
  a 3 * (rootPairing r 3 : R) + a 1 * (rootPairing r 1 : R)
def diagonalValue (a : Fin 4 → R) : Index → F
  | .inl _ => 1
  | .inr r => (coeff (Multiplicative.ofAdd (weight n p a r))).val

private lemma weight_enumeration (i : Fin 4) (r : Fin 24) :
    corootWeight i (latticeEnumeration (.inr r)) = rootPairing r i := by
  change (typeDRootPairing 2).pairingIn ℤ (rootEnumeration r)
    (typeDSimpleRootIndex 2 i) = _
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.algebraMap_pairingIn, ← rootEnumeration_simpleIndex,
    typeDRootPairing_pairing]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simp [rootPairing, Int.cast_mul, mul_comm]

lemma unitHom_coeff (a : R) (k : ℤ) :
    (coeff (Multiplicative.ofAdd (a * (k : R)))).val =
      (coeff (Multiplicative.ofAdd a)).val ^ k := by
  have h := congrArg Units.val (map_zpow coeff (Multiplicative.ofAdd a) k)
  simpa only [← ofAdd_zsmul, zsmul_eq_mul, mul_comm,
    Units.val_zpow_eq_zpow_val] using h

lemma matrix_exponentProduct (a : Fin 4 → R) : matrix P (exponentProduct n hn p coeff a) =
    Matrix.diagonal (diagonalValue n hn p coeff a) := by
  ext r s
  change (product P (exponents n hn p coeff a)).val.val
    (latticeEnumeration r) (latticeEnumeration s) = _
  rw [product_val P rfl]
  simp only [Matrix.diagonal_apply, latticeEnumeration.injective.eq_iff]
  by_cases h : r = s
  · subst s
    simp only [if_true]
    cases r with
    | inl i => simp [corootWeight, latticeEnumeration, diagonalValue]
    | inr r =>
      simp only [weight_enumeration, exponents, diagonalValue, weight,
        ofAdd_add, map_mul, Units.val_mul, unitHom_coeff]
  · simp [h]

lemma word_intertwine (l : List (Fin 4)) (a b : Fin 4 → R)
    (h : ∀ r, weight n p a r = weight n p b (permWord l r)) :
    word n hn l * exponentProduct n hn p coeff a =
      exponentProduct n hn p coeff b * word n hn l := by
  apply matrix_injective P
  simp only [map_mul, matrix_exponentProduct]
  ext r s
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [(realizes_word n hn l).matrix_column]
  cases s with
  | inl j =>
    cases r with
    | inl i => simp [diagonalValue]
    | inr q => simp [corootVector]
  | inr s =>
    dsimp only
    rw [rootAction_rootWord]
    by_cases he : r = Sum.inr (permWord l s)
    · subst r
      simp only [if_true, one_mul, mul_one, diagonalValue]
      rw [h]
    · simp [he]

/-- The integral coroot action of (s₁s₀s₂s₃)². -/
def weylCoordinates (a : Fin 4 → R) : Fin 4 → R :=
  ![a 1 - a 2 - a 3, -a 0 + a 1 - a 2 - a 3,
    -a 0 + a 1 - a 3, -a 0 + a 1 - a 2]

private lemma pairing_twistWord (r : Fin 24) :
    let s := permWord [1,0,2,3,1,0,2,3] r
    rootPairing r 0 = -rootPairing s 1 - rootPairing s 2 - rootPairing s 3 ∧
    rootPairing r 1 = rootPairing s 0 + rootPairing s 1 + rootPairing s 2 + rootPairing s 3 ∧
    rootPairing r 2 = -rootPairing s 0 - rootPairing s 1 - rootPairing s 3 ∧
    rootPairing r 3 = -rootPairing s 0 - rootPairing s 1 - rootPairing s 2 := by
  revert r
  decide +kernel

lemma weight_weylCoordinates (a : Fin 4 → R) (r : Fin 24) :
    weight n p a r =
      weight n p (weylCoordinates n p a) (permWord [1,0,2,3,1,0,2,3] r) := by
  obtain ⟨h0, h1, h2, h3⟩ := pairing_twistWord r
  simp only [weight, weylCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0, h1, h2, h3]
  push_cast
  ring

lemma twistWord_intertwine (a : Fin 4 → R) :
    twistWord n hn * exponentProduct n hn p coeff a =
      exponentProduct n hn p coeff (weylCoordinates n p a) * twistWord n hn :=
  word_intertwine n hn p coeff _ _ _ (weight_weylCoordinates n p a)

lemma frobenius_unitHom (a : R) :
    frobenius P (coeff (Multiplicative.ofAdd a)) =
      coeff (Multiplicative.ofAdd ((2 ^ n : R) * a)) := by
  apply Units.ext
  change fieldFrobenius P _ = _
  rw [fieldFrobenius_apply]
  change _ ^ (2 ^ n) = _
  have h := congrArg Units.val (map_pow coeff (Multiplicative.ofAdd a) (2 ^ n))
  simpa only [← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    Units.val_pow_eq_pow_val] using h.symm

def exponentTwist (a : Fin 4 → R) : Fin 4 → R :=
  fun i => (2 ^ n : R) * a (typeD4DiagramPermutation.symm i)

lemma graphField_exponentProduct (a : Fin 4 → R) :
    graphFieldAutomorphism P (exponentProduct n hn p coeff a) =
      exponentProduct n hn p coeff (exponentTwist n p a) := by
  unfold exponentProduct
  rw [graphField_product P rfl]
  congr 1
  funext i
  exact frobenius_unitHom n hn p coeff _

lemma cyclotomic_relation : (2 ^ n : R) ^ 2 + 2 ^ n + 1 = 0 := by
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
    (ZMod.natCast_eq_zero_iff _ _).mpr (primaryOrder_dvd n p)

lemma weylCoordinates_twist_plane (z : R × R) :
    weylCoordinates n p (exponentTwist n p (planeCoordinates n p z)) =
      planeCoordinates n p z := by
  have h := cyclotomic_relation n p
  funext i
  fin_cases i
  all_goals simp [weylCoordinates, exponentTwist, planeCoordinates,
    typeD4DiagramPermutation]
  · linear_combination -(z.1 + (2 ^ n : R) * z.2) * h
  · linear_combination -(z.1 + (2 ^ n : R) * z.2) * h
  · linear_combination -(z.1 + (2 ^ n : R) * z.2) * h
  · linear_combination -(z.1 + z.2) * h

lemma weylCoordinates_plane (z : R × R) :
    weylCoordinates n p (planeCoordinates n p z) =
      planeCoordinates n p (((2 ^ n : R) ^ 2) * z.1, z.2) := by
  have h := cyclotomic_relation n p
  funext i
  fin_cases i
  all_goals simp [weylCoordinates, planeCoordinates]
  · linear_combination -(z.1 + z.2) * h
  · linear_combination (((2 ^ n : R) - 2) * z.1 - z.2) * h
  · linear_combination -(z.1 + z.2) * h
  · linear_combination -(z.1 + z.2) * h

lemma twisted_fixed (z : Plane n p) :
    twistWord n hn * graphFieldAutomorphism P (splitEmbedding n hn p coeff z) =
      splitEmbedding n hn p coeff z * twistWord n hn := by
  change twistWord n hn * graphFieldAutomorphism P
    (exponentProduct n hn p coeff (planeCoordinates n p z.toAdd)) = _
  rw [graphField_exponentProduct, twistWord_intertwine, weylCoordinates_twist_plane]
  rfl

lemma conjugate_plane (z : R × R) :
    twistWord n hn * splitEmbedding n hn p coeff (Multiplicative.ofAdd z) *
      (twistWord n hn)⁻¹ =
      splitEmbedding n hn p coeff (Multiplicative.ofAdd (((2 ^ n : R) ^ 2) * z.1, z.2)) := by
  have h := twistWord_intertwine n hn p coeff (planeCoordinates n p z)
  rw [weylCoordinates_plane] at h
  exact (congrArg (fun g => g * (twistWord n hn)⁻¹) h).trans (mul_inv_cancel_right _ _)

lemma conjugate_left :
    twistWord n hn * splitEmbedding n hn p coeff (leftVector n p) * (twistWord n hn)⁻¹ =
      splitEmbedding n hn p coeff (leftVector n p) ^ (2 ^ n) ^ 2 := by
  rw [leftVector, conjugate_plane, ← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  ext <;> simp

lemma conjugate_right :
    twistWord n hn * splitEmbedding n hn p coeff (rightVector n p) * (twistWord n hn)⁻¹ =
      splitEmbedding n hn p coeff (rightVector n p) := by
  rw [rightVector, conjugate_plane]
  simp

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.SplitTorus

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree

/-- The full primary plane in the original split coroot torus, with the
specified graph-field twist and marked cubic Weyl action. -/
theorem exists_twistedPlane (n : ℕ) (hn : 0 < n) (_hlarge : 1 < n)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    Nonempty (TwistedPlane n hn p) := by
  obtain ⟨coeff, hcoeff⟩ := exists_unitHom n hn p
  exact ⟨{
    embedding := SplitTorus.splitEmbedding n hn p coeff
    injective := SplitTorus.splitEmbedding_injective n hn p coeff hp hthree hcoeff
    twisted_fixed := SplitTorus.twisted_fixed n hn p coeff
    conjugate_left := SplitTorus.conjugate_left n hn p coeff
    conjugate_right := SplitTorus.conjugate_right n hn p coeff
  }⟩

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
