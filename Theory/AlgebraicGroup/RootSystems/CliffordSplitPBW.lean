module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Split Clifford PBW bases

This module supplies a characteristic-free finite-dimensional interface for a
split quadratic space.  A split witness is a quadratic isometry to the
hyperbolic form `∑ i, x i * y i`; its nondegeneracy is recorded explicitly so
that the witness can be used by the geometric Clifford constructions without
reconstructing a decomposition.  Its polar map is perfect in every
characteristic: the explicit polar formula pairs each coordinate in one
summand with the matching coordinate in the other, and transport through the
split isometry gives surjectivity onto the dual.  In the hyperbolic coordinates,
the non-symmetric bilinear form `-∑ i, x i * y i'` has quadratic map `-Q`.
Mathlib's `CliffordAlgebra.changeFormEquiv` therefore identifies the Clifford
algebra with the exterior algebra without any assumption that `2` is
invertible.  The ordinary exterior PBW basis transports across this equivalence,
and a finite `Fin (finrank)` basis is then obtained from `Module.finBasis`.

The construction is the standard ordered-monomial PBW argument, expressed
through the universal-property change-of-form equivalence.  It applies over a
field in characteristic two as well as in other characteristics.
-/

universe u

open scoped BigOperators
open LinearMap (BilinForm)

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The coordinate space of a hyperbolic quadratic form of rank `n`. -/
public abbrev HyperbolicSpace (k : Type u) (n : Nat) :=
  (Fin n → k) × (Fin n → k)

/-- The split hyperbolic quadratic form `∑ i, x i * y i`. -/
public def hyperbolicForm (n : Nat) :
    QuadraticForm k (HyperbolicSpace k n) where
  toFun v := ∑ i, v.1 i * v.2 i
  toFun_smul := by
    intro a v
    change (∑ i, (a * v.1 i) * (a * v.2 i)) = a * a * ∑ i, v.1 i * v.2 i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exists_companion' := by
    refine ⟨LinearMap.mk₂ k (fun v w => ∑ i, (v.1 i * w.2 i + w.1 i * v.2 i)) ?_ ?_ ?_ ?_, ?_⟩
    · intro v w w'
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add]
      simp only [Finset.sum_add_distrib]
      ring

    · intro a v w
      change (∑ i, ((a * v.1 i) * w.2 i + w.1 i * (a * v.2 i))) =
        a * ∑ i, (v.1 i * w.2 i + w.1 i * v.2 i)
      rw [Finset.mul_sum]
      simp only [mul_add]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · intro v w w'
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add]
      simp only [Finset.sum_add_distrib]
      ring
    · intro a v w
      change (∑ i, (v.1 i * (a * w.2 i) + (a * w.1 i) * v.2 i)) =
        a * ∑ i, (v.1 i * w.2 i + w.1 i * v.2 i)
      rw [Finset.mul_sum]
      simp only [mul_add]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · intro v w
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul,
        Finset.sum_add_distrib, LinearMap.mk₂_apply]
      ring

@[simp]
public lemma hyperbolicForm_apply (n : Nat) (v : HyperbolicSpace k n) :
    hyperbolicForm (k := k) n v = ∑ i, v.1 i * v.2 i := by
  change (∑ i, v.1 i * v.2 i) = _
  rfl

@[simp]
public lemma hyperbolicForm_polar (n : Nat) (v w : HyperbolicSpace k n) :
    (hyperbolicForm (k := k) n).polarBilin v w =
      ∑ i, (v.1 i * w.2 i + w.1 i * v.2 i) := by
  change (∑ i, (v.1 i + w.1 i) * (v.2 i + w.2 i)) -
      (∑ i, v.1 i * v.2 i) - (∑ i, w.1 i * w.2 i) = _
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  ring

private theorem hyperbolicPolar_injective (n : Nat) :
    Function.Injective (hyperbolicForm (k := k) n).polarBilin := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Prod.ext <;> funext i
  · have hi := congrArg (fun f => f (0, Pi.single i 1)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi
  · have hi := congrArg (fun f => f (Pi.single i 1, 0)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi

/-- A triangular bilinear companion whose quadratic map is the negative
hyperbolic form.  Its asymmetry is intentional and is what makes the
construction valid in characteristic two. -/
public def hyperbolicBilinForm (n : Nat) :
    BilinForm k (HyperbolicSpace k n) :=
  LinearMap.mk₂ k (fun v w => -∑ i, v.1 i * w.2 i) (by
    intro v w w'
    simp only [Prod.fst_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring) (by
    intro a v w
    change -(∑ i, (a * v.1 i) * w.2 i) = a * -(∑ i, v.1 i * w.2 i)
    simp only [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring) (by
    intro v w w'
    simp only [Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring) (by
    intro a v w
    change -(∑ i, v.1 i * (a * w.2 i)) = a * -(∑ i, v.1 i * w.2 i)
    simp only [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring)

@[simp]
public lemma hyperbolicBilinForm_toQuadraticMap (n : Nat) :
    (hyperbolicBilinForm (k := k) n).toQuadraticMap =
      (0 : QuadraticForm k (HyperbolicSpace k n)) - hyperbolicForm n := by
  ext v
  simp [hyperbolicBilinForm, hyperbolicForm]

/-- An explicit hyperbolic splitness witness for a finite-dimensional quadratic
space.  The isometry is oriented from `Q` to the standard hyperbolic form. -/
public structure SplitQuadraticForm {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) [FiniteDimensional k V] where
  rank : Nat
  isometry : Q.IsometryEquiv (hyperbolicForm (k := k) rank)
  nondegenerate : Q.Nondegenerate

namespace SplitQuadraticForm

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

/-- Transport the triangular hyperbolic companion back to `V`. -/
public noncomputable def bilinear (s : SplitQuadraticForm Q) : BilinForm k V :=
  LinearMap.compl₁₂ (hyperbolicBilinForm (k := k) s.rank)
    s.isometry.toLinearEquiv.toLinearMap s.isometry.toLinearEquiv.toLinearMap

@[simp]
public lemma bilinear_toQuadraticMap (s : SplitQuadraticForm Q) :
    (bilinear s).toQuadraticMap = (0 : QuadraticForm k V) - Q := by
  ext v
  rw [LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [bilinear, LinearMap.compl₁₂_apply]
  rw [← LinearMap.BilinMap.toQuadraticMap_apply]
  rw [hyperbolicBilinForm_toQuadraticMap]
  simp [s.isometry.map_app]

/-- The characteristic-free change-of-form equivalence from `CliffordAlgebra Q`
to the exterior algebra of `V`. -/
public noncomputable def cliffordToExterior (s : SplitQuadraticForm Q) :
    CliffordAlgebra Q ≃ₗ[k] ExteriorAlgebra k V :=
  CliffordAlgebra.changeFormEquiv (bilinear_toQuadraticMap s)

/-- The ordered exterior monomial basis transported to the split Clifford
algebra.  Its index is the finite-set type of subsets of the input basis. -/
public noncomputable def pbwBasis (s : SplitQuadraticForm Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Module.Basis (Finset (Fin (Module.finrank k V))) k (CliffordAlgebra Q) :=
  (b.ExteriorAlgebra).map (cliffordToExterior s).symm

/-- The PBW basis reindexed by the canonical finite ordinal required by the
algebraic-group matrix APIs. -/
public noncomputable def pbwFinBasis (s : SplitQuadraticForm Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k (CliffordAlgebra Q) := by
  let pbw := pbwBasis s b
  let hcard := Module.finrank_eq_card_basis pbw
  exact pbw.reindex (Fintype.equivFinOfCardEq hcard.symm)

/-- Finite generation of a split Clifford algebra, with no characteristic
restriction on `k`. -/
public theorem moduleFinite (s : SplitQuadraticForm Q) :
    Module.Finite k (CliffordAlgebra Q) :=
  Module.Finite.of_basis (pbwFinBasis s (Module.finBasis k V))

/-- The polar bilinear map of an explicitly split finite-dimensional quadratic
form is onto its dual, including in characteristic two. -/
public theorem polarBilin_surjective (s : SplitQuadraticForm Q) :
    Function.Surjective Q.polarBilin := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := k) (V := V)).symm (f := Q.polarBilin)).mp
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply s.isometry.injective
  have hzero : (hyperbolicForm (k := k) s.rank).polarBilin (s.isometry v) = 0 := by
    apply LinearMap.ext
    intro w
    let x := s.isometry.symm w
    calc
      (hyperbolicForm (k := k) s.rank).polarBilin (s.isometry v) w =
          (hyperbolicForm (k := k) s.rank).polarBilin (s.isometry v)
            (s.isometry x) := by rw [s.isometry.apply_symm_apply]
      _ = Q.polarBilin v x := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
          QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
          s.isometry.map_app, s.isometry.map_app, s.isometry.map_app]
      _ = 0 := by simpa using congrArg (fun f => f x) hv
      _ = (0 : Module.Dual k (HyperbolicSpace k s.rank)) w := by rfl
  apply hyperbolicPolar_injective s.rank
  simpa using hzero

/-- A basis indexed by `Fin (Module.finrank k (CliffordAlgebra Q))`. -/
public noncomputable def finBasis (s : SplitQuadraticForm Q) :
    Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k (CliffordAlgebra Q) :=
  pbwFinBasis s (Module.finBasis k V)

end SplitQuadraticForm

end Theory.AlgebraicGroup
