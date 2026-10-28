module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Mathlib.Data.Fin.VecNotation

/-!
# Janko's four binary coordinate cases

This module records the four actions displayed in Janko, *A characterization
of the Mathieu simple groups, I*, J. Algebra 9 (1968), Section 1, pp.2–3,
DOI 10.1016/0021-8693(68)90002-1. It proves that Cases I and II give the
ordinary and parity-twisted products already defined in `Actions`.

The source uses row vectors and right conjugation `x^g = g⁻¹*x*g`.
Accordingly `action_c` specifies the action of `jankoC⁻¹`; the other three
source generators are involutions. The fixed permutations satisfy
`b = c⁻¹*a*c`, `a^d = a`, `b^d = a*b`, and `b^c = a*b`.
The basis vectors for both surviving models are 1111, 0001, 1100, 1010.
Small kernel computations verify the basis and generator identities. The
24-element decomposition of S4 then extends agreement to the whole action.

`JankoCoordinates` is a coordinate witness, not an existence theorem. Neither
the four-case exhaustion nor the ambient exclusions of Cases III and IV is
asserted here. They are the separate mathematical inputs needed for the
local dichotomy in Held, Illinois J. Math. 13 (1969), p.224.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

/-- The four parameter choices on Janko's printed p.2. -/
public inductive JankoCase where
  | one | two | three | four
  deriving DecidableEq

/-- Source generator `a = (01)(23)`. -/
@[expose] public def jankoA : SymmetricFour := Equiv.swap 0 1 * Equiv.swap 2 3
/-- Source generator `c = (012)`, acting on the right in the source. -/
@[expose] public def jankoC : SymmetricFour := Equiv.swap 0 1 * Equiv.swap 1 2
/-- Source generator `d = (01)`. -/
@[expose] public def jankoD : SymmetricFour := Equiv.swap 0 1
/-- Source generator `b = a^c = (02)(13)`. -/
@[expose] public def jankoB : SymmetricFour := jankoC⁻¹ * jankoA * jankoC

/-- The four source matrices for right conjugation by `a`. -/
@[expose] public def jankoSourceA (k : JankoCase) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd <| match k with
  | .one | .two => ![x 0 + x 1 + x 3, x 1, x 2 + x 1, x 3]
  | .three => ![x 0 + x 2, x 1 + x 3, x 2, x 3]
  | .four => ![x 0 + x 3, x 1, x 2, x 3]

/-- The common source matrix for right conjugation by `c`. -/
@[expose] public def jankoSourceC (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd ![x 0, x 1, x 3, x 2 + x 3]

/-- The four source matrices for right conjugation by `b`. -/
@[expose] public def jankoSourceB (k : JankoCase) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd <| match k with
  | .one | .two => ![x 0 + x 1 + x 2, x 1, x 2, x 3 + x 1]
  | .three => ![x 0 + x 2 + x 3, x 1 + x 2, x 2, x 3]
  | .four => ![x 0 + x 2, x 1, x 2, x 3]

/-- The source matrix for `d`: alpha is zero only in Case I. -/
@[expose] public def jankoSourceD (k : JankoCase) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd ![x 0 + (if k = .one then 0 else x 1), x 1, x 2 + x 3, x 3]

/-- An actual basis intertwining the supplied action with one source case.
No existence or ambient-group conclusion is included. -/
public structure JankoCoordinates (ρ : SymmetricFour →* MulAut BinaryFour) (k : JankoCase) where
  /-- Source coordinates mapped to the coordinates of the supplied action. -/
  basis : BinaryFour ≃* BinaryFour
  action_a : ∀ v, ρ jankoA (basis v) = basis (jankoSourceA k v)
  action_c : ∀ v, ρ jankoC⁻¹ (basis v) = basis (jankoSourceC v)
  action_d : ∀ v, ρ jankoD (basis v) = basis (jankoSourceD k v)

/-- Every actor is a word in the four source generators, with the source exponents. -/
public theorem janko_decomposition : ∀ s : SymmetricFour,
    ∃ i j : Fin 2, ∃ k : Fin 3, ∃ l : Fin 2,
      s = jankoA ^ i.val * jankoB ^ j.val * jankoC ^ k.val * jankoD ^ l.val := by
  decide +kernel

private theorem generator_ext {H : Type*} [Group H] (f g : SymmetricFour →* H)
    (ha : f jankoA = g jankoA) (hc : f jankoC⁻¹ = g jankoC⁻¹)
    (hd : f jankoD = g jankoD) : f = g := by
  have hc' : f jankoC = g jankoC := inv_injective (by simpa only [map_inv] using hc)
  have hb : f jankoB = g jankoB := by simp only [jankoB, map_mul, map_inv, ha, hc']
  ext s
  obtain ⟨i, j, k, l, rfl⟩ := janko_decomposition s
  simp only [map_mul, map_pow, ha, hb, hc', hd]

/-- The basis 1111, 0001, 1100, 1010 in the two surviving models. -/
@[expose] public def jankoModelBasis : BinaryFour ≃* BinaryFour where
  toFun v := let x := v.toAdd
    Multiplicative.ofAdd ![x 0 + x 2 + x 3, x 0 + x 2, x 0 + x 3, x 0 + x 1]
  invFun v := let y := v.toAdd
    Multiplicative.ofAdd ![y 0 + y 1 + y 2, y 0 + y 1 + y 2 + y 3, y 0 + y 2, y 0 + y 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

/-- The ordinary permutation action realizes Case I with the source marking. -/
@[expose] public def permutationJankoCoordinates : JankoCoordinates permutationAction .one where
  basis := jankoModelBasis
  action_a := by decide +kernel
  action_c := by decide +kernel
  action_d := by decide +kernel

/-- The parity-twisted action realizes Case II with the source marking. -/
@[expose] public def twistedJankoCoordinates : JankoCoordinates twistedAction .two where
  basis := jankoModelBasis
  action_a := by decide +kernel
  action_c := by decide +kernel
  action_d := by decide +kernel

namespace JankoCoordinates
variable {ρ σ : SymmetricFour →* MulAut BinaryFour} {k : JankoCase}

/-- The left action of `c` is the square of the source's right action. -/
public theorem action_c_left (R : JankoCoordinates ρ k) (v : BinaryFour) :
    ρ jankoC (R.basis v) = R.basis (jankoSourceC (jankoSourceC v)) := by
  have cube : ∀ w, jankoSourceC (jankoSourceC (jankoSourceC w)) = w := by decide +kernel
  apply (ρ jankoC⁻¹).injective
  rw [R.action_c, cube, map_inv, MulAut.inv_apply_self]

/-- The derived generator `b` has exactly Janko's displayed matrix. -/
public theorem action_b (R : JankoCoordinates ρ k) (v : BinaryFour) :
    ρ jankoB (R.basis v) = R.basis (jankoSourceB k v) := by
  have formula : ∀ w,
      jankoSourceC (jankoSourceA k (jankoSourceC (jankoSourceC w))) = jankoSourceB k w := by
    cases k <;> decide +kernel
  simp only [jankoB, map_mul, MulAut.mul_apply, R.action_c_left, R.action_a,
    R.action_c, formula]

/-- Agreement on the source generators determines the whole normalized action. -/
public theorem normalizedAction_eq (R : JankoCoordinates ρ k) (S : JankoCoordinates σ k) :
    (MulAut.congr R.basis.symm).toMonoidHom.comp ρ =
      (MulAut.congr S.basis.symm).toMonoidHom.comp σ := by
  apply generator_ext
  · apply MulEquiv.ext
    intro v
    change R.basis.symm (ρ jankoA (R.basis v)) = S.basis.symm (σ jankoA (S.basis v))
    rw [R.action_a, S.action_a, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  · apply MulEquiv.ext
    intro v
    change R.basis.symm (ρ jankoC⁻¹ (R.basis v)) = S.basis.symm (σ jankoC⁻¹ (S.basis v))
    rw [R.action_c, S.action_c, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  · apply MulEquiv.ext
    intro v
    change R.basis.symm (ρ jankoD (R.basis v)) = S.basis.symm (σ jankoD (S.basis v))
    rw [R.action_d, S.action_d, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- Identical source coordinates give an isomorphism of the actual products. -/
@[expose] public def semidirectEquiv (R : JankoCoordinates ρ k) (S : JankoCoordinates σ k) :
    BinaryFour ⋊[ρ] SymmetricFour ≃* BinaryFour ⋊[σ] SymmetricFour :=
  SemidirectProduct.congr (R.basis.symm.trans S.basis) (MulEquiv.refl _) (by
    intro s
    apply MulEquiv.ext
    intro v
    change S.basis (R.basis.symm (ρ s v)) = σ s (S.basis (R.basis.symm v))
    have h := congrArg (fun f : SymmetricFour →* MulAut BinaryFour =>
      f s (R.basis.symm v)) (R.normalizedAction_eq S)
    change R.basis.symm (ρ s (R.basis (R.basis.symm v))) =
      S.basis.symm (σ s (S.basis (R.basis.symm v))) at h
    rw [MulEquiv.apply_symm_apply] at h
    have h' := congrArg S.basis h
    simpa only [MulEquiv.apply_symm_apply] using h')

/-- Case I is the actual ordinary binary permutation product. -/
@[expose] public def permutationEquiv (R : JankoCoordinates ρ .one) :
    BinaryFour ⋊[ρ] SymmetricFour ≃* PermutationModel := R.semidirectEquiv permutationJankoCoordinates

/-- Case II is the actual parity-twisted binary product. -/
@[expose] public def twistedEquiv (R : JankoCoordinates ρ .two) :
    BinaryFour ⋊[ρ] SymmetricFour ≃* TwistedModel := R.semidirectEquiv twistedJankoCoordinates

end JankoCoordinates
end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
