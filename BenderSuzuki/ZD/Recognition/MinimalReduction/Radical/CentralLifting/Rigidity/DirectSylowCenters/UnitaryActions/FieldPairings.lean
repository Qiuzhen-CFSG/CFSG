module

public import BenderSuzuki.PFAppendixIII.FrobeniusBilinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions.Coordinates
import Mathlib.Algebra.Module.ZMod

/-!
# Binary pairings under separated Frobenius weights

An arbitrary finite field of order 2ᵐ is transported by a ring equivalence to
`BinaryGaloisField m`. Embed the binary values of a bihomomorphism in that field
and expand the resulting bilinear map in Frobenius coordinates. Scalar invariance
supports a coefficient only when the corresponding product of two weights is one.
Separation excludes every such coefficient, and injectivity of the binary-field
embedding recovers triviality of the original pairing. Neither symmetry nor
alternation is required.

For the actual projective unitary root subgroup, the published first-coordinate
descent intertwines the literal torus normalizer action with `torusWeight`.
The final theorem applies the field calculation in degree 2n, retaining the
standard form, both field cardinalities, and separation as an explicit premise.

Source: the finite-field step in the direct Sylow-center proof of GLS4,
Chapter 4, Lemma 2.8(c); the root coordinates and action are those of
Huppert II.10.12. The Frobenius expansion is proved in
`BenderSuzuki.PFAppendixIII.FrobeniusBilinear`.
-/

public section

namespace BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions

open BenderSuzuki.PFAppendixIII

/-- A binary bihomomorphism invariant under simultaneous multiplication by a
scalar is trivial if no product of two Frobenius conjugates of that scalar is one. -/
theorem field_pairings_trivial {K : Type*} [Field K] [Finite K] [CharP K 2]
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card K = 2 ^ m)
    (lambda : K)
    (hsep : ∀ i j : Fin m, lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) ≠ 1)
    (c : Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)))
    (hc : ∀ x y : Multiplicative K,
      c (.ofAdd (lambda * x.toAdd)) (.ofAdd (lambda * y.toAdd)) = c x y) :
    c = 1 := by
  classical
  let F := BinaryGaloisField m
  let : Algebra (ZMod 2) K := ZMod.algebra _ _
  let e : K ≃+* F := (GaloisField.algEquivGaloisField 2 m hcard).toRingEquiv
  let v (a b : F) : F := algebraMap (ZMod 2) F
    (c (.ofAdd (e.symm a)) (.ofAdd (e.symm b))).toAdd
  have hv₁ (a b d : F) : v (a + b) d = v a d + v b d := by
    simp [v, map_add, ofAdd_add, map_mul, MonoidHom.mul_apply,
      toAdd_mul]
  have hv₂ (a b d : F) : v a (b + d) = v a b + v a d := by
    simp [v, map_add, ofAdd_add, map_mul, toAdd_mul]
  let L (a : F) : F →ₗ[ZMod 2] F :=
    ({ toFun := v a
       map_zero' := by simp [v]
       map_add' := hv₂ a } : F →+ F).toZModLinearMap 2
  let B : F →ₗ[ZMod 2] F →ₗ[ZMod 2] F :=
    ({ toFun := L
       map_zero' := by ext b; simp [L, v]
       map_add' := by intro a b; ext d; exact hv₁ a b d } :
      F →+ (F →ₗ[ZMod 2] F)).toZModLinearMap 2
  have hB (a b : F) : B a b = v a b := rfl
  have hequiv (a b : F) : B (e lambda * a) (e lambda * b) = 1 * B a b := by
    simp only [hB, v, map_mul, RingEquiv.symm_apply_apply, one_mul]
    exact congrArg (fun z : Multiplicative (ZMod 2) =>
      algebraMap (ZMod 2) F z.toAdd) (hc (.ofAdd (e.symm a)) (.ofAdd (e.symm b)))
  obtain ⟨coeff, hexp, hsupp⟩ :=
    frobeniusBilinear_expansion_with_support_of_equivariant m hm B
      (e lambda) (e lambda) 1 hequiv
  have hzero (i j : Fin m) : coeff i j = 0 := by
    by_contra h
    apply hsep i j
    have hh := congrArg e.symm (hsupp i j h)
    simpa only [map_mul, map_pow, RingEquiv.symm_apply_apply, map_one] using hh
  have hBzero (a b : F) : B a b = 0 := by
    simp [hexp, hzero]
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  apply Multiplicative.toAdd.injective
  change (c x y).toAdd = 0
  apply (algebraMap (ZMod 2) F).injective
  have hh := hBzero (e x.toAdd) (e y.toAdd)
  simpa only [hB, v, RingEquiv.symm_apply_apply, ofAdd_toAdd,
    map_zero] using hh

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.BorelTorus
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage

/-- Separated torus weights kill every binary pairing on the actual projective
root subgroup invariant under the literal torus normalizer action. This discharges
the field-pairing premise of the Sylow-center action criterion; construction of
a parameter satisfying separation remains a separate premise. -/
theorem root_pairings_trivial_of_separated_weights
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (k : Kˣ)
    (hsep : ∀ i j : Fin (2 * n),
      (torusWeight J k : K) ^ (2 ^ (i : ℕ)) *
        (torusWeight J k : K) ^ (2 ^ (j : ℕ)) ≠ 1)
    (c : projectiveRoot J hJ →* (projectiveRoot J hJ →* Multiplicative (ZMod 2)))
    (hc : ∀ x y,
      c ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) x)
        ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) y) = c x y) :
    c = 1 := by
  apply root_pairings_trivial J hJ hcard hfixed k ?_ c hc
  intro b hb
  exact field_pairings_trivial (2 * n) (by omega)
    (by simpa only [pow_mul, Nat.mul_comm] using hcard) (torusWeight J k : K) hsep b hb

end BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions
