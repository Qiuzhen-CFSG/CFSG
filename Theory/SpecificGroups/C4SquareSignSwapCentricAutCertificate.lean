module

public import Theory.SpecificGroups.C4SquareSignSwapCentricGenerators
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.FinCases

/-!
# Certificates for automorphisms of the sign-and-swap candidates

An automorphism is reconstructed from the images of the first three generators
using the checked normal-form words. A finite certificate tests possible images
of the same orders, preservation of pairwise product orders and the identity
fiber, and that eight iterations fix the generators.
Every actual automorphism passes the hypotheses, so a successful certificate
proves that the automorphism group is a two-group.

This is a direct finite-group argument for the explicit candidates in
`C4SquareSignSwapCentricGenerators`; no small-group catalogue is used.
-/

namespace C4SquareSignSwap
open Theory.GroupTheory
set_option synthInstance.maxSize 4096

/-- Reconstruct a proposed map from its generator images and normal-form words. -/
@[expose] public def centricImage (i : Fin 32) (v : Fin 4 → Model) (x : Model) : Model :=
  evalWord v (centricCandidateWord i x)

set_option maxHeartbeats 4000000 in
/-- Reconstruction agrees with any actual homomorphism on the candidate. -/
public theorem centricImage_hom (i : Fin 32) (f : centricCandidate i →* Model)
    (x : centricCandidate i) :
    centricImage i (fun j => f (centricCandidateGeneratorIn i j)) x = f x := by
  have hw (w : List (Fin 4)) :
      evalWord (fun j => f (centricCandidateGeneratorIn i j)) w =
      f ⟨evalWord (centricCandidateGenerator i) w,
        SubgroupEnumeration.evalWord_mem _ _ (centricCandidateGenerator_mem i) w⟩ := by
    induction w with
    | nil => exact f.map_one.symm
    | cons j w ih =>
      let y : centricCandidate i := ⟨evalWord (centricCandidateGenerator i) w,
        SubgroupEnumeration.evalWord_mem _ _ (centricCandidateGenerator_mem i) w⟩
      change f (centricCandidateGeneratorIn i j) * evalWord _ w =
        f (centricCandidateGeneratorIn i j * y)
      rw [map_mul, ih]
  have hx : (⟨evalWord (centricCandidateGenerator i) (centricCandidateWord i x),
      SubgroupEnumeration.evalWord_mem _ _ (centricCandidateGenerator_mem i) _⟩ :
      centricCandidate i) = x := Subtype.ext (centricCandidate_normal_form i x x.property)
  exact (hw _).trans (congrArg f hx)

/-- Necessary power tests for the image of a generator under an automorphism. -/
@[expose] public def centricImageEligible (i : Fin 32) (j : Fin 4) (x : Model) : Prop :=
  x ∈ centricCandidate i ∧
  (x = 1 ↔ centricCandidateGenerator i j = 1) ∧
  (x ^ 2 = 1 ↔ centricCandidateGenerator i j ^ 2 = 1) ∧
  (x ^ 4 = 1 ↔ centricCandidateGenerator i j ^ 4 = 1)

public instance (i : Fin 32) (j : Fin 4) (x : Model) :
    Decidable (centricImageEligible i j x) := by
  unfold centricImageEligible
  infer_instance

/-- Two elements whose identity fibers suffice for these finite certificates.
Unused slots are the identity; their tests are harmless. -/
@[expose] public def centricWitness (i : Fin 32) (z : Fin 2) : Model :=
  coordinateElement ((![![0, 0], ![0, 0], ![8, 8], ![58, 58], ![8, 24],
    ![26, 26], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![31, 31],
    ![10, 10], ![10, 10], ![10, 10], ![10, 10], ![8, 8], ![8, 8],
    ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![26, 26], ![0, 0], ![8, 8],
    ![31, 31], ![42, 42], ![0, 0], ![48, 58], ![0, 0], ![0, 0], ![0, 0],
    ![0, 0] ] : Fin 32 → Fin 2 → ℕ) i z)

/-- The product-order tests used to prune generator-image triples. -/
@[expose] public def centricProductPowers (x y : Model) : Prop :=
  (x ^ 2 = 1 ↔ y ^ 2 = 1) ∧ (x ^ 4 = 1 ↔ y ^ 4 = 1)

public instance (x y : Model) : Decidable (centricProductPowers x y) := by
  unfold centricProductPowers
  infer_instance

/-- Finite equations sufficient to bound the order of every automorphism by eight. -/
@[expose] public def CentricAutCertificate (i : Fin 32) : Prop :=
  ∀ a : Model, centricImageEligible i 0 a →
  ∀ b : Model, centricImageEligible i 1 b →
  ∀ c : Model, centricImageEligible i 2 c →
  let v : Fin 4 → Model := ![a, b, c, 1]
  (∀ j k : Fin 3, j < k →
    centricProductPowers (v j.castSucc * v k.castSucc)
      (centricCandidateGenerator i j.castSucc * centricCandidateGenerator i k.castSucc)) →
  (∀ z : Fin 2, let x := centricWitness i z
    x ∈ centricCandidate i → (centricImage i v x = 1 ↔ x = 1)) →
  ∀ j : Fin 4, (centricImage i v)^[8] (centricCandidateGenerator i j) =
    centricCandidateGenerator i j

/-- A successful finite certificate excludes odd-order automorphisms. -/
public theorem centricAutCertificate_sound (i : Fin 32)
    (hpad : centricCandidateGenerator i 3 = 1) (cert : CentricAutCertificate i) :
    IsPGroup 2 (MulAut (centricCandidate i)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro f
  let v : Fin 4 → Model := fun j => (f (centricCandidateGeneratorIn i j) : Model)
  have hpad' : centricCandidateGeneratorIn i 3 = 1 := Subtype.ext hpad
  have hv : v = ![v 0, v 1, v 2, 1] := by
    funext j
    fin_cases j <;> simp [v, hpad']
  have himg (x : centricCandidate i) : centricImage i v x = (f x : Model) :=
    centricImage_hom i ((centricCandidate i).subtype.comp f.toMonoidHom) x
  have hpow (x : centricCandidate i) (n : ℕ) :
      (f x : Model) ^ n = 1 ↔ (x : Model) ^ n = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow]
    exact (Subtype.ext_iff.symm.trans f.map_eq_one_iff).trans Subtype.ext_iff
  have hp : ∀ j k : Fin 3, j < k →
      centricProductPowers (v j.castSucc * v k.castSucc)
        (centricCandidateGenerator i j.castSucc * centricCandidateGenerator i k.castSucc) := by
    intro j k _
    let x := centricCandidateGeneratorIn i j.castSucc
    let y := centricCandidateGeneratorIn i k.castSucc
    change centricProductPowers ((f x : Model) * (f y : Model)) ((x : Model) * (y : Model))
    rw [← Subgroup.coe_mul, ← map_mul]
    exact ⟨hpow (x * y) 2, hpow (x * y) 4⟩
  have hel (j : Fin 4) : centricImageEligible i j (v j) := by
    refine ⟨(f (centricCandidateGeneratorIn i j)).property, ?_, ?_, ?_⟩
    · change ((f (centricCandidateGeneratorIn i j) : Model) = 1 ↔ _)
      exact (Subtype.ext_iff.symm.trans f.map_eq_one_iff).trans Subtype.ext_iff
    · change ((f (centricCandidateGeneratorIn i j) : Model) ^ 2 = 1 ↔ _)
      rw [← Subgroup.coe_pow, ← map_pow]
      exact (Subtype.ext_iff.symm.trans f.map_eq_one_iff).trans Subtype.ext_iff
    · change ((f (centricCandidateGeneratorIn i j) : Model) ^ 4 = 1 ↔ _)
      rw [← Subgroup.coe_pow, ← map_pow]
      exact (Subtype.ext_iff.symm.trans f.map_eq_one_iff).trans Subtype.ext_iff
  have hk : ∀ x : Model, x ∈ centricCandidate i → (centricImage i v x = 1 ↔ x = 1) := by
    intro x hx
    rw [himg ⟨x, hx⟩]
    exact (Subtype.ext_iff.symm.trans f.map_eq_one_iff).trans Subtype.ext_iff
  have hc : ∀ j : Fin 4, (centricImage i v)^[8] (centricCandidateGenerator i j) =
      centricCandidateGenerator i j := by
    have h := cert (v 0) (hel 0) (v 1) (hel 1) (v 2) (hel 2)
    rw [← hv] at h
    exact h hp (fun z => hk (centricWitness i z))
  have hiter (n : ℕ) (x : centricCandidate i) :
      (centricImage i v)^[n] x = ((f ^ n) x : Model) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, himg]
      rw [pow_succ', MulAut.mul_apply]
  refine ⟨3, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply centricCandidate_hom_ext i
  intro j
  apply Subtype.ext
  exact (hiter 8 (centricCandidateGeneratorIn i j)).symm.trans (hc j)

end C4SquareSignSwap
