module

public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension

/-!
# Normalizers of the binary seven-letter core action

An automorphism of A₇ is induced by a unique permutation of seven letters.
An intertwining linear automorphism is that same permutation operator:
correcting by the permutation gives an element of the trivial linear
centralizer of A₇. Faithfulness of an ambient extension is unnecessary.

Source application: Aschbacher--Smith, 12.3.4(3), printed pp.808--809,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
namespace BinaryPermutation.SevenNormalizer

/-- The seven-letter permutation inducing a given automorphism of A₇. -/
def permutationOfAut : MulAut (alternatingGroup (Fin 7)) ≃* Equiv.Perm (Fin 7) :=
  (MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide))).symm

theorem conjugation_permutationOfAut (φ : MulAut (alternatingGroup (Fin 7))) :
    MulAut.conjNormal (permutationOfAut φ) = φ :=
  permutationOfAut.symm_apply_apply φ

theorem permutationOfAut_conj (g : alternatingGroup (Fin 7)) :
    permutationOfAut (MulAut.conj g) = g.val := by
  apply permutationOfAut.symm.injective
  simpa [permutationOfAut] using
    (MulAut.conjNormal_val (h := g)).symm

/-- A linear normalizer acts by the permutation inducing its actor automorphism. -/
theorem intertwiner
    (c : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7))
    (φ : MulAut (alternatingGroup (Fin 7)))
    (hc : ∀ (g : alternatingGroup (Fin 7)) v,
      c (coreRepresentation (Fin 7) g.val v) =
        coreRepresentation (Fin 7) (φ g).val (c v)) :
    ∀ v, c v = coreRepresentation (Fin 7) (permutationOfAut φ) v := by
  let s := permutationOfAut φ
  let R := coreRepresentation (Fin 7)
  have hφ (g : alternatingGroup (Fin 7)) : (φ g).val = s * g.val * s⁻¹ := by
    exact (congrArg (fun a : MulAut (alternatingGroup (Fin 7)) => (a g).val)
      (conjugation_permutationOfAut φ)).symm
  let d := c.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (R.asGroupHom s⁻¹))
  have hd : d = 1 := by
    apply SevenParabolic.linearCentralizer_eq_one
    intro g v
    change R s⁻¹ (c (R g.val v)) = R g.val (R s⁻¹ (c v))
    rw [hc, hφ]
    change (R s⁻¹ * R (s * g.val * s⁻¹)) (c v) = (R g.val * R s⁻¹) (c v)
    rw [← map_mul, ← map_mul]
    congr 2
    group
  intro v
  have hv := congrArg (fun e : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7) => e v) hd
  change R s⁻¹ (c v) = v at hv
  have hh := congrArg (R s) hv
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

end BinaryPermutation.SevenNormalizer
