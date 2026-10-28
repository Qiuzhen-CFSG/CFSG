module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model

/-!
# Outer operators cannot fix a nonzero matrix displacement space

An operator carrying the natural summand into the dual summand cannot fix
any nonzero natural displacement. A nontrivial field-semilinear operator
cannot fix a nonzero field-linear displacement space pointwise: compare a
vector with a scalar multiple on which the field automorphism is nontrivial.
Faithfulness then makes the matrix actor the identity.

These are the mixed-quadraticity inputs for the normalizer reduction in
Aschbacher--Smith, proof of 13.8.20, printed p.955 (1 March 2004 manuscript).
The coordinate properties are explicit hypotheses here; the normalizer-form
classification must establish them for the relevant outer operators.
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction

lemma representation_smul (g : SL) (a : F) (v : V) :
    representation g (a • v) = a • representation g v := by
  simp only [representation_apply, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul,
    Prod.smul_mk]

/-- Any summand-exchanging operator separates every nonidentity matrix displacement. -/
theorem eq_one_of_exchange_fixes_displacement (f : BinaryGL) (g : SL)
    (hf : ∀ w : W, (f (w, 0)).1 = 0)
    (hfix : ∀ v : V, f (representation g v - v) = representation g v - v) : g = 1 := by
  apply (naturalDisplacement_eq_zero_iff g).mp
  apply LinearMap.ext
  intro w
  have hd : representation g (w, 0) - (w, 0) = (naturalDisplacement g w, 0) := by
    apply Prod.ext
    · rfl
    · change dualCoordinates g 0 - 0 = 0
      simp
  have h := congrArg Prod.fst (hfix (w, 0))
  rw [hd, hf] at h
  exact h.symm

/-- The same separation for any nontrivial common field twist, without a
normal form for its linear part or an involution hypothesis. -/
theorem eq_one_of_field_twist_fixes_displacement (f : BinaryGL)
    (σ : F ≃+* F) (hσ : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ a : F, ∀ v : V, f (a • v) = σ a • f v)
    (g : SL) (hfix : ∀ v : V, f (representation g v - v) = representation g v - v) :
    g = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra! hn
    exact hσ (RingEquiv.ext hn)
  apply representation_injective
  apply LinearMap.ext
  intro v
  have hd : representation g (a • v) - a • v = a • (representation g v - v) := by
    rw [representation_smul, smul_sub]
  have h := hfix (a • v)
  rw [hd, hsemi, hfix] at h
  have hz : (σ a - a) • (representation g v - v) = 0 := by
    rw [sub_smul, h, sub_self]
  have hdisp : representation g v - v = 0 :=
    (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)
  simpa only [map_one, Module.End.one_apply] using sub_eq_zero.mp hdisp

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
