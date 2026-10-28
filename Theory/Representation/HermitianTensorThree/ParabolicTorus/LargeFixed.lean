module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Contracts
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.LargeFixed.FixedSpan
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Centralizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.InducedAction.Semilinearity

/-!
# Large odd fixed spaces in the descended Hermitian tensor

Every binary normalizer acts semilinearly on the actual nine-dimensional
space over the fixed field `F n`. Its coefficient order divides its actor
order. If that coefficient action is nontrivial and the actor has odd order,
the coefficient order is at least three, so the fixed binary dimension is
at most `3*n`. Thus a larger fixed space forces fixed-field linearity.
Restriction of scalars then makes its binary dimension divisible by `n`.

This proves the exact `LargeOddFixedSpaceLinearity` contract for arbitrary
overgroups and their literal cyclic subgroups. The parabolic exponent
calculation remains separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.0.1,
printed p.377; H.4.2 tensor setup, printed p.380; and the linear-three branch
of 8.2.3, printed pp.715–716.
-/

public section
noncomputable section

namespace Representation.HermitianTensorThree.ParabolicTorus
open ImageOuter BinaryOffender FiniteFieldSemilinearDisplacement
open Module
variable (n : ℕ) [NeZero n]

/-- An odd binary normalizer fixing more than one third of the Hermitian space
preserves its actual fixed-field scalars; its fixed binary dimension is a multiple of `n`. -/
theorem largeOddFixedSpaceLinearity : LargeOddFixedSpaceLinearity n := by
  intro M x hnormal hodd hlarge
  obtain ⟨τ, hτ⟩ := normalizer_semilinear_of_scalarCentralizer n
    (scalarCentralizerCoverage n) x.val hnormal
  let σ : F n ≃ₐ[ZMod 2] F n := AlgEquiv.ofRingEquiv (f := τ) (fun a => by
    exact congrArg (fun (f : ZMod 2 →+* F n) => f a)
      (Subsingleton.elim (τ.toRingHom.comp (algebraMap (ZMod 2) (F n)))
        (algebraMap (ZMod 2) (F n))))
  have hsemi (a : F n) (v : Space n) :
      overgroupAction n M x (a • v) = σ a • overgroupAction n M x v := hτ a v
  -- Use the algebra-induced scalar instance appearing in the dimension lemmas.
  let : Module (ZMod 2) (F n) := Algebra.toModule
  have hF : finrank (ZMod 2) (F n) = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 (F n)).trans (card_F n)
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp (by
    rw [finrank_space n]
    decide)
  have ho : Odd (orderOf σ) :=
    hodd.of_dvd_nat (coefficient_order_dvd (overgroupAction n M) x σ hsemi)
  have hσ : σ = 1 := by
    by_contra hne
    have hne1 : orderOf σ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have hthree : 3 ≤ orderOf σ := by
      obtain ⟨k, hk⟩ := ho
      omega
    have hb := fixedSpace_order_bound (overgroupAction n M) x σ hsemi
    rw [hF, finrank_space n] at hb
    have hle := Nat.mul_le_mul_right
      (finrank (ZMod 2) (fixedSpace (overgroupAction n M) (Subgroup.zpowers x))) hthree
    omega
  have hlinear : IsFixedFieldLinear n x.val := by
    intro a v
    have ht := hsemi a v
    change x.val (a • v) = σ a • x.val v at ht
    simpa only [hσ, AlgEquiv.one_apply] using ht
  refine ⟨hlinear, ?_⟩
  simpa only [hF] using
    (field_degree_dvd_fixedSpace (F := F n) (overgroupAction n M) x hlinear)
end Representation.HermitianTensorThree.ParabolicTorus
