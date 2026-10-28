module
public import Mathlib.FieldTheory.Finite.Extension

/-!+# Scalar coordinates on an actual root line

Fong--Seitz II, printed p.201, constructs field automorphisms from scalar
actions on already labelled root lines. Multiplication of labels is not an
extra compatibility hypothesis: it follows from the module laws and the
diagonal action on the line. The second lemma compares two such lines by
the actual linear Weyl transport.

The final lemma extends a binary finite-field automorphism across the given
field embedding. Its construction is a power of Frobenius, so it commutes
with the specified unitary involution as well.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]

/-- Diagonal scalar action on an injectively labelled additive root line
constructs its scalar-label field automorphism. -/
theorem exists_scalar_coordinates (u : F →+ V) (hu : Function.Injective u)
    (hdiag : ∀ a : F, ∃ b : F, ∀ x : F, a • u x = u (b*x)) :
    ∃ τ : F ≃+* F, ∀ a x : F, a • u x = u (τ a*x) := by
  choose t ht using hdiag
  have hone : t 1 = 1 := by
    apply hu
    simpa only [mul_one, one_smul] using (ht 1 1).symm
  have hadd (a b : F) : t (a+b) = t a+t b := by
    apply hu
    calc
      u (t (a+b)) = (a+b) • u 1 := by simpa only [mul_one] using (ht (a+b) 1).symm
      _ = a • u 1 + b • u 1 := add_smul a b (u 1)
      _ = u (t a+t b) := by rw [ht, ht, mul_one, mul_one, map_add]
  have hmul (a b : F) : t (a*b) = t a*t b := by
    apply hu
    calc
      u (t (a*b)) = (a*b) • u 1 := by simpa only [mul_one] using (ht (a*b) 1).symm
      _ = a • (b • u 1) := mul_smul a b (u 1)
      _ = u (t a*t b) := by rw [ht, mul_one, ht]
  have hzero : t 0 = 0 := by
    apply hu
    simpa only [zero_smul, mul_one, map_zero] using (ht 0 1).symm
  let f : F →+* F :=
    { toFun := t
      map_zero' := hzero
      map_one' := hone
      map_add' := hadd
      map_mul' := hmul }
  exact ⟨RingEquiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective), ht⟩

omit [Finite F] in
/-- A linear Weyl transport forces the two scalar-label automorphisms to
coincide. It compares the two lines inside the same module. -/
theorem scalar_coordinates_eq_of_transport
    (u v : F →+ V) (hv : Function.Injective v) (s : V →ₗ[F] V)
    (hs : ∀ x, s (u x) = v x) (τ υ : F ≃+* F)
    (huτ : ∀ a x, a • u x = u (τ a*x))
    (hvυ : ∀ a x, a • v x = v (υ a*x)) : τ = υ := by
  ext a
  apply hv
  have h := congrArg s (huτ a 1)
  simpa only [map_smul, hs, hvυ, mul_one] using h.symm

/-- The extension is constructed over the given field embedding; it also
commutes with every automorphism of the larger binary finite field. -/
theorem exists_extending_automorphism {E : Type*} [Field E] [Finite E]
    [CharP F 2] [CharP E 2] (ι : F →+* E) (τ : F ≃+* F) :
    ∃ η : E ≃+* E, (∀ a, η (ι a) = ι (τ a)) ∧
      ∀ (σ : E ≃+* E) a, η (σ a) = σ (η a) := by
  let := ZMod.algebra F 2
  let τa : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := τ) (by
    intro x
    exact DFunLike.congr_fun (RingHom.ext_zmod
      (τ.toRingHom.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)) x)
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 F τa
  refine ⟨iterateFrobeniusEquiv E 2 n, ?_, ?_⟩
  · intro a
    change iterateFrobeniusEquiv E 2 n (ι a) = ι (τa a)
    rw [hn, iterateFrobeniusEquiv_def, Nat.card_eq_fintype_card, ZMod.card, map_pow]
  · intro σ a
    simp only [iterateFrobeniusEquiv_def, map_pow]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
