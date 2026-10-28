module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Field identifications for binary rank-one models

Two finite fields of the same cardinality embedded in one field have the same
image: each consists of the roots of `X^q-X`. This gives an isomorphism that
respects the supplied embeddings, as required when descending a representation
from the algebraic closure of its Schur field.

For a field of order eight we also retain an actual identification with GF(8)
and prove that its automorphisms are the three powers of squaring, using the
finite-field Frobenius theorem.

Source: GLS volume 3, §2.8.8; Aschbacher--Smith, combined manuscript
(1 March 2004), G.9.3(6), (16), printed p.354.
-/

public section

open Polynomial

namespace Representation.SL2.BinarySmall
noncomputable section

/-- Equal finite subfields admit an identification compatible with their specified embeddings. -/
theorem exists_fieldEquiv_comp_eq_of_card_eq {K E F : Type*}
    [Field K] [Field E] [Field F] [Finite K] [Finite E]
    (e : K →+* F) (i : E →+* F) (hc : Nat.card K = Nat.card E) :
    ∃ c : K ≃+* E, i.comp c.toRingHom = e := by
  have hm (x : K) : e x ∈ i.range := by
    apply (Polynomial.splits_X_pow_nat_card_sub_X (K := E)).mem_range_of_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero E (Finite.one_lt_card (α := E)))
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rw [← hc, ← map_pow]
    congr 1
    let : Fintype K := Fintype.ofFinite K
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
  let ir : E ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b h => i.injective (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  let f : K →+* E := ir.symm.toRingHom.comp (e.codRestrict i.range hm)
  have hf (x : K) : i (f x) = e x :=
    congrArg Subtype.val (ir.apply_symm_apply (⟨e x, hm x⟩ : i.range))
  let c : K ≃+* E := RingEquiv.ofBijective f
    (f.injective.bijective_of_nat_card_le hc.ge)
  exact ⟨c, RingHom.ext hf⟩

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance binaryFieldIdentificationAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

omit [CharP K 2] in
/-- An actual field identification with the standard field of eight elements. -/
theorem nonempty_fieldEightEquiv (hc : Nat.card K = 8) : Nonempty (K ≃+* GaloisField 2 3) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hc,
      GaloisField.card 2 3 (by decide)]
    norm_num)⟩

/-- Every automorphism of a field of eight elements is one of the first three powers
of the actual squaring automorphism. -/
theorem exists_frobenius_pow_eq_of_card_eight (hc : Nat.card K = 8) (τ : K ≃+* K) :
    ∃ j : ℕ, j < 3 ∧ (iterateFrobeniusEquiv K 2 1) ^ j = τ := by
  have hd : Module.finrank (ZMod 2) K = 3 := by
    have h : 2 ^ Module.finrank (ZMod 2) K = 2 ^ 3 := by
      simpa [hc] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)).symm
    exact (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h
  let a : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := τ) (by
    intro x
    exact DFunLike.congr_fun (RingHom.ext_zmod
      (τ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)) x)
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) K).2 a
  refine ⟨j.val, hd ▸ j.isLt, ?_⟩
  have he : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K).toRingEquiv =
      iterateFrobeniusEquiv K 2 1 := by
    ext x
    simp [frobenius_def]
  rw [← he]
  let forget : (K ≃ₐ[ZMod 2] K) →* (K ≃+* K) :=
    ⟨⟨AlgEquiv.toRingEquiv, rfl⟩, fun _ _ => rfl⟩
  exact (forget.map_pow _ j.val).symm.trans (congrArg forget hj)

end
end Representation.SL2.BinarySmall
