module
public import Theory.Representation.SymplecticFour.BinaryDegree
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The coefficient-field constraint on symplectic four-space embeddings

A faithful embedding Sp₄(2ᵏ) into Sp₄(2ᵈ) forces k to divide d. Choose a
primitive prime of binary order 4k. It divides the source group order and
hence the target order. Its oddness and the symplectic order formula place
it in 2^(4d)−1, forcing 4k to divide 4d. The finite-field embedding theorem
then realizes the model field as a literal subfield of the ambient field.
No irreducibility or module-recognition hypothesis is needed.

This supplies the coefficient-field existence prerequisite in the degree-four
inspection of Aschbacher--Smith G.4.1, printed p.342. Recognition of the
actual four-dimensional action remains a separate mathematical statement.
-/

public noncomputable section
set_option linter.style.haveILetI false
namespace Theory.SpecificGroups.SymplecticFour.NativeFieldEmbedding
variable {K F : Type*} [Field K] [Finite K] [Field F] [Finite F]

/-- A faithful symplectic embedding forces divisibility of the binary field degrees. -/
theorem exponent_dvd_of_injective {k d : ℕ} (hk : 0 < k)
    (hK : Nat.card K = 2 ^ k) (hF : Nat.card F = 2 ^ d)
    (j : Sp K →* Sp F) (hj : Function.Injective j) : k ∣ d := by
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul hk
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at ho
    omega
  have hd : p ∣ Nat.card (Sp F) :=
    (Representation.SymplecticFour.prime_dvd_card_of_orderOf_two hk hK hp ho).trans
      (Subgroup.card_dvd_of_injective j hj)
  rw [card_sp, hF] at hd
  have hnot : ¬p ∣ (2 ^ d) ^ 4 := by
    intro h
    have hh := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hh |>.resolve_left hp.ne_one)
  have hd4 : p ∣ (2 ^ d) ^ 4 - 1 := by
    rcases hp.dvd_mul.mp hd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact (hnot h).elim
      · exact h.trans (Nat.pow_sub_one_dvd_pow_sub_one (2 ^ d) (by decide : 2 ∣ 4))
    · exact h
  have he : (2 : ZMod p) ^ (4 * d) = 1 := by
    have hh : (2 ^ (4 * d) : ℕ) ≡ 1 [MOD p] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero (4*d) (by decide : (2:ℕ)≠0))) (n := p)).mpr
        (by simpa only [←pow_mul, Nat.mul_comm d 4] using hd4)).symm
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have hh := orderOf_dvd_of_pow_eq_one he
  rw [ho] at hh
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) hh

variable [CharP K 2] [CharP F 2]

/-- The source coefficient field embeds into the target coefficient field. -/
theorem exists_ringHom_of_injective {k d : ℕ} (hk : 0 < k)
    (hK : Nat.card K = 2 ^ k) (hF : Nat.card F = 2 ^ d)
    (j : Sp K →* Sp F) (hj : Function.Injective j) : Nonempty (K →+* F) := by
  letI : Algebra (ZMod 2) K := (ZMod.castHom (by simp) K).toAlgebra
  letI : Algebra (ZMod 2) F := (ZMod.castHom (by simp) F).toAlgebra
  have hk' : Module.finrank (ZMod 2) K = k := by
    have hh := FiniteField.pow_finrank_eq_natCard 2 K
    rw [hK] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh
  have hd' : Module.finrank (ZMod 2) F = d := by
    have hh := FiniteField.pow_finrank_eq_natCard 2 F
    rw [hF] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := K) (L := F)
    (by rw [hk', hd']; exact exponent_dvd_of_injective hk hK hF j hj)
  exact ⟨f.toRingHom⟩

/-- The source field is isomorphic to an actual subfield of the target field. -/
theorem exists_subfield_equiv_of_injective {k d : ℕ} (hk : 0 < k)
    (hK : Nat.card K = 2 ^ k) (hF : Nat.card F = 2 ^ d)
    (j : Sp K →* Sp F) (hj : Function.Injective j) :
    ∃ L : Subfield F, Nonempty (K ≃+* L) := by
  obtain ⟨f⟩ := exists_ringHom_of_injective hk hK hF j hj
  exact ⟨f.fieldRange, ⟨f.rangeRestrictFieldEquiv⟩⟩

/-- The actual embedded subgroup application retains its literal ambient inclusion. -/
theorem subgroup_exists_subfield_equiv {k d : ℕ} (hk : 0 < k)
    (hK : Nat.card K = 2 ^ k) (hF : Nat.card F = 2 ^ d)
    (N : Subgroup (Sp F)) (e : N ≃* Sp K) :
    ∃ L : Subfield F, Nonempty (K ≃+* L) := by
  exact exists_subfield_equiv_of_injective hk hK hF
    (N.subtype.comp e.symm.toMonoidHom) (Subtype.val_injective.comp e.symm.injective)

end Theory.SpecificGroups.SymplecticFour.NativeFieldEmbedding
