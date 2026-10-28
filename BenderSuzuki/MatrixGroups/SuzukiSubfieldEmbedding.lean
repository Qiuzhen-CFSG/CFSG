module

public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# Suzuki subfield embeddings

If the odd degree `2*d+1` divides `2*n+1`, the binary field embedding respects
both powers occurring in the Suzuki generators. Indeed the quotient of these
odd degrees is odd, so `n = (2*d+1)*t+d` for some `t`. Frobenius periodicity
on the smaller field identifies the powers `2^n` and `2^d`, and likewise the
Tits powers `2^(n+1)` and `2^(d+1)`. Mapping matrices entrywise therefore
restricts to an injective homomorphism of the generated Suzuki subgroups.

Source: the standard Suzuki subfield construction, in the matrix coordinates
of Huppert--Blackburn XI.3.
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

/-- Frobenius compatibility for dividing odd Suzuki degrees. -/
public theorem suzuki_subfield_power {d n : ℕ} (hdiv : 2 * d + 1 ∣ 2 * n + 1)
    (a : BinaryGaloisField (2 * d + 1)) : a ^ (2 ^ n) = a ^ (2 ^ d) := by
  classical
  let := Fintype.ofFinite (BinaryGaloisField (2 * d + 1))
  obtain ⟨k, hk⟩ := hdiv
  have hkodd : Odd k := (show Odd (2 * n + 1) from ⟨n, rfl⟩).of_dvd_nat
    ⟨2 * d + 1, hk.trans (Nat.mul_comm _ _)⟩
  obtain ⟨t, ht⟩ := hkodd
  have hn : n = (2 * d + 1) * t + d := by nlinarith
  have hcard : Fintype.card (BinaryGaloisField (2 * d + 1)) = 2 ^ (2 * d + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * d + 1) (by omega)
  rw [hn, pow_add, pow_mul, pow_mul, ← hcard, FiniteField.pow_card_pow]

/-- The Tits powers also agree on the smaller field. -/
public theorem suzuki_subfield_tits_power {d n : ℕ}
    (hdiv : 2 * d + 1 ∣ 2 * n + 1) (a : BinaryGaloisField (2 * d + 1)) :
    a ^ (2 ^ (n + 1)) = a ^ (2 ^ (d + 1)) := by
  rw [pow_succ (2 : ℕ) n, pow_succ (2 : ℕ) d, pow_mul, pow_mul]
  exact congrArg (fun x : BinaryGaloisField (2 * d + 1) => x ^ 2)
      (suzuki_subfield_power hdiv a)

/-- Entrywise field transport sends a Suzuki root generator to a root generator. -/
public theorem map_suzukiRootGL {d n : ℕ} (hdiv : 2 * d + 1 ∣ 2 * n + 1)
    (i : BinaryGaloisField (2 * d + 1) →+* BinaryGaloisField (2 * n + 1))
    (a b : BinaryGaloisField (2 * d + 1)) :
    Matrix.GeneralLinearGroup.map i (SuzukiRootGL d a b) = SuzukiRootGL n (i a) (i b) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  rw [Matrix.GeneralLinearGroup.map_apply]
  have hp (x : BinaryGaloisField (2 * d + 1)) :
      i x ^ (2 ^ (n + 1)) = i x ^ (2 ^ (d + 1)) := by
    simpa only [map_pow] using congrArg i (suzuki_subfield_tits_power hdiv x)
  simp only [pow_succ (2 : ℕ) n, pow_succ (2 : ℕ) d] at hp
  fin_cases r <;> fin_cases c <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, map_add, map_mul, map_pow, pow_add, hp]

/-- Entrywise field transport sends a Suzuki torus generator to a torus generator. -/
public theorem map_suzukiTorusGL {d n : ℕ} (hdiv : 2 * d + 1 ∣ 2 * n + 1)
    (i : BinaryGaloisField (2 * d + 1) →+* BinaryGaloisField (2 * n + 1))
    (x : (BinaryGaloisField (2 * d + 1))ˣ) :
    Matrix.GeneralLinearGroup.map i (SuzukiTorusGL d x) =
      SuzukiTorusGL n (Units.map i.toMonoidHom x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  rw [Matrix.GeneralLinearGroup.map_apply]
  have hp : i (x : BinaryGaloisField (2 * d + 1)) ^ (2 ^ n) =
      i (x : BinaryGaloisField (2 * d + 1)) ^ (2 ^ d) := by
    simpa only [map_pow] using congrArg i (suzuki_subfield_power hdiv (x : _))
  fin_cases r <;> fin_cases c <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, pow_add, hp]

/-- Entrywise field transport preserves the Suzuki Weyl generator. -/
public theorem map_suzukiWeylGL {d n : ℕ}
    (i : BinaryGaloisField (2 * d + 1) →+* BinaryGaloisField (2 * n + 1)) :
    Matrix.GeneralLinearGroup.map i (SuzukiWeylGL d) = SuzukiWeylGL n := by
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  rw [Matrix.GeneralLinearGroup.map_apply]
  fin_cases r <;> fin_cases c <;> simp [SuzukiWeylGL, SuzukiWeylMatrix]

/-- A dividing odd field degree induces an injective Suzuki homomorphism. -/
public theorem exists_suzuki_subfield_embedding {d n : ℕ}
    (hdiv : 2 * d + 1 ∣ 2 * n + 1) :
    ∃ f : SuzukiMatrixGroup d →* SuzukiMatrixGroup n, Function.Injective f := by
  have hdegree : Module.finrank (ZMod 2) (BinaryGaloisField (2 * d + 1)) ∣
      Module.finrank (ZMod 2) (BinaryGaloisField (2 * n + 1)) := by
    rw [GaloisField.finrank 2 (by omega), GaloisField.finrank 2 (by omega)]
    exact hdiv
  obtain ⟨i⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdegree
  let f := Matrix.GeneralLinearGroup.map (n := Fin 4) i.toRingHom
  have hmap : SuzukiMatrixSubgroup d ≤ (SuzukiMatrixSubgroup n).comap f := by
    apply (Subgroup.closure_le _).2
    rintro A (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
    · change f (SuzukiRootGL d a b) ∈ SuzukiMatrixSubgroup n
      rw [show f (SuzukiRootGL d a b) = SuzukiRootGL n (i a) (i b) from
        map_suzukiRootGL hdiv i.toRingHom a b]
      exact Subgroup.subset_closure (Or.inl ⟨i a, i b, rfl⟩)
    · change f (SuzukiTorusGL d x) ∈ SuzukiMatrixSubgroup n
      rw [show f (SuzukiTorusGL d x) = SuzukiTorusGL n (Units.map i.toMonoidHom x) from
        map_suzukiTorusGL hdiv i.toRingHom x]
      exact Subgroup.subset_closure (Or.inr (Or.inl ⟨_, rfl⟩))
    · change f (SuzukiWeylGL d) ∈ SuzukiMatrixSubgroup n
      rw [show f (SuzukiWeylGL d) = SuzukiWeylGL n from map_suzukiWeylGL i.toRingHom]
      exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  refine ⟨(f.comp (SuzukiMatrixSubgroup d).subtype).codRestrict
    (SuzukiMatrixSubgroup n) (fun x => hmap x.property), ?_⟩
  intro a b hab
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  apply i.injective
  exact congrArg (fun x : SuzukiMatrixGroup n =>
    (x.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * n + 1))) r c) hab

end BenderSuzuki.MatrixGroups
