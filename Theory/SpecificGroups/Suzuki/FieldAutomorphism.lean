module

public import BenderSuzuki.MatrixGroups.SuzukiSubfieldEmbedding

/-!
# Frobenius on the actual Suzuki matrix group

Entrywise squaring preserves the root, torus and Weyl generators and is
injective, hence bijective on the finite group. On Sz(8), three iterations
are the identity because the coefficient field has eight elements. The
root entry (0,1) detects nontriviality, so this automorphism has order three.

These are the matrix coordinates of Huppert--Blackburn XI.3 already used
by SuzukiSubfieldEmbedding. The automorphism is the one required in
Aschbacher--Smith I.2.2(7a), printed p.412, and GLS3 section 6.3.
No action on a covering kernel is asserted here.
-/

namespace BenderSuzuki.MatrixGroups
open PFAppendixIII

/-- Restriction of entrywise Frobenius to the generated Suzuki subgroup. -/
@[expose] public noncomputable def suzukiFieldHom (m : ℕ) : SuzukiMatrixGroup m →* SuzukiMatrixGroup m := by
  let σ := frobenius (BinaryGaloisField (2 * m + 1)) 2
  let f := Matrix.GeneralLinearGroup.map (n := Fin 4) σ
  have hmap : SuzukiMatrixSubgroup m ≤ (SuzukiMatrixSubgroup m).comap f := by
    apply (Subgroup.closure_le _).2
    rintro A (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
    · change f (SuzukiRootGL m a b) ∈ SuzukiMatrixSubgroup m
      rw [show f (SuzukiRootGL m a b) = SuzukiRootGL m (σ a) (σ b) from
        map_suzukiRootGL (dvd_refl _) σ a b]
      exact Subgroup.subset_closure (Or.inl ⟨_, _, rfl⟩)
    · change f (SuzukiTorusGL m x) ∈ SuzukiMatrixSubgroup m
      rw [show f (SuzukiTorusGL m x) = SuzukiTorusGL m (Units.map σ.toMonoidHom x) from
        map_suzukiTorusGL (dvd_refl _) σ x]
      exact Subgroup.subset_closure (Or.inr (Or.inl ⟨_, rfl⟩))
    · change f (SuzukiWeylGL m) ∈ SuzukiMatrixSubgroup m
      rw [show f (SuzukiWeylGL m) = SuzukiWeylGL m from map_suzukiWeylGL σ]
      exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  exact (f.comp (SuzukiMatrixSubgroup m).subtype).codRestrict
    (SuzukiMatrixSubgroup m) (fun x => hmap x.property)

/-- Entrywise Frobenius is injective on the actual matrix carrier. -/
public theorem suzukiFieldHom_injective (m : ℕ) : Function.Injective (suzukiFieldHom m) := by
  intro a b hab
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  apply (frobenius (BinaryGaloisField (2 * m + 1)) 2).injective
  exact congrArg (fun x : SuzukiMatrixGroup m =>
    (x.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) r c) hab

/-- The Suzuki field automorphism, using entrywise squaring. -/
@[expose] public noncomputable def suzukiFieldAutomorphism (m : ℕ) : MulAut (SuzukiMatrixGroup m) :=
  MulEquiv.ofBijective (suzukiFieldHom m)
    ⟨suzukiFieldHom_injective m, Finite.surjective_of_injective (suzukiFieldHom_injective m)⟩

/-- Explicit matrix-entry convention for the field automorphism. -/
@[simp] public theorem suzukiFieldAutomorphism_entry (m : ℕ) (x : SuzukiMatrixGroup m) (r c : Fin 4) :
    ((suzukiFieldAutomorphism m x).val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) r c =
      (x.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) r c ^ 2 := rfl

/-- Parameter one is Sz(8), on which the field action has cube one. -/
public theorem suzukiFieldAutomorphism_one_cube : suzukiFieldAutomorphism 1 ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  change ((suzukiFieldAutomorphism 1 (suzukiFieldAutomorphism 1
    (suzukiFieldAutomorphism 1 x))).val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 3)) r c = _
  rw [suzukiFieldAutomorphism_entry, suzukiFieldAutomorphism_entry,
    suzukiFieldAutomorphism_entry, ← pow_mul, ← pow_mul]
  let := Fintype.ofFinite (BinaryGaloisField 3)
  have hc : Fintype.card (BinaryGaloisField 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by decide)]
    decide
  change ((x.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 3)) r c) ^ 8 =
    ((x.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 3)) r c)
  rw [← hc]
  exact FiniteField.pow_card _

/-- A Suzuki root entry detects a nontrivial field automorphism on Sz(8). -/
public theorem suzukiFieldAutomorphism_one_ne_one : suzukiFieldAutomorphism 1 ≠ 1 := by
  intro h
  have hs (a : BinaryGaloisField 3) : a ^ 2 = a := by
    let x : SuzukiMatrixGroup 1 := ⟨SuzukiRootGL 1 a 0,
      Subgroup.subset_closure (Or.inl ⟨a, 0, rfl⟩)⟩
    have he := congrArg (fun g : MulAut (SuzukiMatrixGroup 1) =>
      ((g x).val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 3)) 0 1) h
    rw [suzukiFieldAutomorphism_entry] at he
    simpa [x, SuzukiRootGL, SuzukiRootMatrix] using he
  let := Fintype.ofFinite (BinaryGaloisField 3)
  have hc : Fintype.card (BinaryGaloisField 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by decide)]
    decide
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp
    (show 2 < Fintype.card (BinaryGaloisField 3) by omega)
  rcases eq_zero_or_one_of_sq_eq_self (hs a) with ha | ha <;>
    rcases eq_zero_or_one_of_sq_eq_self (hs b) with hb | hb <;>
    rcases eq_zero_or_one_of_sq_eq_self (hs c) with hc | hc <;> simp_all

/-- The precise order of the field automorphism on Sz(8). -/
public theorem suzukiFieldAutomorphism_one_order : orderOf (suzukiFieldAutomorphism 1) = 3 :=
  orderOf_eq_prime suzukiFieldAutomorphism_one_cube suzukiFieldAutomorphism_one_ne_one

end BenderSuzuki.MatrixGroups
