/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Alphabets
public import Theory.AtlasPort.OtherSporadic.Codes.Weight
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.TransferInstance

/-!
# KleinianIsometries

The linear isometries of the Kleinian alphabet are exactly the permutations of its three
nonzero letters. Extending such a permutation by zero proves the equivalence, and
explicit letter maps give the six elements and the centralizer of a three-cycle.

Source: `Atlas/Codes/KleinianIsometries.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

/-- In the anisotropic binary plane every invertible linear map is an isometry. -/
abbrev KIsometry := K ≃ₗ[Bit] K

@[simp] theorem k_inv_apply_apply (e : KIsometry) (u : K) : e⁻¹ (e u) = u :=
  e.symm_apply_apply u
@[simp] theorem k_apply_inv_apply (e : KIsometry) (u : K) : e (e⁻¹ u) = u :=
  e.apply_symm_apply u

theorem KIsometry.map_q (e : KIsometry) (u : K) : qK (e u) = qK u := by
  simp only [qK_eq_indicator, e.map_eq_zero_iff]

theorem KIsometry.map_polar (e : KIsometry) (u v : K) : polar (e u) (e v) = polar u v := by
  rw [← qK_polar, ← map_add, e.map_q, e.map_q, e.map_q, qK_polar]

def kAlphabetEquiv : AlphabetIsometry qK ≃ KIsometry where
  toFun e := e.toLinearEquiv
  invFun e := ⟨e, e.map_q⟩
  left_inv := by intro e; cases e; rfl
  right_inv := by intro e; rfl

instance : Group (AlphabetIsometry qK) := kAlphabetEquiv.group

def kAlphabetMulEquiv : AlphabetIsometry qK ≃* KIsometry where
  toEquiv := kAlphabetEquiv
  map_mul' := by intros; rfl

abbrev NonzeroK := {u : K // u ≠ 0}

def kNonzeroPerm : KIsometry →* Equiv.Perm NonzeroK where
  toFun e :=
    { toFun := fun u => ⟨e u, by simpa using u.prop⟩
      invFun := fun u => ⟨e.symm u, by simpa using u.prop⟩
      left_inv := by intro u; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  map_one' := by apply Equiv.ext; intro u; rfl
  map_mul' := by intros; apply Equiv.ext; intro u; rfl

/-- A local four-letter identity characterizes addition without choosing field multiplication. -/
theorem letter_add_characterization : ∀ u v w : K,
    u + v = w ↔ (u = 0 ∧ v = w) ∨ (v = 0 ∧ u = w) ∨ (u = v ∧ w = 0) ∨
      (u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w) := by decide

theorem zeroFixing_add (e : Equiv.Perm K) (he : e 0 = 0) (u v : K) :
    e (u + v) = e u + e v := by
  have h := (letter_add_characterization u v (u+v)).mp rfl
  symm
  apply (letter_add_characterization _ _ _).mpr
  have hz : ∀ x, e x = 0 ↔ x = 0 := fun x => by
    have hh : e x = e 0 ↔ x = 0 := e.injective.eq_iff
    simpa only [he] using hh
  simpa only [ne_eq, hz, e.injective.eq_iff] using h

def zeroFixingLinear (e : Equiv.Perm K) (he : e 0 = 0) : KIsometry where
  toEquiv := e
  map_add' := zeroFixing_add e he
  map_smul' := by
    intro r u
    rcases bit_cases r with rfl | rfl <;> simp [he]

def extendNonzero (e : Equiv.Perm NonzeroK) : KIsometry :=
  zeroFixingLinear (e.extendDomain (Equiv.refl NonzeroK))
    (by apply Equiv.Perm.extendDomain_apply_not_subtype; simp)

theorem kNonzeroPerm_bijective : Function.Bijective kNonzeroPerm := by
  constructor
  · intro e f h
    apply LinearEquiv.ext
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · exact congrArg Subtype.val (Equiv.congr_fun h ⟨u,hu⟩)
  · intro e
    refine ⟨extendNonzero e, ?_⟩
    apply Equiv.ext
    intro u
    apply Subtype.ext
    exact Equiv.Perm.extendDomain_apply_subtype e (Equiv.refl NonzeroK) u.prop

noncomputable def kIsometryPermEquiv : KIsometry ≃* Equiv.Perm NonzeroK :=
  MulEquiv.ofBijective kNonzeroPerm kNonzeroPerm_bijective

instance : Finite KIsometry :=
  Finite.of_equiv (Equiv.Perm NonzeroK) kIsometryPermEquiv.symm.toEquiv

theorem nonzeroK_card : Fintype.card NonzeroK = 3 := by decide

theorem kIsometry_card : Nat.card KIsometry = 6 := by
  rw [Nat.card_congr kIsometryPermEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, nonzeroK_card]
  decide

def localU : KIsometry := LinearEquiv.ofInvolutive
  (⟨⟨fun u => (u.1+u.2,u.2), by decide⟩, by decide⟩ : K →ₗ[Bit] K) (by intro u; revert u; decide)
def localV : KIsometry := LinearEquiv.ofInvolutive
  (⟨⟨fun u => (u.2,u.1), by decide⟩, by decide⟩ : K →ₗ[Bit] K) (by intro u; revert u; decide)
def localW : KIsometry := LinearEquiv.ofInvolutive
  (⟨⟨fun u => (u.1,u.1+u.2), by decide⟩, by decide⟩ : K →ₗ[Bit] K) (by intro u; revert u; decide)
def localKappa : KIsometry := localV * localU

@[simp] theorem localU_apply (u : K) : localU u = (u.1+u.2,u.2) := rfl
@[simp] theorem localV_apply (u : K) : localV u = (u.2,u.1) := rfl
@[simp] theorem localW_apply (u : K) : localW u = (u.1,u.1+u.2) := rfl
@[simp] theorem localKappa_apply (u : K) : localKappa u = (u.2,u.1+u.2) := rfl

@[simp] theorem localU_sq : localU * localU = 1 := by apply LinearEquiv.ext; intro u; revert u; decide
@[simp] theorem localV_sq : localV * localV = 1 := by apply LinearEquiv.ext; intro u; revert u; decide
@[simp] theorem localW_sq : localW * localW = 1 := by apply LinearEquiv.ext; intro u; revert u; decide
@[simp] theorem localKappa_cube : localKappa ^ 3 = 1 := by apply LinearEquiv.ext; intro u; revert u; decide

theorem localKappa_inv_apply (u : K) : localKappa⁻¹ u = (u.1+u.2,u.1) := by
  revert u; decide

theorem local_maps_table :
    (localU a, localU b, localU c) = (a,c,b) ∧
    (localV a, localV b, localV c) = (b,a,c) ∧
    (localW a, localW b, localW c) = (c,b,a) ∧
    (localKappa a, localKappa b, localKappa c) = (b,c,a) := by decide

theorem kIsometry_ext_ab {e f : KIsometry} (ha : e a = f a) (hb : e b = f b) : e = f := by
  apply LinearEquiv.ext
  intro u
  have hu : u = u.1 • a + u.2 • b := by revert u; decide
  rw [hu, map_add, map_add, map_smul, map_smul, map_smul, map_smul, ha, hb]

theorem nonzero_distinct_pairs : ∀ x y : K, x ≠ 0 → y ≠ 0 → x ≠ y →
    (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = b ∧ y = a) ∨
    (x = c ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = a) := by
  intro x y; fin_cases x <;> fin_cases y <;> decide

theorem kIsometry_eq_six (e : KIsometry) :
    e = 1 ∨ e = localU ∨ e = localV ∨ e = localW ∨ e = localKappa ∨ e = localKappa⁻¹ := by
  have ha : e a ≠ 0 := by simpa only [ne_eq, e.map_eq_zero_iff] using (show a ≠ (0 : K) by decide)
  have hb : e b ≠ 0 := by simpa only [ne_eq, e.map_eq_zero_iff] using (show b ≠ (0 : K) by decide)
  have hab : e a ≠ e b := e.injective.ne (by decide)
  rcases nonzero_distinct_pairs (e a) (e b) ha hb hab with h | h | h | h | h | h
  · exact Or.inl (kIsometry_ext_ab h.1 h.2)
  · exact Or.inr (Or.inl (kIsometry_ext_ab h.1 h.2))
  · exact Or.inr (Or.inr (Or.inl (kIsometry_ext_ab h.1 h.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (kIsometry_ext_ab h.1 h.2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (kIsometry_ext_ab h.1 h.2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (kIsometry_ext_ab h.1 h.2)))))

theorem kIsometry_centralizer (e : KIsometry) (he : e * localKappa = localKappa * e) :
    e = 1 ∨ e = localKappa ∨ e = localKappa⁻¹ := by
  rcases kIsometry_eq_six e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    have hh := LinearEquiv.congr_fun he a
    exact (by decide : _ ≠ _) hh
  · exfalso
    have hh := LinearEquiv.congr_fun he a
    exact (by decide : _ ≠ _) hh
  · exfalso
    have hh := LinearEquiv.congr_fun he a
    exact (by decide : _ ≠ _) hh
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Atlas.Codes
