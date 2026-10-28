module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField.TorusSections
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Positive-root relations in the central cover

The five commuting root pairs admit diagonal tori fixing one root and
scaling the other nontrivially. Their lifted commutators are central,
additive and invariant under this scaling, hence trivial.

For the remaining pair, compare [x₂(v),x₆(c)] with x₀(c²v)x₄(cv).
The actual matrix identity makes their ratio central. The commuting pairs
make this ratio additive in c. Conjugation by a lift of diag(a,1,a⁻¹,1)
fixes x₂(v), scales c by a, and transforms both comparison factors with
exactly the required weights. Thus the central ratio is also invariant
under a nonidentity scalar, and vanishes. These are relations in the cover,
not just in its matrix image.

Source: the type-C₂ calculation underlying Aschbacher–Smith I.1.3,
printed p.407, GLS III §6.1, and 13.6.6, printed p.927.
-/

@[expose] public section

open Matrix
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem additive_fixed_scale_eq_one {E : Type*} [Group E] (B : F → E)
    (ha : ∀ x y, B (x+y) = B x * B y)
    (c : F) (hc : c ≠ 1) (hs : ∀ x, B (c*x) = B x) (x : F) : B x = 1 := by
  have h (y : F) : B ((c-1)*y) = 1 := by
    have H := hs y
    rw [show c*y = (c-1)*y+y by ring, ha] at H
    exact mul_right_cancel (H.trans (one_mul _).symm)
  simpa only [mul_inv_cancel_left₀ (sub_ne_zero.mpr hc)] using h ((c-1)⁻¹*x)

omit [Finite F] [CharP F 2] in
theorem commute_of_fixed_scale {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative F →* E) (v z : E) (c : F) (hc : c ≠ 1)
    (hcomm : ∀ x : F, Commute (f (u (.ofAdd x))) (f v))
    (hu : ∀ x : F, z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (c*x)))
    (hv : z * v * z⁻¹ = v) (x : F) : Commute (u (.ofAdd x)) v := by
  let B : F → E := fun x => ⁅u (.ofAdd x), v⁆
  have hB (y : F) : B y ∈ Subgroup.center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (hcomm y).commutator_eq
  have hBa (s t : F) : B (s+t) = B s * B t := by
    dsimp [B]
    rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
    change u (.ofAdd s) * B t * (u (.ofAdd s))⁻¹ * B s = B s * B t
    rw [Subgroup.mem_center_iff.mp (hB t) _, mul_assoc (B t), mul_inv_cancel,
      mul_one, Subgroup.mem_center_iff.mp (hB s) _]
  have hBs (y : F) : B (c*y) = B y := by
    dsimp [B]
    rw [← hu y, ← hv, ← conjugate_commutatorElement, hv]
    change z * B y * z⁻¹ = B y
    rw [Subgroup.mem_center_iff.mp (hB y) z, mul_assoc, mul_inv_cancel, mul_one]
  exact commutatorElement_eq_one_iff_commute.mp
    (additive_fixed_scale_eq_one B hBa c hc hBs x)

def CommutingPair (r s : Fin 8) : Prop :=
  (r = 6 ∧ s = 0) ∨ (r = 6 ∧ s = 4) ∨ (r = 0 ∧ s = 4) ∨
    (r = 0 ∧ s = 2) ∨ (r = 4 ∧ s = 2)

omit [Finite F] [CharP F 2] in
theorem matrix_commute60 (x y : F) :
    Commute (rootElement 6 x) (rootElement 0 y) := by
  apply Subtype.ext
  change rootMatrix 6 x * rootMatrix 0 y = rootMatrix 0 y * rootMatrix 6 x
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]

omit [Finite F] in
theorem matrix_commute64 (x y : F) :
    Commute (rootElement 6 x) (rootElement 4 y) := by
  apply Subtype.ext
  change rootMatrix 6 x * rootMatrix 4 y = rootMatrix 4 y * rootMatrix 6 x
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, sub_eq_add_neg, CharTwo.neg_eq, add_assoc,
      CharTwo.add_self_eq_zero, mul_comm]

omit [Finite F] [CharP F 2] in
theorem matrix_commute04 (x y : F) :
    Commute (rootElement 0 x) (rootElement 4 y) := by
  apply Subtype.ext
  change rootMatrix 0 x * rootMatrix 4 y = rootMatrix 4 y * rootMatrix 0 x
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]

omit [Finite F] [CharP F 2] in
theorem matrix_commute02 (x y : F) :
    Commute (rootElement 0 x) (rootElement 2 y) := by
  apply Subtype.ext
  change rootMatrix 0 x * rootMatrix 2 y = rootMatrix 2 y * rootMatrix 0 x
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]

omit [Finite F] [CharP F 2] in
theorem matrix_commute42 (x y : F) :
    Commute (rootElement 4 x) (rootElement 2 y) := by
  apply Subtype.ext
  change rootMatrix 4 x * rootMatrix 2 y = rootMatrix 2 y * rootMatrix 4 x
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]

omit [Finite F] in
theorem matrix_commute {r s : Fin 8} (h : CommutingPair r s) (x y : F) :
    Commute (rootElement r x) (rootElement s y) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact matrix_commute60 x y
  · exact matrix_commute64 x y
  · exact matrix_commute04 x y
  · exact matrix_commute02 x y
  · exact matrix_commute42 x y

theorem exists_separating_torus (hF : 2 < Nat.card F) {r s : Fin 8}
    (h : CommutingPair r s) :
    ∃ a b : Fˣ, torusWeight r a b ≠ 1 ∧ torusWeight s a b = 1 := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc2 : c^2 ≠ 1 := by
    intro H
    apply hc
    apply Units.ext
    apply CharTwo.sq_injective
    simpa using congrArg Units.val H
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨1,c, by simpa [torusWeight] using hc, by simp [torusWeight]⟩
  · exact ⟨c,c⁻¹, by simpa [torusWeight, ← pow_two] using hc2, by simp [torusWeight]⟩
  · exact ⟨c,c⁻¹, by simpa [torusWeight] using hc2, by simp [torusWeight]⟩
  · exact ⟨c,1, by simpa [torusWeight] using hc2, by simp [torusWeight]⟩
  · exact ⟨c,1, by simpa [torusWeight] using hc, by simp [torusWeight]⟩

theorem equivariant_lifts_commute (hF : 2 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) {r s : Fin 8} (hp : CommutingPair r s)
    (u v : Multiplicative F →* E)
    (hu : f.comp u = RootSubgroup.parameter r)
    (hv : f.comp v = RootSubgroup.parameter s)
    (htu : ∀ (a b : Fˣ) (z : E), f z = diagonalTorus a b → ∀ t : F,
      z * u (.ofAdd t) * z⁻¹ = u (.ofAdd ((torusWeight r a b : F) * t)))
    (htv : ∀ (a b : Fˣ) (z : E), f z = diagonalTorus a b → ∀ t : F,
      z * v (.ofAdd t) * z⁻¹ = v (.ofAdd ((torusWeight s a b : F) * t)))
    (x y : F) : Commute (u (.ofAdd x)) (v (.ofAdd y)) := by
  obtain ⟨a,b,ha,hb⟩ := exists_separating_torus hF hp
  obtain ⟨z,hz⟩ := hf (diagonalTorus a b)
  apply commute_of_fixed_scale f hk u (v (.ofAdd y)) z (torusWeight r a b : F)
    (fun H => ha (Units.ext H)) ?_ (htu a b z hz) ?_ x
  · intro t
    change Commute ((f.comp u) (.ofAdd t)) ((f.comp v) (.ofAdd y))
    rw [hu,hv]
    exact matrix_commute hp t y
  · simpa only [hb, Units.val_one, one_mul] using htv a b z hz y


omit [Finite F] in
theorem matrix_crossing (v c : F) :
    rootElement 2 v * rootElement 6 c =
      rootElement 6 c * rootElement 0 (c^2*v) * rootElement 4 (c*v) * rootElement 2 v := by
  apply Subtype.ext
  change rootMatrix 2 v * rootMatrix 6 c =
    rootMatrix 6 c * rootMatrix 0 (c^2*v) * rootMatrix 4 (c*v) * rootMatrix 2 v
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_sub, pow_two, mul_assoc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, sub_eq_add_neg, CharTwo.neg_eq, add_assoc,
      CharTwo.add_self_eq_zero, mul_comm]

omit [Finite F] in
theorem matrix_commutator (v c : F) :
    ⁅rootElement 2 v, rootElement 6 c⁆ =
      rootElement 0 (c^2*v) * rootElement 4 (c*v) := by
  rw [commutatorElement_def, matrix_crossing]
  have hc := (matrix_commute (F := F) (r := 6) (s := 0) (Or.inl ⟨rfl,rfl⟩) c (c^2*v)).mul_right
    (matrix_commute (F := F) (r := 6) (s := 4) (Or.inr (Or.inl ⟨rfl,rfl⟩)) c (c*v))
  rw [mul_assoc (rootElement 6 c) (rootElement 0 _), ← mul_assoc (rootElement 6 c),
    mul_assoc _ (rootElement 2 v), mul_inv_cancel, mul_one, mul_assoc (rootElement 6 c) (rootElement 0 _), hc.eq,
    mul_assoc, mul_inv_cancel, mul_one]

theorem equivariant_crossing (hF : 2 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (u : Fin 8 → Multiplicative F →* E)
    (hu : ∀ r, f.comp (u r) = RootSubgroup.parameter r)
    (ht : ∀ (r : Fin 8) (a b : Fˣ) (z : E), f z = diagonalTorus a b → ∀ t : F,
      z * u r (.ofAdd t) * z⁻¹ = u r (.ofAdd ((torusWeight r a b : F) * t)))
    (v c : F) :
    u 2 (.ofAdd v) * u 6 (.ofAdd c) =
      u 6 (.ofAdd c) * u 0 (.ofAdd (c^2*v)) * u 4 (.ofAdd (c*v)) * u 2 (.ofAdd v) := by
  let X : Fin 8 → F → E := fun r x => u r (.ofAdd x)
  have hXa (r : Fin 8) (x y : F) : X r (x+y) = X r x * X r y :=
    (u r).map_mul (.ofAdd x) (.ofAdd y)
  have hXp (r : Fin 8) (x : F) : f (X r x) = rootElement r x :=
    DFunLike.congr_fun (hu r) (.ofAdd x)
  have hcomm (r s : Fin 8) (h : CommutingPair r s) (x y : F) :
      Commute (X r x) (X s y) :=
    equivariant_lifts_commute hF f hf hk h (u r) (u s) (hu r) (hu s) (ht r) (ht s) x y
  have h60 := hcomm 6 0 (Or.inl ⟨rfl,rfl⟩)
  have h64 := hcomm 6 4 (Or.inr (Or.inl ⟨rfl,rfl⟩))
  have h04 := hcomm 0 4 (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
  have h02 := hcomm 0 2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))
  have h42 := hcomm 4 2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))))
  let P : F → E := fun x => X 0 (x^2*v) * X 4 (x*v)
  let C : F → E := fun x => ⁅X 2 v, X 6 x⁆
  let D : F → E := fun x => C x * (P x)⁻¹
  have hD (x : F) : D x ∈ Subgroup.center E := by
    apply hk
    change f (C x * (P x)⁻¹) = 1
    dsimp [C,P]
    rw [map_mul, map_inv, map_mul, map_commutatorElement, hXp, hXp, hXp, hXp,
      matrix_commutator, mul_inv_cancel]
  have hDC (x : F) : C x = D x * P x := by simp [D, mul_assoc]
  have hP6 (x y : F) : Commute (P x) (X 6 y) :=
    (h60 y (x^2*v)).symm.mul_left (h64 y (x*v)).symm
  have hP2 (x : F) : Commute (P x) (X 2 v) :=
    (h02 (x^2*v) v).mul_left (h42 (x*v) v)
  have hPC (x y : F) : Commute (P x) (C y) := by
    dsimp [C, commutatorElement_def]
    exact (((hP2 x).mul_right (hP6 x y)).mul_right (hP2 x).inv_right).mul_right
      (hP6 x y).inv_right
  have hC6 (x y : F) : Commute (C x) (X 6 y) := by
    rw [hDC]
    have hc : Commute (D x) (X 6 y) := (Subgroup.mem_center_iff.mp (hD x) _).symm
    exact hc.mul_left (hP6 x y)
  have hCa (x y : F) : C (x+y) = C x * C y := by
    dsimp [C]
    rw [hXa, commutatorElement_mul_right_eq_mul_conj]
    change C x * X 6 x * C y * (X 6 x)⁻¹ = C x * C y
    rw [mul_assoc (C x), (hC6 y x).symm.eq, ← mul_assoc,
      mul_assoc (C x * C y), mul_inv_cancel, mul_one]
  have hPa (x y : F) : P (x+y) = P x * P y := by
    have hs : (x+y)^2*v = x^2*v+y^2*v := by rw [CharTwo.add_sq, add_mul]
    dsimp [P]
    rw [hs, add_mul, hXa, hXa]
    exact (h04 (y^2*v) (x*v)).mul_mul_mul_comm _ _
  have hDa (x y : F) : D (x+y) = D x * D y := by
    dsimp [D]
    rw [hCa, hPa, _root_.mul_inv_rev]
    have h := (hPC x y).inv_left
    have hp : Commute (P x) (P y) := by
      change P x * P y = P y * P x
      rw [← hPa, ← hPa, add_comm]
    rw [hp.inv_inv.symm.eq]
    exact h.symm.mul_mul_mul_comm _ _
  have ha : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp ha
  obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
  obtain ⟨z,hz⟩ := hf (diagonalTorus a 1)
  let e : E ≃* E := MulAut.conj z
  have he (r : Fin 8) (x : F) : e (X r x) = X r ((torusWeight r a 1 : F)*x) :=
    ht r a 1 z hz x
  have heP (x : F) : e (P x) = P ((a : F)*x) := by
    dsimp [P]
    rw [map_mul, he, he]
    simp only [show torusWeight 0 a 1 = a^2 by rfl,
      show torusWeight 4 a 1 = a by simp [torusWeight], Units.val_pow_eq_pow_val]
    congr 1 <;> congr 1 <;> ring
  have heC (x : F) : e (C x) = C ((a : F)*x) := by
    dsimp [C]
    rw [map_commutatorElement, he, he]
    simp [torusWeight]
  have hDs (x : F) : D ((a : F)*x) = D x := by
    calc
      D ((a : F)*x) = e (D x) := by simp only [D, map_mul, map_inv, heC, heP]
      _ = D x := by
        change z * D x * z⁻¹ = D x
        rw [Subgroup.mem_center_iff.mp (hD x) z, mul_assoc, mul_inv_cancel, mul_one]
  have hDone : D c = 1 := additive_fixed_scale_eq_one D hDa (a : F)
    (fun H => ha (Units.ext H)) hDs c
  have hCP : C c = P c := by rw [hDC, hDone, one_mul]
  change X 2 v * X 6 c = X 6 c * X 0 (c^2*v) * X 4 (c*v) * X 2 v
  have H : X 2 v * X 6 c = P c * X 6 c * X 2 v := by
    rw [← hCP]
    dsimp [C, commutatorElement_def]
    group
  rw [H, (hP6 c c).eq]
  simp only [P, mul_assoc]

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField

end
