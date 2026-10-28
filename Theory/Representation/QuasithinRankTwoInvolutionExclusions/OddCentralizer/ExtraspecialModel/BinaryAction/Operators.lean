module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.Group
public import Theory.Representation.SL2FourNaturalOrbits.Model
import Mathlib.Tactic

/-!
# Explicit operators for the extraspecial-three binary module

On functions from F₃ to the concrete quadratic field F₄, Heisenberg triples
act by translation and multiplication by powers of a primitive cube root.
The two displayed matrices, composed with coordinatewise Frobenius, satisfy
the SD₁₆ relations and induce exactly `rotate` and `reflect` on this subgroup.
The semidirect-product compatibility follows from its three generators.

Finite certificates test linear maps on single-coordinate vectors. The
rotation's square is computed first; its fourth power reverses coordinates.
Thus no certificate enumerates the full general linear group or expands an
eighth iterate of the concrete matrix operator.

This constructs the operators for the SD₁₆/3^(1+2) model in Aschbacher–Smith,
G.9.4(5), printed pp.354–355, and G.11.2(3), printed p.364. The faithful
semidirect-product action and marked image are assembled in `BinaryAction`.
-/

@[expose] public section

namespace Representation.RankTwo.ExtraspecialModel.BinaryAction
abbrev F := SL2FourNatural.F
abbrev V := ZMod 3 → F
def w : F := ⟨0, 1⟩
def chi (a : ZMod 3) : F := w ^ a.val
lemma chi_add (a b : ZMod 3) : chi (a + b) = chi a * chi b := by
  revert a b
  decide +kernel
lemma chi_zero : chi 0 = 1 := rfl

def heisenbergLinear (p : P) : V →ₗ[F] V where
  toFun f t := chi (p.c + p.b * t) * f (t + p.a)
  map_add' f g := by funext t; exact mul_add _ _ _
  map_smul' c f := by funext t; exact mul_left_comm _ _ _

lemma heisenbergLinear_one : heisenbergLinear 1 = 1 := by
  apply LinearMap.ext
  intro f
  funext t
  simp [heisenbergLinear, chi_zero]
lemma heisenbergLinear_mul (p q : P) :
    heisenbergLinear (p * q) = heisenbergLinear p * heisenbergLinear q := by
  apply LinearMap.ext
  intro f
  funext t
  change chi (p.c + q.c + p.a * q.b + (p.b + q.b) * t) * f (t + (p.a + q.a)) =
    chi (p.c + p.b * t) * (chi (q.c + q.b * (t + p.a)) * f (t + p.a + q.a))
  rw [show p.c + q.c + p.a * q.b + (p.b + q.b) * t =
    (p.c + p.b * t) + (q.c + q.b * (t + p.a)) by ring, chi_add]
  simp only [mul_assoc, add_assoc]

def heisenberg : P →* (V ≃ₗ[ZMod 2] V) where
  toFun p :=
    { (heisenbergLinear p).restrictScalars (ZMod 2) with
      invFun := heisenbergLinear p⁻¹
      left_inv f := by
        have h := LinearMap.congr_fun (heisenbergLinear_mul p⁻¹ p) f
        simpa [heisenbergLinear_one] using h.symm
      right_inv f := by
        have h := LinearMap.congr_fun (heisenbergLinear_mul p p⁻¹) f
        simpa [heisenbergLinear_one] using h.symm }
  map_one' := by apply LinearEquiv.ext; intro f; exact LinearMap.congr_fun heisenbergLinear_one f
  map_mul' p q := by apply LinearEquiv.ext; intro f; exact LinearMap.congr_fun (heisenbergLinear_mul p q) f

lemma heisenberg_apply (p : P) (f : V) (t : ZMod 3) :
    heisenberg p f t = w ^ (p.c + p.b * t).val * f (t + p.a) := rfl

lemma heisenberg_injective : Function.Injective heisenberg := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro p hp
  have hh : ∀ i t, chi (p.c + p.b * t) * (Pi.single i (1 : F) : V) (t + p.a) =
      (Pi.single i (1 : F) : V) t := by
    intro i t
    exact congrFun (LinearEquiv.congr_fun (show heisenberg p = 1 from hp) (Pi.single i 1)) t
  have cert : ∀ a b c : ZMod 3,
      (∀ i t : ZMod 3, chi (c + b * t) * (Pi.single i (1 : F) : V) (t + a) =
        (Pi.single i (1 : F) : V) t) → a = 0 ∧ b = 0 ∧ c = 0 := by decide +kernel
  obtain ⟨ha, hb, hc⟩ := cert p.a p.b p.c hh
  change p = 1
  ext <;> assumption

def frob : V →ₗ[ZMod 2] V where
  toFun f t := SL2FourNatural.fieldFrobenius (f t)
  map_add' f g := by funext t; exact map_add SL2FourNatural.fieldFrobenius _ _
  map_smul' c f := by
    funext t
    change SL2FourNatural.fieldFrobenius (c • f t) = c • SL2FourNatural.fieldFrobenius (f t)
    fin_cases c
    · change SL2FourNatural.fieldFrobenius ((0 : ZMod 2) • f t) = (0 : ZMod 2) • _
      simp
    · change SL2FourNatural.fieldFrobenius ((1 : ZMod 2) • f t) = (1 : ZMod 2) • _
      simp

def matrixM : Matrix (ZMod 3) (ZMod 3) F := fun i j =>
  (!![1, w^2, w^2; 1, w, 1; 1, 1, w] : Matrix (Fin 3) (Fin 3) F) ⟨i.val, i.val_lt⟩ ⟨j.val, j.val_lt⟩
def matrixN : Matrix (ZMod 3) (ZMod 3) F := fun i j =>
  (!![1, 0, 0; 0, 0, w^2; 0, w^2, 0] : Matrix (Fin 3) (Fin 3) F) ⟨i.val, i.val_lt⟩ ⟨j.val, j.val_lt⟩
def rLinear : V →ₗ[ZMod 2] V :=
  ((Matrix.mulVecLin matrixM).restrictScalars (ZMod 2)).comp frob
def bLinear : V →ₗ[ZMod 2] V :=
  ((Matrix.mulVecLin matrixN).restrictScalars (ZMod 2)).comp frob

def reverseLinear : V →ₗ[ZMod 2] V where
  toFun f t := f (-t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def squareLinear : V →ₗ[ZMod 2] V :=
  (Matrix.mulVecLin (fun i j : ZMod 3 =>
    (!![1, w^2, w^2; w, w, w^2; w, w^2, w] : Matrix (Fin 3) (Fin 3) F)
      ⟨i.val, i.val_lt⟩ ⟨j.val, j.val_lt⟩)).restrictScalars (ZMod 2)

private lemma rLinear_square : rLinear ^ 2 = squareLinear := by
  apply LinearMap.pi_ext
  decide +kernel
private lemma squareLinear_square : squareLinear ^ 2 = reverseLinear := by
  apply LinearMap.pi_ext
  decide +kernel
lemma rLinear_four : rLinear ^ 4 = reverseLinear := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, rLinear_square, squareLinear_square]
lemma reverseLinear_two : reverseLinear ^ 2 = 1 := by
  apply LinearMap.ext
  intro f
  funext t
  change f (- -t) = f t
  rw [neg_neg]
lemma rLinear_eight : rLinear ^ 8 = 1 := by
  rw [show 8 = 4 * 2 from rfl, pow_mul, rLinear_four, reverseLinear_two]
lemma bLinear_two : bLinear ^ 2 = 1 := by
  apply LinearMap.pi_ext
  decide +kernel
lemma bLinear_rLinear : bLinear * rLinear * bLinear = rLinear ^ 3 := by
  apply LinearMap.pi_ext
  decide +kernel


/-- Turn an endomorphism of specified finite order into an automorphism. -/
def equivOfPower (f : V →ₗ[ZMod 2] V) (n : ℕ) (h : f ^ (n + 1) = 1) :
    V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap f (f ^ n)
  (by change f * f ^ n = 1; rw [← pow_succ']; exact h)
  (by change f ^ n * f = 1; rw [← pow_succ]; exact h)

def R : V ≃ₗ[ZMod 2] V := equivOfPower rLinear 7 rLinear_eight
def B : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap bLinear bLinear
  (by change bLinear * bLinear = 1; simpa only [pow_two] using bLinear_two)
  (by change bLinear * bLinear = 1; simpa only [pow_two] using bLinear_two)
private lemma linearEquiv_pow (g : V ≃ₗ[ZMod 2] V) (n : ℕ) :
    (g ^ n).toLinearMap = g.toLinearMap ^ n :=
  map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom g n
private lemma R_linear : R.toLinearMap = rLinear := rfl
private lemma B_linear : B.toLinearMap = bLinear := rfl
lemma R_eight : R ^ 8 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  rw [linearEquiv_pow, R_linear]
  exact rLinear_eight
lemma B_two : B ^ 2 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  rw [linearEquiv_pow, B_linear]
  exact bLinear_two
lemma B_R : B * R * B⁻¹ = R ^ 3 := by
  have hB : B⁻¹ = B := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using B_two
  rw [hB]
  apply LinearEquiv.toLinearMap_injective
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
    linearEquiv_pow, R_linear, B_linear]
  exact bLinear_rLinear

def complement : S →* (V ≃ₗ[ZMod 2] V) := complementHom R B R_eight B_two B_R
lemma complement_rotation :
    complement (Semidihedral.standardRotation 4 (Nat.le_refl 4)) = R :=
  complementHom_rotation _ _ _ _ _
lemma complement_reflection :
    complement (Semidihedral.standardReflection 4 (Nat.le_refl 4)) = B :=
  complementHom_reflection _ _ _ _ _

private lemma p_normal_form (p : P) :
    p = (⟨0, 1, 0⟩ : P) ^ p.b.val * (⟨1, 0, 0⟩ : P) ^ p.a.val *
      (⟨0, 0, 1⟩ : P) ^ p.c.val := by
  rcases p with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> apply HeisenbergPrime.ext <;> decide

private lemma p_generators :
    Subgroup.closure ({⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩} : Set P) = ⊤ := by
  apply top_unique
  intro p _
  rw [p_normal_form p]
  apply mul_mem
  · apply mul_mem <;> apply pow_mem <;> apply Subgroup.subset_closure <;> simp
  · apply pow_mem; apply Subgroup.subset_closure; simp

private lemma conjugation_of_generators (a : MulAut P) (g : V ≃ₗ[ZMod 2] V)
    (hx : heisenberg (a ⟨1, 0, 0⟩) * g = g * heisenberg ⟨1, 0, 0⟩)
    (hy : heisenberg (a ⟨0, 1, 0⟩) * g = g * heisenberg ⟨0, 1, 0⟩)
    (hc : heisenberg (a ⟨0, 0, 1⟩) * g = g * heisenberg ⟨0, 0, 1⟩) (p : P) :
    heisenberg (a p) = g * heisenberg p * g⁻¹ := by
  have h : heisenberg.comp a.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp heisenberg := by
    apply MonoidHom.eq_of_eqOn_dense p_generators
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact (eq_mul_inv_iff_mul_eq).mpr hx
    · exact (eq_mul_inv_iff_mul_eq).mpr hy
    · exact (eq_mul_inv_iff_mul_eq).mpr hc
  exact DFunLike.congr_fun h p

lemma rotate_intertwines (p : P) : heisenberg (rotate p) * R = R * heisenberg p := by
  apply (eq_mul_inv_iff_mul_eq).mp
  apply conjugation_of_generators rotate R
  all_goals
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.pi_ext
    decide +kernel
lemma reflect_intertwines (p : P) : heisenberg (reflect p) * B = B * heisenberg p := by
  apply (eq_mul_inv_iff_mul_eq).mp
  apply conjugation_of_generators reflect B
  all_goals
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.pi_ext
    decide +kernel

lemma compatibility (s : S) (p : P) :
    heisenberg (action s p) = complement s * heisenberg p * (complement s)⁻¹ := by
  let T : Subgroup S :=
    { carrier := {s | ∀ p, heisenberg (action s p) =
          complement s * heisenberg p * (complement s)⁻¹}
      one_mem' := by intro p; simp
      mul_mem' := by
        intro x y hx hy p
        change ∀ p, heisenberg (action x p) = _ at hx
        change ∀ p, heisenberg (action y p) = _ at hy
        simp only [map_mul, MulAut.mul_apply, hx, hy, mul_inv_rev]
        group
      inv_mem' := by
        intro x hx p
        have hh := hx (action x⁻¹ p)
        simp only [map_inv, MulAut.apply_inv_self] at hh
        simp only [map_inv, inv_inv]
        rw [hh]
        group }
  have hT : (⊤ : Subgroup S) ≤ T := by
    rw [← Semidihedral.standard_generators 4 (Nat.le_refl 4)]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · intro p
      rw [action_rotation, complement_rotation]
      exact (eq_mul_inv_iff_mul_eq).mpr (rotate_intertwines p)
    · intro p
      rw [action_reflection, complement_reflection]
      exact (eq_mul_inv_iff_mul_eq).mpr (reflect_intertwines p)
  exact hT (Subgroup.mem_top s) p

end Representation.RankTwo.ExtraspecialModel.BinaryAction
