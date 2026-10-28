module

public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# A thirty-element five-normalizer over the golden field

For the block rotation `diag(1, [[0,1],[1,τ]])`, every normalizing matrix
intertwines it with one of its four nonidentity powers. The fixed-row and
fixed-column equations force the off-block entries to vanish. Determinant
one then determines the upper-left entry as the inverse determinant of the
lower two-by-two block.

This gives an equivalence with the invertible two-by-two blocks satisfying
one of the four intertwining equations. Kernel-checked finite calculations
on the 256 possible blocks give exactly thirty parameters; the fixed-vector
checks use only the sixteen vectors over `GoldenFour`. No enumeration of
SL₃(4) is used. `Normalizer` transports the result to the marked source model.

Source context: Aschbacher, *Sporadic Groups* (1994), proof of 49.5,
pp.283–284, with the local placement from 48.3, 49.2 and 48.8.
-/

@[expose] public section

open Matrix Atlas.Algebra
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.FiveNormalizer

def rot : Matrix (Fin 2) (Fin 2) GoldenFour := !![0,1;1,goldenFourTau]
def diag (c : GoldenFour) (a : Matrix (Fin 2) (Fin 2) GoldenFour) :
    Matrix (Fin 3) (Fin 3) GoldenFour :=
  !![c,0,0;0,a 0 0,a 0 1;0,a 1 0,a 1 1]

theorem diag_mul (c d : GoldenFour) (a b : Matrix (Fin 2) (Fin 2) GoldenFour) :
    diag c a * diag d b = diag (c*d) (a*b) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diag, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem diag_one : diag 1 1 = 1 := by decide +kernel

theorem diag_pow (a : Matrix (Fin 2) (Fin 2) GoldenFour) (k : ℕ) :
    (diag 1 a)^k = diag 1 (a^k) := by
  induction k with
  | zero => simp [diag_one]
  | succ k ih => simp [pow_succ, ih, diag_mul]

theorem diag_det (c : GoldenFour) (a : Matrix (Fin 2) (Fin 2) GoldenFour) :
    (diag c a).det = c * a.det := by
  simp [diag, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

def bigR : SL(3,GoldenFour) := ⟨diag 1 rot, by decide +kernel⟩

theorem bigR_order : orderOf bigR = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

abbrev N := Subgroup.normalizer (Subgroup.zpowers bigR : Set SL(3,GoldenFour))

theorem mem_N_iff (g : SL(3,GoldenFour)) : g ∈ N ↔
    ∃ k : Fin 5, k ≠ 0 ∧ g * bigR = bigR ^ k.val * g := by
  constructor
  · intro hg
    have hm := (Subgroup.mem_normalizer_iff.mp hg bigR).mp (Subgroup.mem_zpowers _)
    rw [mem_zpowers_iff_mem_range_orderOf, bigR_order] at hm
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hm
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_, ?_⟩
    · intro hz
      have hk0 : k = 0 := congrArg Fin.val hz
      simp only [hk0, pow_zero] at he
      have hR : bigR = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) he
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this.symm
      have : bigR ≠ 1 := by decide +kernel
      exact this hR
    · simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (· * g) he.symm
  · rintro ⟨k, hk, he⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hc : MulAut.conj g bigR = bigR ^ k.val := by
      change g * bigR * g⁻¹ = _
      rw [he, mul_assoc, mul_inv_cancel, mul_one]
    change Subgroup.zpowers (MulAut.conj g bigR) = _
    rw [hc]
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers _ _)
    · apply Subgroup.zpowers_le.mpr
      rw [mem_zpowers_pow_iff, bigR_order]
      revert hk
      fin_cases k <;> decide


def lower (a : Matrix (Fin 3) (Fin 3) GoldenFour) : Matrix (Fin 2) (Fin 2) GoldenFour :=
  fun i j => a i.succ j.succ

def Parameters := {a : Matrix (Fin 2) (Fin 2) GoldenFour //
  a.det ≠ 0 ∧ ∃ k : Fin 5, k ≠ 0 ∧ a * rot = rot ^ k.val * a}
instance : Fintype Parameters := inferInstanceAs (Fintype (Subtype _))

theorem parameters_card : Fintype.card Parameters = 30 := by decide +kernel

theorem fixed_col : ∀ k : Fin 5, k ≠ 0 → ∀ v : Fin 2 → GoldenFour,
    rot ^ k.val *ᵥ v = v → v = 0 := by decide +kernel

theorem fixed_row : ∀ v : Fin 2 → GoldenFour, v 0 = v 1 →
    v 1 = v 0 + v 1 * goldenFourTau → v = 0 := by decide +kernel

theorem matrix_form (a : Matrix (Fin 3) (Fin 3) GoldenFour)
    (k : Fin 5) (hk : k ≠ 0) (he : a * diag 1 rot = diag 1 (rot^k.val) * a) :
    a = diag (a 0 0) (lower a) := by
  have h01 := congrFun (congrFun he 0) 1
  have h02 := congrFun (congrFun he 0) 2
  simp [diag, rot, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02
  have hr := fixed_row ![a 0 1, a 0 2] h01.symm h02.symm
  have h10 := congrFun (congrFun he 1) 0
  have h20 := congrFun (congrFun he 2) 0
  have hv : rot^k.val *ᵥ ![a 1 0,a 2 0] = ![a 1 0,a 2 0] := by
    funext i
    fin_cases i
    · simpa [diag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] using h10.symm
    · simpa [diag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] using h20.symm
  have hc := fixed_col k hk _ hv
  have hr1 := congrFun hr 0
  have hr2 := congrFun hr 1
  have hc1 := congrFun hc 0
  have hc2 := congrFun hc 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [diag, lower]

theorem lower_intertwines (a : Matrix (Fin 3) (Fin 3) GoldenFour)
    (k : Fin 5) (he : a * diag 1 rot = diag 1 (rot^k.val) * a) :
    lower a * rot = rot ^ k.val * lower a := by
  apply Matrix.ext
  intro i j
  have h := congrFun (congrFun he i.succ) j.succ
  fin_cases i <;> fin_cases j <;>
    simpa [lower, diag, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] using h

theorem normalizer_form (g : N) :
    g.val.val = diag ((lower g.val.val).det)⁻¹ (lower g.val.val) ∧
    (lower g.val.val).det ≠ 0 ∧
      ∃ k : Fin 5, k ≠ 0 ∧ lower g.val.val * rot = rot ^ k.val * lower g.val.val := by
  obtain ⟨k, hk, he⟩ := (mem_N_iff g.val).mp g.property
  have hm : g.val.val * diag 1 rot = diag 1 (rot^k.val) * g.val.val := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      bigR, diag_pow] using congrArg Subtype.val he
  have hf := matrix_form g.val.val k hk hm
  have hd := g.val.property
  rw [hf, diag_det] at hd
  have hn : (lower g.val.val).det ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, zero_ne_one] at hd
  refine ⟨?_, hn, k, hk, lower_intertwines _ k hm⟩
  calc
    _ = diag (g.val.val 0 0) (lower g.val.val) := hf
    _ = _ := by rw [eq_inv_of_mul_eq_one_left hd]


def parameterSL (p : Parameters) : SL(3,GoldenFour) :=
  ⟨diag p.val.det⁻¹ p.val, by rw [diag_det, inv_mul_cancel₀ p.property.1]⟩

theorem parameterSL_mem (p : Parameters) : parameterSL p ∈ N := by
  obtain ⟨k, hk, he⟩ := p.property.2
  apply (mem_N_iff _).mpr
  refine ⟨k, hk, ?_⟩
  apply Subtype.ext
  change diag p.val.det⁻¹ p.val * diag 1 rot = (diag 1 rot)^k.val * diag p.val.det⁻¹ p.val
  rw [diag_pow, diag_mul, diag_mul, mul_one, one_mul, he]

def normalizerEquiv : N ≃ Parameters where
  toFun g := ⟨lower g.val.val, (normalizer_form g).2⟩
  invFun p := ⟨parameterSL p, parameterSL_mem p⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact (normalizer_form g).1.symm
  right_inv p := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem normalizer_card : Nat.card N = 30 := by
  rw [Nat.card_congr normalizerEquiv, Nat.card_eq_fintype_card, parameters_card]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.FiveNormalizer
