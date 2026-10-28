module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
/-!
# Binary certificates for the native A₆ sixteen-space

Two fixed-point equations have a checked linear left inverse modulo a
specified two-dimensional space. Each of its three nonzero vectors is
cyclic under two generator matrices: sixteen short orbit words form an
invertible matrix. Every entry and inverse identity is checked by kernel
reduction; no exhaustive invariant-subspace search is used.

The companion Coordinates module identifies these four matrices with the
published tensor action. Source: Aschbacher–Smith G.5.1, printed pp.342–343.
-/
@[expose] public section
namespace BinaryAlternatingSix.TensorIrreducibility.Certificate
abbrev Vec := Fin 16 → ZMod 2
abbrev Mat := Matrix (Fin 16) (Fin 16) (ZMod 2)
def bits (n : ℕ) : Vec := fun i => if n.testBit i.val then 1 else 0
def cols (a : Array ℕ) : Mat := fun i j => bits a[j.val]! i
def R : Mat := cols #[56589, 13059, 52236, 34824, 221, 51, 204, 136, 56576, 13056, 52224, 34816, 53248, 12288, 49152, 32768]
def S : Mat := cols #[4353, 47883, 52236, 34824, 272, 2992, 3264, 2176, 256, 2816, 3072, 2048, 4096, 45056, 49152, 32768]
def G : Mat := cols #[8, 4, 6, 9, 32768, 16384, 24576, 36864, 2048, 1024, 1536, 2304, 32896, 16448, 24672, 37008]
def H : Mat := cols #[119, 153, 17, 34, 30576, 39312, 4368, 8736, 1911, 2457, 273, 546, 112, 144, 16, 32]
def left : Mat := cols #[27526, 27558, 27521, 128, 0, 0, 27606, 27457, 27136, 0, 27904, 5120, 26624, 0, 6144, 2048]
def right : Mat := cols #[0, 0, 0, 8580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18432]
def projection : Mat := cols #[0, 0, 0, 21512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32768]
theorem fixed_certificate : projection + left * (R + 1) + right * (S + 1) = 1 := by
  decide +kernel
end BinaryAlternatingSix.TensorIrreducibility.Certificate

namespace BinaryAlternatingSix.TensorIrreducibility.Certificate
def orbitData : Fin 3 → Array ℕ := ![#[21512, 59113, 339, 689, 41693, 59404, 25081, 50478, 19757, 47551, 6177, 55922, 48891, 40812, 10087, 55158], #[32768, 37008, 32, 16, 21760, 16384, 39312, 30576, 1542, 24672, 272, 20565, 2720, 61695, 514, 45067], #[54280, 30329, 371, 673, 63453, 43020, 63593, 45662, 19243, 55775, 6449, 35367, 46171, 28563, 9573, 26493]]
def inverseData : Fin 3 → Array ℕ := ![#[56664, 21878, 2040, 29745, 48197, 2988, 13974, 53480, 761, 47697, 39878, 5831, 50227, 53634, 11205, 40809], #[43023, 17080, 21445, 39792, 8, 4, 58655, 5878, 1032, 696, 4805, 1098, 5885, 59195, 32, 1], #[30039, 6094, 21565, 61249, 48205, 2984, 54153, 50718, 1777, 47337, 35075, 4749, 53966, 14009, 11237, 40808]]
def orbitMatrix (a : Fin 3) : Mat := cols (orbitData a)
def inverseMatrix (a : Fin 3) : Mat := cols (inverseData a)
def seed : Fin 3 → Vec := ![bits 21512,bits 32768,bits 54280]
def parent : Fin 16 → Fin 16 := ![0, 0, 0, 1, 1, 2, 2, 3, 4, 5, 6, 6, 7, 7, 8, 12]
def isH : Fin 16 → Bool := ![false, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true]
theorem parent_lt (i : Fin 16) (hi : i ≠ 0) : (parent i).val < i.val := by
  fin_cases i <;> first | contradiction | decide +kernel

theorem orbit_zero (a : Fin 3) : (orbitMatrix a).transpose 0 = seed a := by
  fin_cases a <;> decide +kernel

theorem orbit_step (a : Fin 3) (i : Fin 16) (hi : i ≠ 0) :
    (orbitMatrix a).transpose i =
      (if isH i then H else G).mulVec ((orbitMatrix a).transpose (parent i)) := by
  fin_cases a <;> fin_cases i <;> first | contradiction | decide +kernel

theorem orbit_inverse (a : Fin 3) : orbitMatrix a * inverseMatrix a = 1 := by
  fin_cases a <;> decide +kernel

theorem projection_apply (v : Vec) :
    projection.mulVec v = v 3 • bits 21512 + v 15 • bits 32768 := by
  ext i
  fin_cases i <;>
    simp [projection, cols, bits, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem fixed_cases (v : Vec) (hr : R.mulVec v = v) (hs : S.mulVec v = v) :
    v = 0 ∨ ∃ a : Fin 3, v = seed a := by
  have he := congrArg (fun M : Mat => M.mulVec v) fixed_certificate
  have hz : v + v = 0 := by ext i; exact CharTwo.add_self_eq_zero (v i)
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hr, hs,
    hz, Matrix.mulVec_zero, add_zero] at he
  rw [projection_apply] at he
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  rcases hc (v 3) with h3 | h3 <;> rcases hc (v 15) with h15 | h15
  · left; simpa only [h3,h15,zero_smul,zero_add] using he.symm
  · right; refine ⟨1,?_⟩; change v = bits 32768
    simpa only [h3,h15,zero_smul,one_smul,zero_add] using he.symm
  · right; refine ⟨0,?_⟩; change v = bits 21512
    simpa only [h3,h15,zero_smul,one_smul,add_zero] using he.symm
  · right
    refine ⟨2,?_⟩
    have hb : bits 21512 + bits 32768 = bits 54280 := by decide +kernel
    change v = bits 54280
    simpa only [h3,h15,one_smul,hb] using he.symm

theorem cyclic_eq_top (U : Submodule (ZMod 2) Vec)
    (hg : ∀ v ∈ U, G.mulVec v ∈ U) (hh : ∀ v ∈ U, H.mulVec v ∈ U)
    (a : Fin 3) (ha : seed a ∈ U) : U = ⊤ := by
  have ho (i : Fin 16) : (orbitMatrix a).transpose i ∈ U := by
    induction i using (measure Fin.val).wf.induction with
    | h i ih =>
      by_cases hi : i = 0
      · subst i; simpa only [orbit_zero] using ha
      · rw [orbit_step a i hi]
        split
        · exact hh _ (ih (parent i) (parent_lt i hi))
        · exact hg _ (ih (parent i) (parent_lt i hi))
  apply top_unique
  intro v _
  have he : v = (orbitMatrix a).mulVec ((inverseMatrix a).mulVec v) := by
    rw [Matrix.mulVec_mulVec, orbit_inverse, Matrix.one_mulVec]
  rw [he]
  have hs : (orbitMatrix a).mulVec ((inverseMatrix a).mulVec v) =
      ∑ j : Fin 16, ((inverseMatrix a).mulVec v) j • (orbitMatrix a).transpose j := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hs]
  exact U.sum_mem fun j _ => U.smul_mem _ (ho j)
end BinaryAlternatingSix.TensorIrreducibility.Certificate
