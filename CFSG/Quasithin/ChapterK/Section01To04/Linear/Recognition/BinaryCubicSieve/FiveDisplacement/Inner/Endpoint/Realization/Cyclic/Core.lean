module
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction

/-!
# Transport of binary endpoint relations

The positive roots and the lower roots inside coordinates 1, 2, 3 fix a
vector of support {0, 3}. Products of these roots therefore identify orbit
vectors. Translating either active rank-one relation gives an additive
triangle. `Geometry` uses these lemmas for the incident rank-one matrices
needed to construct the marked adjoint map.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author
manuscript, Lemma 4.5 step 2, pp.23–24. This proves the local-relation
recognition needed to apply the source's adjoint-module case over F₂.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Representation
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
abbrev Group := Representation.SL5TenDimensional.Group

/-- A checked right inverse gives a binary special-linear matrix without a
factorial determinant computation. -/
def matrixElement (M N : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : M * N = 1) : Group :=
  ⟨M, by
    have hn : Matrix.det M ≠ 0 := by
      intro hz
      have hh := congrArg Matrix.det h
      rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hh
      exact zero_ne_one hh
    exact (show ∀ c : ZMod 2, c ≠ 0 → c = 1 by decide) _ hn⟩

def fixedRoot : Fin 13 → Group :=
  ![rootElement 0 1, rootElement 0 2, rootElement 0 3, rootElement 0 4,
    rootElement 1 2, rootElement 1 3, rootElement 1 4, rootElement 2 3,
    rootElement 2 4, rootElement 3 4, rootElement 2 1, rootElement 3 1, rootElement 3 2]
def fixedWord (w : List (Fin 13)) : Group := (w.map fixedRoot).prod
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

/-- Additive cancellation of two copies, in the integer-scalar form used by
normalization of the incident-pair relations. -/
theorem binary_two_zsmul (x : V) : (2 : ℤ) • x = 0 := by
  have ht : (2 : ZMod 2) = 0 := by decide
  simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) ht

theorem fixedRoot_fixed (h : LocalHighestVector σ {0, 3} v) (i : Fin 13) :
    σ (fixedRoot i) v = v := by
  fin_cases i
  all_goals first
  | exact h.upper_fixed _ _ (by decide)
  | skip
  · have hh := difference_zero h (rootElement 2 1) 1 [1]
      (by decide) 1 2 (by decide) (by decide +kernel)
    simpa [difference, sub_eq_zero, fixedRoot] using hh
  · have hh := difference_zero h (rootElement 3 1) 1 [2, 1, 2]
      (by decide) 1 3 (by decide) (by decide +kernel)
    simpa [difference, sub_eq_zero, fixedRoot] using hh
  · have hh := difference_zero h (rootElement 3 2) 1 [2]
      (by decide) 2 3 (by decide) (by decide +kernel)
    simpa [difference, sub_eq_zero, fixedRoot] using hh

theorem fixedWord_fixed (h : LocalHighestVector σ {0, 3} v) (w : List (Fin 13)) :
    σ (fixedWord w) v = v := by
  induction w with
  | nil => simp [fixedWord]
  | cons i w ih =>
    change σ (fixedRoot i * fixedWord w) v = v
    rw [apply_mul, ih, fixedRoot_fixed h]

theorem word_transport (h : LocalHighestVector σ {0, 3} v)
    (g r : Group) (w : List (Fin 13)) (he : g = r * fixedWord w) :
    σ g v = σ r v := by
  rw [he, apply_mul, fixedWord_fixed h]

theorem triangle_relation (h : LocalHighestVector σ {0, 3} v)
    (g a b c : Group) (i : Fin 4) (hi : i ∈ ({0, 3} : Finset (Fin 4)))
    (wa wb wc : List (Fin 13))
    (ha : g = a * fixedWord wa)
    (hb : g * simpleSwap i = b * fixedWord wb)
    (hc : g * simpleLower i = c * fixedWord wc) :
    σ a v + σ b v + σ c v = 0 := by
  have hh := congrArg (σ g) (h.active_relation i hi)
  simp only [map_add, map_zero, ← apply_mul] at hh
  rw [word_transport h _ _ wa ha, word_transport h _ _ wb hb,
    word_transport h _ _ wc hc] at hh
  exact hh
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
