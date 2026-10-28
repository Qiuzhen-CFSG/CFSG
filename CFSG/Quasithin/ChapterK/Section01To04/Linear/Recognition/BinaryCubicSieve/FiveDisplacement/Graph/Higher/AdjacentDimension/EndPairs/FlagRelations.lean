module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction

/-!
# Flag relations for the left end-adjacent support

A local highest vector of support `{0,1}` is fixed by the upper roots and by
all roots on the final three coordinates. Consequently, matrices differing
on the right by a word in those roots have the same translate. The active
rank-one relations then give three-term relations among these translates.
`Case01` uses these rules to certify twenty-five independent vectors.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Lemma 4.2/Table 6 and Proposition 4.8(3B); Aschbacher–Smith K.3.2,
printed pp.454–455. The calculation uses the actual binary matrices and
local highest-vector relations, without a highest-weight comparison.
-/

@[expose] public section
open Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.EndPairs

def checkedMatrix (M N : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : M * N = 1) : Group :=
  ⟨M, by
    have hd : M.det * N.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
    have hn : M.det ≠ 0 := by intro hz; simp [hz] at hd
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact (hb M.det).resolve_left hn⟩

def rootWord (w : List (Fin 5 × Fin 5)) : Group :=
  (w.map fun t => rootElement t.1 t.2).prod

def Allowed (t : Fin 5 × Fin 5) : Prop :=
  t.1 < t.2 ∨ (2 ≤ t.1.val ∧ 2 ≤ t.2.val)
instance (t : Fin 5 × Fin 5) : Decidable (Allowed t) := inferInstanceAs (Decidable (_ ∨ _))

private def revLast : Fin 5 → Fin 5 := ![0, 1, 4, 3, 2]
private theorem revLast_lt (a b : Fin 5) (ha : 2 ≤ a.val) (hb : 2 ≤ b.val) (hba : b < a) :
    revLast a < revLast b := by revert a b; decide +kernel
private theorem reverse_root (a b : Fin 5) (ha : 2 ≤ a.val) (hb : 2 ≤ b.val) :
    rootElement a b = swapWord [2, 3, 2] * rootElement (revLast a) (revLast b) *
      swapWord [2, 3, 2] := by revert a b; decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {0, 1} v)
include h

omit h in
theorem binary_normalize {x y : V}
    (h : (1 : ZMod 2) • x = (1 : ZMod 2) • y) : x = y := by
  simpa only [one_smul] using h

theorem fixed_allowed (t : Fin 5 × Fin 5) (ht : Allowed t) :
    ρ (rootElement t.1 t.2) v = v := by
  rcases t with ⟨a, b⟩
  by_cases hab : a = b
  · subst b; simp [rootElement]
  rcases ht with ht | ⟨ha, hb⟩
  · simpa [rootElement, ne_of_lt ht] using h.upper_fixed a b ht
  rcases lt_or_gt_of_ne hab with ht | ht
  · simpa [rootElement, ne_of_lt ht] using h.upper_fixed a b ht
  have hw := fixed_word h [2, 3, 2] (by simp)
  have hr := revLast_lt a b ha hb ht
  have hu : ρ (rootElement (revLast a) (revLast b)) v = v := by
    simpa [rootElement, ne_of_lt hr] using h.upper_fixed _ _ hr
  rw [reverse_root a b ha hb]
  simp only [apply_mul, hw, hu]

theorem fixed_rootWord (w : List (Fin 5 × Fin 5)) (hw : ∀ t ∈ w, Allowed t) :
    ρ (rootWord w) v = v := by
  induction w with
  | nil => simp [rootWord]
  | cons t w ih =>
    change ρ (rootElement t.1 t.2 * rootWord w) v = v
    rw [apply_mul, ih (fun s hs => hw s (by simp [hs])), fixed_allowed h t (hw t (by simp))]

theorem translate_eq (a b : Group) (w : List (Fin 5 × Fin 5))
    (hw : ∀ t ∈ w, Allowed t) (he : a = b * rootWord w) : ρ a v = ρ b v := by
  rw [he, apply_mul, fixed_rootWord h w hw]

theorem difference_apply (t a b : Group) (w : List (Fin 5 × Fin 5))
    (hw : ∀ s ∈ w, Allowed s) (he : t * a = b * rootWord w) :
    difference ρ t (ρ a v) = ρ b v - ρ a v := by
  change ρ t (ρ a v) - ρ a v = _
  rw [← apply_mul, translate_eq h (t * a) b w hw he]

theorem relation (i : Fin 4) (hi : i ∈ ({0, 1} : Finset (Fin 4)))
    (g a b c : Group) (wa wb wc : List (Fin 5 × Fin 5))
    (hwa : ∀ t ∈ wa, Allowed t) (hwb : ∀ t ∈ wb, Allowed t)
    (hwc : ∀ t ∈ wc, Allowed t)
    (ha : g = a * rootWord wa)
    (hb : g * simpleSwap i = b * rootWord wb)
    (hc : g * simpleLower i = c * rootWord wc) :
    ρ a v + ρ b v + ρ c v = 0 := by
  have hh := congrArg (ρ g) (h.active_relation i hi)
  simp only [map_add, ← apply_mul, map_zero] at hh
  rw [translate_eq h g a wa hwa ha,
    translate_eq h (g * simpleSwap i) b wb hwb hb,
    translate_eq h (g * simpleLower i) c wc hwc hc] at hh
  exact hh

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.EndPairs
