module
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic
/-!
# The seven-point core, its quadratic form and complementary plane

The sum of the coordinate products has the restricted dot product as its
polar form on the even-weight core. Its nonzero singular vectors have weight
four. Invariance therefore forces a nonzero single displacement `(g-1)e`
orthogonal to e to have weight four. This statement deliberately retains a
single displacement, rather than membership in their linear span.

The even vectors on the three complementary letters form an invariant plane,
disjoint from the distinguished line. Weight-four coordinates identify it
with `{0,e₅,₆,e₅,₇,e₆,₇}`. Nondegeneracy of the dot product gives the isotropic
dimension bound three. The only exhaustive checks enumerate the 128 binary
words; permutation invariance and polarization are proved structurally.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3 and
Lemma 12.8.13(6), printed pp.856–857, using 12.8.11(3).
-/

@[expose] public section
namespace BinaryPermutation.SevenParabolic
open Module
abbrev Space := core (Fin 7)
abbrev action := coreRepresentation (Fin 7)
def weight (v : Space) : ℕ := (Finset.univ.filter fun i => v.val i ≠ 0).card

def form : QuadraticForm (ZMod 2) Space :=
  (∑ i : Fin 7, ∑ j : Fin 7 with i < j,
    (QuadraticMap.proj i j : QuadraticForm (ZMod 2) (Full (Fin 7)))).comp
      (core (Fin 7)).subtype

def pairing : LinearMap.BilinForm (ZMod 2) Space :=
  (dotProductEquiv (ZMod 2) (Fin 7)).toLinearMap.compl₁₂
    (core (Fin 7)).subtype (core (Fin 7)).subtype

lemma pairing_apply (v w : Space) : pairing v w = ∑ i, v.val i * w.val i := rfl

lemma finrank_space : finrank (ZMod 2) Space = 6 := by
  simpa using BinaryPermutation.finrank_core (Fin 7)

lemma singular_iff (x : Space) : form x = 0 ↔ x = 0 ∨ weight x = 4 := by
  have h : ∀ x : Full (Fin 7), (∑ i, x i) = 0 →
      ((∑ i : Fin 7, ∑ j : Fin 7 with i < j, x i * x j) = 0 ↔
        x = 0 ∨ (Finset.univ.filter fun i => x i ≠ 0).card = 4) := by decide +kernel
  change (∑ i : Fin 7, ∑ j : Fin 7 with i < j, x.val i * x.val j) = 0 ↔ _
  simpa only [Subtype.ext_iff, Submodule.coe_zero, weight] using h x.val x.property

lemma weight_permute (g : Equiv.Perm (Fin 7)) (v : Space) :
    weight (action g v) = weight v := by
  change (Finset.univ.filter (fun i => v.val (g.symm i) ≠ 0)).card =
    (Finset.univ.filter (fun i => v.val i ≠ 0)).card
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    simpa using hi
  · intro i _ j _ h
    exact g.symm.injective h
  · intro j hj
    refine ⟨g j, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, coreRepresentation_apply, representation_apply, Equiv.symm_apply_apply] using hj

lemma form_permute (g : Equiv.Perm (Fin 7)) (v : Space) :
    form (action g v) = form v := by
  have hz : action g v = 0 ↔ v = 0 := by
    constructor
    · intro h
      apply Subtype.ext
      funext i
      have hi := congrArg (fun w : Space => w.val (g i)) h
      simpa using hi
    · intro h; rw [h, map_zero]
  have he : form (action g v) = 0 ↔ form v = 0 := by
    simp only [singular_iff, hz, weight_permute]
  have hb : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact hb _ _ he

lemma form_add (v w : Space) : form (v + w) = form v + form w + pairing v w := by
  have hv : ∑ i, v.val i = 0 := v.property
  have hw : ∑ i, w.val i = 0 := w.property
  have h : form (v + w) = form v + form w +
      (∑ i, v.val i) * (∑ i, w.val i) - pairing v w := by
    change (∑ i : Fin 7, ∑ j : Fin 7 with i < j, (v.val i + w.val i) * (v.val j + w.val j)) =
      (∑ i : Fin 7, ∑ j : Fin 7 with i < j, v.val i * v.val j) +
      (∑ i : Fin 7, ∑ j : Fin 7 with i < j, w.val i * w.val j) +
      (∑ i, v.val i) * (∑ i, w.val i) - ∑ i, v.val i * w.val i
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_succ]
    ring
  rw [hv, hw, zero_mul, add_zero, sub_eq_add_neg, CharTwo.neg_eq] at h
  exact h

lemma weight_four_of_displacement (g : Equiv.Perm (Fin 7))
    (v e : Space) (hv : v ≠ 0) (he : pairing e v = 0)
    (hmove : action g e - e = v) : weight v = 4 := by
  have ha : action g e = e + v := by
    rw [← hmove]; abel
  have hq := form_permute g e
  rw [ha, form_add, he, add_zero] at hq
  have hvq : form v = 0 := add_left_cancel (hq.trans (add_zero (form e)).symm)
  exact ((singular_iff v).mp hvq).resolve_left hv

private lemma pairing_separatingLeft : pairing.SeparatingLeft := by
  intro v hv
  apply (coreEquivNatural (Fin 7) (by decide)).injective
  apply naturalPairing_injective (Fin 7)
  ext w
  obtain ⟨w, rfl⟩ := (coreEquivNatural (Fin 7) (by decide)).surjective w
  have he (a b : Space) :
      naturalPairing (Fin 7) (coreEquivNatural (Fin 7) (by decide) a)
        (coreEquivNatural (Fin 7) (by decide) b) = pairing a b := by
    exact naturalPairing_apply_core (Fin 7) a b
  rw [he, map_zero, map_zero]
  exact hv w

lemma pairing_nondegenerate : pairing.Nondegenerate := by
  refine ⟨pairing_separatingLeft, ?_⟩
  intro v hv
  apply pairing_separatingLeft v
  intro w
  simpa only [pairing_apply, mul_comm] using hv w

lemma isotropic_finrank_le (E : Submodule (ZMod 2) Space)
    (hE : ∀ e ∈ E, ∀ f ∈ E, pairing e f = 0) : finrank (ZMod 2) E ≤ 3 := by
  have hle : E ≤ pairing.orthogonal E := by
    intro e he f hf
    exact hE f hf e he
  have h := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal pairing_nondegenerate, finrank_space] at h
  omega

/-- The weight-four representative `e₁,₂,₃,₄` in the book's one-based notation. -/
def firstFour : Space := ⟨![1, 1, 1, 1, 0, 0, 0], by rw [mem_core]; decide⟩

lemma firstFour_weight : weight firstFour = 4 := by decide

/-- Choose weight-four coordinates without changing the permutation action. -/
lemma exists_permutation_firstFour (v : Space) (hv : weight v = 4) :
    ∃ g : Equiv.Perm (Fin 7), action g v = firstFour := by
  have hc : Fintype.card {i : Fin 7 // v.val i ≠ 0} =
      Fintype.card {i : Fin 7 // firstFour.val i ≠ 0} := by
    simpa only [Fintype.card_subtype, weight] using hv.trans firstFour_weight.symm
  let e := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  apply Subtype.ext
  ext i
  change v.val (e.extendSubtype.symm i) = firstFour.val i
  have hb : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  apply hb
  constructor
  · intro h
    by_contra h'
    have hn := e.extendSubtype_not_mem (e.extendSubtype.symm i) (by simpa using h)
    exact hn (by simpa using h')
  · intro h
    by_contra h'
    have hn := e.extendSubtype_mem (e.extendSubtype.symm i) h'
    exact hn (by simpa using h)

/-- The point stabilizer for the literal core action. -/
def pointStabilizer (v : Space) : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {g | action g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (action g * action h) v = v
    rw [Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change action g⁻¹ v = v
    have h := congrArg (action g⁻¹) hg
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- The even vectors supported on the complement of the distinguished vector. -/
def plus (v : Space) : Submodule (ZMod 2) Space where
  carrier := {w | ∀ i, v.val i ≠ 0 → w.val i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

lemma plus_mem (v w : Space) : w ∈ plus v ↔ ∀ i, v.val i ≠ 0 → w.val i = 0 := Iff.rfl

lemma plus_invariant (v : Space) (g : Equiv.Perm (Fin 7))
    (hg : action g v = v) (w : Space) (hw : w ∈ plus v) : action g w ∈ plus v := by
  intro i hi
  apply hw (g.symm i)
  have h := congrArg (fun u : Space => u.val i) hg
  change v.val (g.symm i) = v.val i at h
  rwa [h]

lemma plus_orthogonal (v w : Space) (hw : w ∈ plus v) : pairing v w = 0 := by
  rw [pairing_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : v.val i = 0
  · rw [hi, zero_mul]
  · rw [hw i hi, mul_zero]

lemma plus_disjoint_line (v : Space) : Disjoint (plus v) (Submodule.span (ZMod 2) {v}) := by
  apply Submodule.disjoint_def.mpr
  intro w hw hl
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hl
  apply Subtype.ext
  ext i
  by_cases hi : v.val i = 0
  · simp [hi]
  · exact hw i hi

/-- The pointwise fixer of the complementary even plane, retaining the point stabilizer. -/
def plusFixer (v : Space) : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {g | action g v = v ∧ ∀ w ∈ plus v, action g w = w}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    constructor
    · exact (pointStabilizer v).mul_mem hg.1 hh.1
    · intro w hw
      change (action g * action h) w = w
      rw [Module.End.mul_apply, hh.2 w hw, hg.2 w hw]
  inv_mem' := by
    intro g hg
    refine ⟨(pointStabilizer v).inv_mem hg.1, ?_⟩
    intro w hw
    have h := congrArg (action g⁻¹) (hg.2 w hw)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- The three pair vectors on the complementary letters. -/
def pair56 : Space := ⟨![0, 0, 0, 0, 1, 1, 0], by rw [mem_core]; decide⟩
def pair57 : Space := ⟨![0, 0, 0, 0, 1, 0, 1], by rw [mem_core]; decide⟩
def pair67 : Space := ⟨![0, 0, 0, 0, 0, 1, 1], by rw [mem_core]; decide⟩

lemma plus_firstFour (w : Space) :
    w ∈ plus firstFour ↔ w = 0 ∨ w = pair56 ∨ w = pair57 ∨ w = pair67 := by
  have h : ∀ w : Full (Fin 7), (∑ i, w i) = 0 →
      ((∀ i, (![1, 1, 1, 1, 0, 0, 0] : Full (Fin 7)) i ≠ 0 → w i = 0) ↔
      w = 0 ∨ w = ![0, 0, 0, 0, 1, 1, 0] ∨ w = ![0, 0, 0, 0, 1, 0, 1] ∨
        w = ![0, 0, 0, 0, 0, 1, 1]) := by decide +kernel
  simpa only [plus_mem, firstFour, pair56, pair57, pair67, Subtype.ext_iff,
    Submodule.coe_zero] using h w.val w.property

end BinaryPermutation.SevenParabolic
