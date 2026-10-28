module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Empty support forces a trivial binary SL₅ module

An upper-fixed vector fixed by every adjacent coordinate exchange is fixed by
all of SL₅(2). Indeed, a word in the exchanges reverses the coordinates and
conjugates lower transvections into upper transvections. These transvections
generate SL₅(2), since the only nonzero binary diagonal entries are one.

The line spanned by such a vector is consequently a subrepresentation. If the
vector is nonzero and the representation is irreducible, this line is the whole
module, which therefore has dimension one.

This is the empty-support case of the highest-vector route to the module
identification used in Aschbacher--Smith, *The Classification of Quasithin
Groups*, I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification
private def reverseWord : List (Fin 4) := [0, 1, 0, 2, 1, 0, 3, 2, 1, 0]
private def reverseElement : Group := (reverseWord.map simpleSwap).prod
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
private theorem reverse_transvection : ∀ (i j : Fin 5) (hij : i ≠ j),
    Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) =
      reverseElement * Matrix.SpecialLinearGroup.transvection
        (show i.rev ≠ j.rev from fun h => hij (Fin.rev_injective h)) (1 : ZMod 2) *
      reverseElement := by
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem fixed_mul {ρ : Representation (ZMod 2) Group V} {v : V}
    {g k : Group} (hg : ρ g v = v) (hk : ρ k v = v) : ρ (g * k) v = v := by
  rw [map_mul]
  change ρ g (ρ k v) = v
  rw [hk, hg]

private theorem fixed_reverse {ρ : Representation (ZMod 2) Group V} {v : V}
    (h : ∀ i, ρ (simpleSwap i) v = v) : ρ reverseElement v = v := by
  have hl (l : List (Fin 4)) : ρ (l.map simpleSwap).prod v = v := by
    induction l with
    | nil => simp
    | cons i l ih => exact fixed_mul (h i) ih
  exact hl reverseWord

/-- Empty support makes the vector fixed by the entire group. -/
theorem LocalHighestVector.fixed_of_empty
    {ρ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector ρ ∅ v) (g : Group) : ρ g v = v := by
  have hr : ρ reverseElement v = v :=
    fixed_reverse (fun i => h.inactive_fixed i (Finset.notMem_empty i))
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun g => ρ g v = v) g
  · intro i j hij c hc
    have hc1 : c = 1 := by
      have : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      exact this c hc
    subst c
    have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe]
    rw [hd]
    simp
  · intro i j hij c
    have hc : c = 0 ∨ c = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this c
    rcases hc with rfl | rfl
    · simp [Matrix.SpecialLinearGroup.transvection_coeff_zero]
    · rcases lt_or_gt_of_ne hij with hij' | hij'
      · exact h.upper_fixed i j hij'
      · rw [reverse_transvection i j hij]
        exact fixed_mul (fixed_mul hr (h.upper_fixed i.rev j.rev (by simpa using hij'))) hr
  · intro a b ha hb
    exact fixed_mul ha hb

/-- A nonzero empty-support vector forces an irreducible module to be a line. -/
theorem LocalHighestVector.finrank_eq_one_of_empty
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ] {v : V}
    (h : LocalHighestVector ρ ∅ v) (hv : v ≠ 0) : Module.finrank (ZMod 2) V = 1 := by
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span (ZMod 2) {v}
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, h.fixed_of_empty g]
        exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩ }
  have hvW : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (by
    intro hW
    have : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      change v ∈ (⊥ : Subrepresentation ρ)
      rw [← hW]
      exact hvW
    exact hv (by simpa using this))
  have hs : Submodule.span (ZMod 2) {v} = (⊤ : Submodule (ZMod 2) V) :=
    congrArg Subrepresentation.toSubmodule hW
  have hf := finrank_span_singleton (K := ZMod 2) hv
  rw [hs] at hf
  simpa using hf

end Representation.SL5TenDimensional.Classification
