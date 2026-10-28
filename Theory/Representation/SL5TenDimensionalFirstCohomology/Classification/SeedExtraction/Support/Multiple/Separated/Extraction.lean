module
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Operators
/-!
# Transvection extraction on permutation translates

Inactive simple exchanges fix a local highest vector, hence so do words in
those exchanges. Conjugating a transvection through a permutation translate
and such an inactive word either gives an upper transvection, which kills the
vector after subtracting the identity, or an active lower transvection, whose
difference is an exchange translate. These two rules certify finite action
tables without any assumption about torus weights.

A triangular family of extracting endomorphisms proves linear independence.
The separated-support certificates use this criterion for eleven vectors.

Source application: Aschbacher--Smith, *The Classification of Quasithin
Groups*, I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section
namespace Representation.SL5TenDimensional.Classification.Separated

def swapWord (w : List (Fin 4)) : Group := (w.map simpleSwap).prod

def rootElement (a b : Fin 5) : Group :=
  if hab : a ≠ b then Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2) else 1

def difference {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (t : Group) : V →ₗ[ZMod 2] V :=
  ρ t - LinearMap.id

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

lemma fixed_word {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (w : List (Fin 4)) (hw : ∀ i ∈ w, i ∉ J) :
    ρ (swapWord w) v = v := by
  induction w with
  | nil => simp [swapWord]
  | cons i w ih =>
    change ρ (simpleSwap i * swapWord w) v = v
    rw [map_mul]
    change ρ (simpleSwap i) (ρ (swapWord w) v) = v
    rw [ih (fun j hj => hw j (by simp [hj]))]
    exact h.inactive_fixed i (hw i (by simp))

lemma apply_mul (ρ : Representation (ZMod 2) Group V) (a b : Group) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl

lemma difference_zero {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (t a : Group) (q : List (Fin 4))
    (hq : ∀ i ∈ q, i ∉ J) (r s : Fin 5) (hrs : r < s)
    (he : t * a * swapWord q = a * swapWord q * rootElement r s) :
    difference ρ t (ρ a v) = 0 := by
  have hu : ρ (rootElement r s) v = v := by
    simpa [rootElement, ne_of_lt hrs] using h.upper_fixed r s hrs
  have hh := congrArg (fun g => ρ g v) he
  simp only [apply_mul, fixed_word h q hq, hu] at hh
  change ρ t (ρ a v) - ρ a v = 0
  exact sub_eq_zero.mpr hh

lemma lower_apply {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (i : Fin 4) (hi : i ∈ J) :
    ρ (simpleLower i) v = v + ρ (simpleSwap i) v := by
  have binary (x : V) : x + x = 0 := by
    have hh : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh
  have hh := congrArg (fun x => x + ρ (simpleLower i) v) (h.active_relation i hi)
  simpa only [add_assoc, binary, add_zero, zero_add] using hh.symm

lemma difference_step {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (t a b : Group) (q r : List (Fin 4))
    (hq : ∀ i ∈ q, i ∉ J) (hr : ∀ i ∈ r, i ∉ J)
    (i : Fin 4) (hi : i ∈ J)
    (he : t * a * swapWord q = a * swapWord q * simpleLower i)
    (hf : a * swapWord q * simpleSwap i = b * swapWord r) :
    difference ρ t (ρ a v) = ρ b v := by
  have hh := congrArg (fun g => ρ g v) he
  have hk := congrArg (fun g => ρ g v) hf
  simp only [apply_mul, fixed_word h r hr] at hk
  simp only [apply_mul, fixed_word h q hq, lower_apply h i hi, map_add, hk] at hh
  change ρ t (ρ a v) - ρ a v = ρ b v
  rw [hh, add_sub_cancel_left]

lemma translate_ne_zero (ρ : Representation (ZMod 2) Group V) (a : Group)
    {v : V} (hv : v ≠ 0) : ρ a v ≠ 0 := by
  intro he
  have hh := congrArg (ρ a⁻¹) he
  rw [← apply_mul, inv_mul_cancel, map_one] at hh
  exact hv (by simpa using hh)

/-- Linear endomorphisms separating each vector from its predecessors certify independence. -/
theorem linearIndependent_of_triangular {n : ℕ} (f : Fin n → V)
    (D : Fin n → V →ₗ[ZMod 2] V)
    (hzero : ∀ i j, j < i → D i (f j) = 0)
    (hne : ∀ i, D i (f i) ≠ 0) : LinearIndependent (ZMod 2) f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := ⟨j, by simp [s, hj]⟩
  let i := s.max' hs
  have hi : c i ≠ 0 := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have he := congrArg (D i) hc
  simp only [map_sum, map_smul, map_zero] at he
  have hh : ∑ k, c k • D i (f k) = c i • D i (f i) := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases hlt : k < i
      · rw [hzero i k hlt, smul_zero]
      · have hk : c k = 0 := by
          by_contra hk
          have hle : k ≤ i := s.le_max' k (by simp [s, hk])
          exact hki (le_antisymm hle (le_of_not_gt hlt))
        rw [hk, zero_smul]
    · simp
  rw [hh] at he
  exact (smul_ne_zero hi (hne i)) he
end Representation.SL5TenDimensional.Classification.Separated
