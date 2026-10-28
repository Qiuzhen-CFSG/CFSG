module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.ResidualUpper.Elementary

/-!
# Elementary generation of an actual binary minimal parabolic

Eliminate columns from left to right, retaining every earlier basis vector.
The flag condition makes each column upper triangular except at the omitted
cut, where its last two possible coefficients cannot both vanish. An upper
simple root supplies a pivot, and the one permitted lower simple root clears
the exceptional coefficient. Upper shears then clear the column. Each shear
is a product of upper roots, by induction in the earlier coordinate span.

This proves generation of the literal flag stabilizer in every dimension;
there is no finite group enumeration or assumed Bruhat decomposition.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.OrderedResidualConjugators.ResidualUpper
open OuterCyclic InvariantNodeActions

private noncomputable def initialSpace {m : ℕ} (b : Basis m) (k : ℕ) :
    Submodule (ZMod 2) (Space (m + 1)) :=
  Submodule.span (ZMod 2) (b '' {r : Fin (m + 1) | r.val < k})

private theorem mem_initialSpace {m : ℕ} (b : Basis m) (k : ℕ) (v : Space (m + 1)) :
    v ∈ initialSpace b k ↔ ∀ r : Fin (m + 1), k ≤ r.val → b.repr v r = 0 := by
  rw [initialSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h r hr
    by_contra hv
    exact (Nat.not_lt_of_ge hr) (h r hv)
  · intro h r hr
    by_contra hv
    exact hr (h r (Nat.le_of_not_gt hv))

private theorem root_eq_transvection {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) :
    root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
  apply b.ext'
  intro j
  rw [root_basis]
  change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
  by_cases h : j = s <;> simp [h, Module.Basis.coord_apply]

private theorem upper_shear_mem {m : ℕ} (b : Basis m) (s : Fin (m + 1))
    (w : Space (m + 1)) (hw : w ∈ initialSpace b s.val) :
    ∃ hf : b.coord s w = 0, transvection w (b.coord s) hf ∈ upperRoots b := by
  classical
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨r, hr, rfl⟩ := hw
    have hrs : r ≠ s := by intro he; subst r; exact (Nat.lt_irrefl _) hr
    refine ⟨by simp [hrs], ?_⟩
    rw [← root_eq_transvection b r s hrs]
    exact subset_closure ⟨r, s, hrs, hr, rfl⟩
  | zero =>
    refine ⟨map_zero _, ?_⟩
    have he : transvection 0 (b.coord s) (map_zero _) = 1 := by ext v; simp [transvection]
    rw [he]
    exact (upperRoots b).one_mem
  | add x y hx hy ihx ihy =>
    obtain ⟨hfx, hx⟩ := ihx
    obtain ⟨hfy, hy⟩ := ihy
    refine ⟨by rw [map_add, hfx, hfy, add_zero], ?_⟩
    have he : transvection (x + y) (b.coord s) (by rw [map_add, hfx, hfy, add_zero]) =
        transvection x (b.coord s) hfx * transvection y (b.coord s) hfy := by
      apply LinearEquiv.ext
      intro v
      change v + b.coord s v • (x + y) =
        (v + b.coord s v • y) + b.coord s (v + b.coord s v • y) • x
      rw [map_add, map_smul, hfy, smul_zero, add_zero, smul_add]
      abel
    rw [he]
    exact (upperRoots b).mul_mem hx hy
  | smul a x hx ih =>
    have ha : a = 0 ∨ a = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases ha with rfl | rfl
    · simp only [zero_smul]
      refine ⟨map_zero _, ?_⟩
      have he : transvection 0 (b.coord s) (map_zero _) = 1 := by ext v; simp [transvection]
      rw [he]
      exact (upperRoots b).one_mem
    · simpa only [one_smul] using ih

private theorem parabolic_column_support {m : ℕ} (b : Basis m) (i : Fin m)
    (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (k r : Fin (m + 1)) (hr : (if k.val = i.val then k.val + 1 else k.val) < r.val) :
    b.repr (g (b k)) r = 0 := by
  let l := if k.val = i.val then k.val + 1 else k.val
  have hl : l < m := by have := r.isLt; dsimp [l]; omega
  let j : Fin m := ⟨l, hl⟩
  have hji : j ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    change l = i.val at hh
    dsimp [l] at hh
    split_ifs at hh <;> omega
  have hk : b k ∈ cutSpace b j := (basis_mem_cutSpace b j k).mpr (by
    change k.val ≤ l
    dsimp [l]
    split_ifs <;> omega)
  have hv := (mem_cutStabilizer_maps b {i}ᶜ g).mp hg j hji (b k) hk
  have hmem : g (b k) ∈ initialSpace b (l + 1) := by
    convert hv using 1
    unfold initialSpace cutSpace
    congr 2
    ext t
    change (t.val < l + 1) ↔ (t.val ≤ l)
    omega
  exact (mem_initialSpace b (l + 1) _).mp hmem r (by omega)

private theorem fixed_on_initialSpace {m : ℕ} (b : Basis m) (k : ℕ)
    (g : LinearGroup (m + 1)) (hfix : ∀ j : Fin (m + 1), j.val < k → g (b j) = b j)
    (v : Space (m + 1)) (hv : v ∈ initialSpace b k) : g v = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, hj, rfl⟩ := hv
    exact hfix j hj
  | zero => exact g.map_zero
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a x hx ih => simp only [map_smul, ih]

private theorem column_not_in_initialSpace {m : ℕ} (b : Basis m) (k : Fin (m + 1))
    (g : LinearGroup (m + 1)) (hfix : ∀ j : Fin (m + 1), j.val < k.val → g (b j) = b j) :
    g (b k) ∉ initialSpace b k.val := by
  intro hv
  have he := g.injective (fixed_on_initialSpace b k.val g hfix (g (b k)) hv)
  have hh : b k ∈ initialSpace b k.val := he ▸ hv
  have hc := (mem_initialSpace b k.val (b k)).mp hh k le_rfl
  simp at hc

private theorem root_repr {m : ℕ} (b : Basis m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (v : Space (m + 1)) (t : Fin (m + 1)) :
    b.repr (root b r s hrs v) t = b.repr v t + if t = r then b.repr v s else 0 := by
  rw [root_eq_transvection]
  change b.repr (v + b.coord s v • b r) t = _
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

private theorem column_pivot {m : ℕ} (b : Basis m) (i : Fin m)
    (k : Fin (m + 1)) (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (hfix : ∀ j : Fin (m + 1), j.val < k.val → g (b j) = b j) :
    ∃ t ∈ elementaryParabolic b i,
      (∀ j : Fin (m + 1), j.val < k.val → t (b j) = b j) ∧
      b.repr ((t * g) (b k)) k = 1 := by
  have hn := column_not_in_initialSpace b k g hfix
  by_cases hdiag : b.repr (g (b k)) k = 0
  · have hki : k.val = i.val := by
      by_contra hne
      apply hn
      apply (mem_initialSpace b k.val _).mpr
      intro r hr
      by_cases he : r = k
      · simpa only [he] using hdiag
      · exact parabolic_column_support b i g hg k r (by
          have : r.val ≠ k.val := fun h => he (Fin.ext h)
          simp only [hne, ↓reduceIte]
          omega)
    have hk : k = i.castSucc := Fin.ext hki
    have hp : b.repr (g (b k)) i.succ = 1 := by
      apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
      intro hz
      apply hn
      apply (mem_initialSpace b k.val _).mpr
      intro r hr
      by_cases he : r = k
      · simpa only [he] using hdiag
      · by_cases hs : r = i.succ
        · simpa only [hs] using hz
        · apply parabolic_column_support b i g hg k r
          simp only [hki, ↓reduceIte]
          have hrk : r.val ≠ k.val := fun h => he (Fin.ext h)
          have hrs : r.val ≠ i.val + 1 := fun h => hs (Fin.ext h)
          omega
    have hks : k ≠ i.succ := by rw [hk]; simp [Fin.ext_iff]
    let t := root b k i.succ hks
    refine ⟨t, subset_closure ⟨k, i.succ, hks, Or.inl (by simp [hki]), rfl⟩, ?_, ?_⟩
    · intro j hj
      have hjs : j ≠ i.succ := by intro he; have := congrArg Fin.val he; simp at this; omega
      simp only [t, root_basis, hjs, ↓reduceIte]
    · change b.repr (root b k i.succ hks (g (b k))) k = 1
      rw [root_repr, if_pos rfl, hdiag, hp, zero_add]
  · refine ⟨1, (elementaryParabolic b i).one_mem, fun _ _ => rfl, ?_⟩
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hdiag

private theorem column_clear_lower {m : ℕ} (b : Basis m) (i : Fin m)
    (k : Fin (m + 1)) (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (hdiag : b.repr (g (b k)) k = 1) :
    ∃ t ∈ elementaryParabolic b i,
      (∀ j : Fin (m + 1), j.val < k.val → t (b j) = b j) ∧
      b.repr ((t * g) (b k)) k = 1 ∧
      (∀ r : Fin (m + 1), k.val < r.val → b.repr ((t * g) (b k)) r = 0) := by
  by_cases hki : k.val = i.val
  · by_cases hlow : b.repr (g (b k)) i.succ = 0
    · refine ⟨1, (elementaryParabolic b i).one_mem, fun _ _ => rfl, hdiag, ?_⟩
      intro r hr
      by_cases he : r = i.succ
      · simpa only [one_mul, he] using hlow
      · apply parabolic_column_support b i g hg k r
        simp only [hki, ↓reduceIte]
        have hne : r.val ≠ i.val + 1 := fun h => he (Fin.ext h)
        omega
    · have hlow1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hlow
      have hk : k = i.castSucc := Fin.ext hki
      have hsk : i.succ ≠ k := by rw [hk]; simp [Fin.ext_iff]
      let t := root b i.succ k hsk
      refine ⟨t, subset_closure ⟨i.succ, k, hsk, Or.inr ⟨rfl, hk⟩, rfl⟩, ?_, ?_, ?_⟩
      · intro j hj
        have hjk : j ≠ k := by intro he; subst j; omega
        simp only [t, root_basis, hjk, ↓reduceIte]
      · change b.repr (root b i.succ k hsk (g (b k))) k = 1
        rw [root_repr, if_neg hsk.symm, add_zero, hdiag]
      · intro r hr
        change b.repr (root b i.succ k hsk (g (b k))) r = 0
        rw [root_repr]
        by_cases he : r = i.succ
        · rw [if_pos he, he, hlow1, hdiag]
          decide
        · rw [if_neg he, add_zero]
          apply parabolic_column_support b i g hg k r
          simp only [hki, ↓reduceIte]
          have hne : r.val ≠ i.val + 1 := fun h => he (Fin.ext h)
          omega
  · refine ⟨1, (elementaryParabolic b i).one_mem, fun _ _ => rfl, hdiag, ?_⟩
    intro r hr
    exact parabolic_column_support b i g hg k r (by simpa only [hki, ↓reduceIte] using hr)

private theorem upper_column_clear {m : ℕ} (b : Basis m) (k : Fin (m + 1))
    (v : Space (m + 1)) (hdiag : b.repr v k = 1)
    (hzero : ∀ r : Fin (m + 1), k.val < r.val → b.repr v r = 0) :
    ∃ t ∈ upperRoots b,
      (∀ j : Fin (m + 1), j.val < k.val → t (b j) = b j) ∧ t v = b k := by
  let w := v + b k
  have hw : w ∈ initialSpace b k.val := by
    apply (mem_initialSpace b k.val w).mpr
    intro r hr
    change b.repr (v + b k) r = 0
    simp only [map_add, Finsupp.add_apply]
    by_cases he : r = k
    · rw [he, hdiag]
      simp only [Module.Basis.repr_self, Finsupp.single_apply]
      decide
    · have hrk : k.val < r.val := by
        have : r.val ≠ k.val := fun h => he (Fin.ext h)
        omega
      rw [hzero r hrk]
      simp [he]
  obtain ⟨hf, ht⟩ := upper_shear_mem b k w hw
  refine ⟨transvection w (b.coord k) hf, ht, ?_, ?_⟩
  · intro j hj
    have hjk : j ≠ k := by intro he; subst j; omega
    change b j + b.coord k (b j) • w = b j
    simp [hjk]
  · change v + b.repr v k • (v + b k) = b k
    rw [hdiag, one_smul]
    ext j
    exact CharTwo.add_cancel_left _ _

private theorem clean_step {m : ℕ} (b : Basis m) (i : Fin m)
    (k : Fin (m + 1)) (g : LinearGroup (m + 1)) (hg : g ∈ minimalParabolic b i)
    (hfix : ∀ j : Fin (m + 1), j.val < k.val → g (b j) = b j) :
    ∃ t ∈ elementaryParabolic b i,
      ∀ j : Fin (m + 1), j.val < k.val + 1 → (t * g) (b j) = b j := by
  obtain ⟨t, ht, htfix, htdiag⟩ := column_pivot b i k g hg hfix
  have htg : t * g ∈ minimalParabolic b i :=
    (minimalParabolic b i).mul_mem (elementaryParabolic_le b i ht) hg
  obtain ⟨l, hl, hlfix, hldiag, hlzero⟩ := column_clear_lower b i k (t * g) htg htdiag
  obtain ⟨u, hu, hufix, huval⟩ := upper_column_clear b k ((l * (t * g)) (b k)) hldiag hlzero
  refine ⟨u * l * t, (elementaryParabolic b i).mul_mem
    ((elementaryParabolic b i).mul_mem (upperRoots_le_elementaryParabolic b i hu) hl) ht, ?_⟩
  intro j hj
  by_cases he : j = k
  · subst j
    exact huval
  · have hjk : j.val < k.val := by
      have : j.val ≠ k.val := fun h => he (Fin.ext h)
      omega
    change u (l (t (g (b j)))) = b j
    rw [hfix j hjk, htfix j hjk, hlfix j hjk, hufix j hjk]

/-- Gaussian elimination uses exactly the upper roots and the one allowed
lower simple root of the literal partial-flag stabilizer. -/
theorem minimalParabolic_le_elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    minimalParabolic b i ≤ elementaryParabolic b i := by
  intro g hg
  have hc : ∀ n : ℕ, n ≤ m + 1 → ∃ h ∈ elementaryParabolic b i,
      ∀ j : Fin (m + 1), j.val < n → (h * g) (b j) = b j := by
    intro n hn
    induction n with
    | zero => exact ⟨1, (elementaryParabolic b i).one_mem, fun j hj => by omega⟩
    | succ n ih =>
      obtain ⟨h, hh, hfix⟩ := ih (by omega)
      let k : Fin (m + 1) := ⟨n, by omega⟩
      have hhg : h * g ∈ minimalParabolic b i :=
        (minimalParabolic b i).mul_mem (elementaryParabolic_le b i hh) hg
      obtain ⟨t, ht, htf⟩ := clean_step b i k (h * g) hhg hfix
      refine ⟨t * h, (elementaryParabolic b i).mul_mem ht hh, ?_⟩
      intro j hj
      exact htf j hj
  obtain ⟨h, hh, hfix⟩ := hc (m + 1) le_rfl
  have he : h * g = 1 := by
    apply b.ext'
    intro j
    exact hfix j j.isLt
  have hg' : g = h⁻¹ := by
    calc g = h⁻¹ * (h * g) := (inv_mul_cancel_left h g).symm
         _ = h⁻¹ := by rw [he, mul_one]
  rw [hg']
  exact (elementaryParabolic b i).inv_mem hh

theorem minimalParabolic_eq_elementaryParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    minimalParabolic b i = elementaryParabolic b i :=
  le_antisymm (minimalParabolic_le_elementaryParabolic b i) (elementaryParabolic_le b i)

end BinaryLinear.OrderedResidualConjugators.ResidualUpper
