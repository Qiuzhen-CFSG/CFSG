module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverHyperplanes.Coordinates
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases

/-!
# Centers and axes of transvections on the S₆ augmentation core

A binary common displacement line forces a transposition subgroup. Its center
is the actual span of the weight-two vector, and its axis is the hyperplane
where the two corresponding coordinates agree. A permutation moving this
hyperplane only within that center is identity or the transposition.

The proof uses the coordinate tests, then transports the standard pair (0,1)
by a permutation of the six letters. No irreducibility or symplectic-model
identification is used.

Source: Aschbacher–Smith, 13.8.7, printed p.949, last two paragraphs.
-/

@[expose] public section
open BinaryPermutation Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes

def center (i j : Six) : Submodule (ZMod 2) Core := Submodule.span (ZMod 2) {pairCore i j}
def axis (i j : Six) : Submodule (ZMod 2) Core := (act (Equiv.swap i j) - LinearMap.id).ker

lemma mem_span_binary {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a x : M) :
    x ∈ Submodule.span (ZMod 2) {a} ↔ x = 0 ∨ x = a := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    fin_cases c
    · exact Or.inl (zero_smul (ZMod 2) a)
    · exact Or.inr (one_smul (ZMod 2) a)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

lemma act_pair (g : Perm) (i j : Six) :
    act g (pairCore i j) = pairCore (g i) (g j) := by
  apply Subtype.ext
  funext k
  simp [act, coreRepresentation, representation, pairCore, pair, Pi.single_apply,
    Equiv.symm_apply_eq]

lemma swap_displacement (i j : Six) (x : Core) :
    act (Equiv.swap i j) x - x = (x.val j - x.val i) • pairCore i j := by
  apply Subtype.ext
  funext k
  change x.val (Equiv.swap i j k) - x.val k =
    (x.val j - x.val i) * (pair i j k)
  by_cases hij : i = j
  · subst j
    simp
  by_cases hki : k = i
  · subst k
    simp [pair, hij]
  by_cases hkj : k = j
  · subst k
    simp [pair, Ne.symm hij, sub_eq_add_neg, CharTwo.neg_eq]
    exact add_comm _ _
  · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, pair, hki, hkj]

lemma mem_axis (i j : Six) (x : Core) : x ∈ axis i j ↔ x.val i = x.val j := by
  change act (Equiv.swap i j) x - x = 0 ↔ _
  constructor
  · intro h
    have he := congrArg (fun v : Core => v.val i) h
    change x.val (Equiv.swap i j i) - x.val i = 0 at he
    simpa using (sub_eq_zero.mp he).symm
  · intro h
    rw [swap_displacement, h, sub_self, zero_smul]

lemma pairCore_ne_zero (i j : Six) (hij : i ≠ j) : pairCore i j ≠ 0 := by
  intro h
  have he := congrArg (fun v : Core => v.val i) h
  simp [pairCore, pair, hij] at he

lemma center_finrank (i j : Six) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (center i j) = 1 :=
  finrank_span_singleton (pairCore_ne_zero i j hij)

lemma exists_third (i j : Six) : ∃ k : Six, k ≠ i ∧ k ≠ j := by
  revert i j
  decide

lemma pair_moved (i j : Six) (hij : i ≠ j) :
    ∃ x : Core, act (Equiv.swap i j) x - x = pairCore i j := by
  obtain ⟨k, hki, hkj⟩ := exists_third i j
  refine ⟨pairCore j k, ?_⟩
  rw [swap_displacement]
  simp [pairCore, pair, hij, Ne.symm hki, Ne.symm hkj]

lemma center_eq_range (i j : Six) (hij : i ≠ j) :
    (act (Equiv.swap i j) - LinearMap.id).range = center i j := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change act (Equiv.swap i j) x - x ∈ center i j
    rw [swap_displacement]
    exact (center i j).smul_mem _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact pair_moved i j hij

lemma axis_finrank (i j : Six) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (axis i j) = 4 := by
  have hd := (act (Equiv.swap i j) - LinearMap.id).finrank_range_add_finrank_ker
  rw [center_eq_range i j hij, center_finrank i j hij, finrank_core] at hd
  change 1 + Module.finrank (ZMod 2) (axis i j) = 5 at hd
  omega

lemma exists_marking (i j : Six) (hij : i ≠ j) :
    ∃ e : Perm, e 0 = i ∧ e 1 = j := by
  let f : Perm := Equiv.swap 0 i
  have hfi : f 1 ≠ i := by
    have h0 : f 0 = i := Equiv.swap_apply_left _ _
    rw [← h0]
    exact f.injective.ne (by decide)
  refine ⟨Equiv.swap (f 1) j * f, ?_, ?_⟩
  · change Equiv.swap (f 1) j (f 0) = i
    rw [show f 0 = i from Equiv.swap_apply_left _ _]
    exact Equiv.swap_apply_of_ne_of_ne hfi.symm hij
  · exact Equiv.swap_apply_left _ _

lemma act_mul (g h : Perm) (x : Core) : act (g * h) x = act g (act h x) := by
  exact LinearMap.congr_fun (act.map_mul g h) x

lemma fixed_hyperplane_test (i j : Six) (hij : i ≠ j) (s : Perm)
    (hs : ∀ x ∈ axis i j, act s x - x ∈ center i j) :
    s = 1 ∨ s = Equiv.swap i j := by
  obtain ⟨e, he0, he1⟩ := exists_marking i j hij
  let g := e⁻¹ * s * e
  have hg : g = 1 ∨ g = Equiv.swap 0 1 := by
    apply axis_pair_test
    intro k l hk0 hk1 hl0 hl1
    let x := pairCore k l
    have hx : act e x ∈ axis i j := by
      rw [mem_axis, act_pair]
      have hkI : e k ≠ i := by rw [← he0]; exact e.injective.ne hk0
      have hkJ : e k ≠ j := by rw [← he1]; exact e.injective.ne hk1
      have hlI : e l ≠ i := by rw [← he0]; exact e.injective.ne hl0
      have hlJ : e l ≠ j := by rw [← he1]; exact e.injective.ne hl1
      simp [pairCore, pair, Ne.symm hkI, Ne.symm hkJ, Ne.symm hlI, Ne.symm hlJ]
    have hd := (mem_span_binary _ _).mp (hs (act e x) hx)
    have heq : act e⁻¹ (act s (act e x) - act e x) = act g x - x := by
      rw [map_sub, ← act_mul, ← act_mul, ← act_mul]
      simp [g]
    rcases hd with hd | hd
    · left
      have hh := congrArg (act e⁻¹) hd
      simpa only [heq, map_zero] using hh
    · right
      have hh := congrArg (act e⁻¹) hd
      rw [heq] at hh
      simpa [act_pair, ← he0, ← he1, x] using hh
  have hconj : s = e * g * e⁻¹ := by simp [g, mul_assoc]
  rcases hg with hg | hg
  · left
    simpa [hg] using hconj
  · right
    simpa [hg, ← Equiv.swap_apply_apply, he0, he1] using hconj

lemma fixed_hyperplane_mem_zpowers (i j : Six) (hij : i ≠ j) (s : Perm)
    (hs : ∀ x ∈ axis i j, act s x - x ∈ center i j) :
    s ∈ zpowers (Equiv.swap i j) := by
  rcases fixed_hyperplane_test i j hij s hs with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

lemma common_center_group (D : Subgroup Perm) (hD : D ≠ ⊥)
    (A : Submodule (ZMod 2) Core) (hA : Module.finrank (ZMod 2) A = 1)
    (hd : ∀ g ∈ D, ∀ x : Core, act g x - x ∈ A) :
    ∃ i j : Six, i ≠ j ∧ A = center i j ∧ D = zpowers (Equiv.swap i j) := by
  obtain ⟨a, ha, hgen⟩ := (finrank_eq_one_iff').mp hA
  have hspan' : A = Submodule.span (ZMod 2) {a.val} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hc⟩ := hgen ⟨x, hx⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr a.property)
  classical
  have hex : ∃ g ∈ D, g ≠ 1 := by
    by_contra h
    apply hD
    apply le_bot_iff.mp
    intro g hg
    apply mem_bot.mpr
    by_contra hne
    exact h ⟨g, hg, hne⟩
  obtain ⟨g, hg, hgne⟩ := hex
  have hgclass := pair_displacement_test g (by
    intro i j
    have hi := (mem_span_binary a.val _).mp (hspan' ▸ hd g hg (pairCore 0 i))
    have hj := (mem_span_binary a.val _).mp (hspan' ▸ hd g hg (pairCore 0 j))
    rcases hi with hi | hi
    · exact Or.inl hi
    rcases hj with hj | hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (hi.trans hj.symm)))
  obtain ⟨i, j, hij, rfl⟩ := hgclass.resolve_left hgne
  have hle : center i j ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ rfl
    obtain ⟨x, hx⟩ := pair_moved i j hij
    exact hx ▸ hd _ hg x
  have hAc : A = center i j := (Submodule.eq_of_le_of_finrank_eq hle
    ((center_finrank i j hij).trans hA.symm)).symm
  refine ⟨i, j, hij, hAc, le_antisymm ?_ (zpowers_le.mpr hg)⟩
  intro s hs
  exact fixed_hyperplane_mem_zpowers i j hij s (fun x _ => hAc ▸ hd s hs x)

lemma common_center_card_two (D : Subgroup Perm) (hD : D ≠ ⊥)
    (A : Submodule (ZMod 2) Core) (hA : Module.finrank (ZMod 2) A = 1)
    (hd : ∀ g ∈ D, ∀ x : Core, act g x - x ∈ A) : Nat.card D = 2 := by
  obtain ⟨i, j, hij, _, rfl⟩ := common_center_group D hD A hA hd
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
  apply orderOf_eq_prime
  · simp [pow_two]
  · simpa using hij

/-- The actual fixed subspace of a permutation subgroup on the core. -/
def fixed (D : Subgroup Perm) : Submodule (ZMod 2) Core where
  carrier := {x | ∀ g ∈ D, act g x = x}
  zero_mem' := by intro g _; exact map_zero _
  add_mem' := by intro x y hx hy g hg; rw [map_add, hx g hg, hy g hg]
  smul_mem' := by intro c x hx g hg; rw [map_smul, hx g hg]

lemma mem_swap_zpowers (i j : Six) (hij : i ≠ j) (s : Perm) :
    s ∈ zpowers (Equiv.swap i j) ↔ s = 1 ∨ s = Equiv.swap i j := by
  rw [mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime (p := 2) (by simp [pow_two]) (by simpa using hij)]
  simp [Nat.le_one_iff_eq_zero_or_eq_one, eq_comm]

lemma fixed_swap (i j : Six) (hij : i ≠ j) :
    fixed (zpowers (Equiv.swap i j)) = axis i j := by
  ext x
  change (∀ g ∈ zpowers (Equiv.swap i j), act g x = x) ↔
    act (Equiv.swap i j) x - x = 0
  constructor
  · intro h
    exact sub_eq_zero.mpr (h _ (mem_zpowers _))
  · intro h g hg
    rcases (mem_swap_zpowers i j hij g).mp hg with rfl | rfl
    · simp
    · exact sub_eq_zero.mp h

/-- A larger subgroup moving the fixed hyperplane only within the common
center is the original transposition subgroup. -/
lemma subgroup_comparison (B W : Subgroup Perm) (hBW : B ≤ W) (hB : B ≠ ⊥)
    (A : Submodule (ZMod 2) Core) (hA : Module.finrank (ZMod 2) A = 1)
    (hBdisp : ∀ b ∈ B, ∀ x : Core, act b x - x ∈ A)
    (hWdisp : ∀ w ∈ W, ∀ x ∈ fixed B, act w x - x ∈ A) : W = B := by
  obtain ⟨i, j, hij, rfl, rfl⟩ := common_center_group B hB A hA hBdisp
  apply le_antisymm _ hBW
  intro w hw
  apply fixed_hyperplane_mem_zpowers i j hij w
  intro x hx
  exact hWdisp w hw x ((fixed_swap i j hij).symm ▸ hx)

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes

end
