module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The irreducible two-core of the four-block stabilizer in S₈

The two double-transposition groups form a normal subgroup K = V₄ × V₄.
A commutator with an internal transposition isolates a nonzero block factor;
internal conjugation and the block interchange then generate all of K.
Thus every nonzero subgroup of K normalized by the block stabilizer equals K.

To identify the entire two-core P, the normal subgroup K of the two-group P
meets Z(P) nontrivially. Irreducibility gives K ≤ Z(P), while the explicit
permutation centralizer calculation gives C_S₈(K) ≤ K. Hence P = K.
All finite checks below are kernel-checked equalities of point permutations.
The construction and centralizer argument adapt the private proofs in
`A6ShadowTwoLocals.FourStructure`, preserving that module's public boundary.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the irreducibility assertion in the last paragraph
of the proof of 15.3.32, printed p.1133 (PDF p.1150).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
open Subgroup Equiv A6ShadowTwoLocals

/-- The identity and the three double transpositions on `{0,1,2,3}`. -/
def leftKlein : Fin 4 → S8 :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

/-- The identity and the three double transpositions on `{4,5,6,7}`. -/
def rightKlein : Fin 4 → S8 :=
  ![1, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7, swap 4 7 * swap 5 6]

/-- The product of a double transposition on each of the disjoint blocks. -/
def kleinPerm (a b : Fin 4) : S8 := leftKlein a * rightKlein b

private theorem klein_mul_table : ∀ a b c d : Fin 4,
    ∃ e f : Fin 4, kleinPerm a b * kleinPerm c d = kleinPerm e f := by decide

private theorem klein_square : ∀ a b : Fin 4, kleinPerm a b * kleinPerm a b = 1 := by decide

/-- The embedded product of the two block Klein-four groups. -/
def kleinGroup : Subgroup S8 where
  carrier := {g | ∃ a b, g = kleinPerm a b}
  one_mem' := ⟨0, 0, rfl⟩
  mul_mem' := by
    rintro g h ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact klein_mul_table a b c d
  inv_mem' := by
    rintro g ⟨a, b, rfl⟩
    exact ⟨a, b, inv_eq_of_mul_eq_one_right (klein_square a b)⟩

private theorem klein_le_four : kleinGroup ≤ fourStabilizer := by
  have ht : ∀ a b : Fin 4, kleinPerm a b ∈ fourStabilizer := by decide
  rintro g ⟨a, b, rfl⟩
  exact ht a b

private theorem klein_pgroup : IsPGroup 2 kleinGroup := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨a, b, he⟩ := g.property
  change (g : S8) ^ (2 ^ 1) = 1
  simpa only [he, pow_one, pow_two] using klein_square a b

private theorem double_swap_mem (a b c d : Fin 8)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : a.val / 4 = b.val / 4) (h₂ : a.val / 4 = c.val / 4)
    (h₃ : a.val / 4 = d.val / 4) : swap a b * swap c d ∈ kleinGroup := by
  have ht : ∀ a b c d : Fin 8,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      a.val / 4 = b.val / 4 → a.val / 4 = c.val / 4 → a.val / 4 = d.val / 4 →
      ∃ e f : Fin 4, swap a b * swap c d = kleinPerm e f := by
    decide
  exact ht a b c d hab hac had hbc hbd hcd h₁ h₂ h₃

private theorem conj_double_swap_mem (g : S8) (hg : g ∈ fourStabilizer)
    (a b c d : Fin 8)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : a.val / 4 = b.val / 4) (h₂ : a.val / 4 = c.val / 4)
    (h₃ : a.val / 4 = d.val / 4) :
    g * (swap a b * swap c d) * g⁻¹ ∈ kleinGroup := by
  have he : g * (swap a b * swap c d) * g⁻¹ =
      swap (g a) (g b) * swap (g c) (g d) := by
    calc
      _ = (g * swap a b * g⁻¹) * (g * swap c d * g⁻¹) := by simp [mul_assoc]
      _ = _ := by
        rw [Equiv.mul_swap_eq_swap_mul g a b, Equiv.mul_swap_eq_swap_mul g c d]
        simp
  rw [he]
  exact double_swap_mem _ _ _ _ (g.injective.ne hab) (g.injective.ne hac)
    (g.injective.ne had) (g.injective.ne hbc) (g.injective.ne hbd)
    (g.injective.ne hcd) ((hg a b).mpr h₁) ((hg a c).mpr h₂) ((hg a d).mpr h₃)

private theorem four_normalizes_klein : fourStabilizer ≤ normalizer (kleinGroup : Set S8) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg n hn
  obtain ⟨a, b, rfl⟩ := hn
  have hl : g * leftKlein a * g⁻¹ ∈ kleinGroup := by
    fin_cases a
    · simp [leftKlein]
    all_goals
      apply conj_double_swap_mem g hg <;> decide
  have hr : g * rightKlein b * g⁻¹ ∈ kleinGroup := by
    fin_cases b
    · simp [rightKlein]
    all_goals
      apply conj_double_swap_mem g hg <;> decide
  simpa only [kleinPerm, mul_assoc, inv_mul_cancel_left] using kleinGroup.mul_mem hl hr

private theorem klein_commute : ∀ a b i : Fin 4,
    leftKlein i * kleinPerm a b = kleinPerm a b * leftKlein i ∧
    rightKlein i * kleinPerm a b = kleinPerm a b * rightKlein i := by decide

private theorem base_images : ∀ a b : Fin 8,
    rightKlein 1 a = a → leftKlein 1 b = b →
    ∃ c d : Fin 4, kleinPerm c d 0 = a ∧ kleinPerm c d 4 = b := by decide

private theorem klein_orbits : ∀ x : Fin 8,
    (∃ i : Fin 4, leftKlein i 0 = x) ∨ (∃ i : Fin 4, rightKlein i 4 = x) := by decide

private theorem klein_centralizer_le : centralizer (kleinGroup : Set S8) ≤ kleinGroup := by
  intro g hg
  have hl (i : Fin 4) (x : Fin 8) : leftKlein i (g x) = g (leftKlein i x) := by
    have hm : leftKlein i ∈ kleinGroup := ⟨i, 0, by simp [kleinPerm, rightKlein]⟩
    exact congrArg (fun q : S8 => q x) (hg _ hm)
  have hr (i : Fin 4) (x : Fin 8) : rightKlein i (g x) = g (rightKlein i x) := by
    have hm : rightKlein i ∈ kleinGroup := ⟨0, i, by simp [kleinPerm, leftKlein]⟩
    exact congrArg (fun q : S8 => q x) (hg _ hm)
  have h0 : rightKlein 1 (g 0) = g 0 := by
    simpa only [show rightKlein 1 0 = 0 from by decide] using hr 1 0
  have h4 : leftKlein 1 (g 4) = g 4 := by
    simpa only [show leftKlein 1 4 = 4 from by decide] using hl 1 4
  obtain ⟨a, b, ha, hb⟩ := base_images (g 0) (g 4) h0 h4
  refine ⟨a, b, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := klein_orbits x
  · calc
      g (leftKlein i 0) = leftKlein i (g 0) := (hl i 0).symm
      _ = leftKlein i (kleinPerm a b 0) := congrArg (leftKlein i) ha.symm
      _ = kleinPerm a b (leftKlein i 0) :=
        congrArg (fun q : S8 => q 0) (klein_commute a b i).1
  · calc
      g (rightKlein i 4) = rightKlein i (g 4) := (hr i 4).symm
      _ = rightKlein i (kleinPerm a b 4) := congrArg (rightKlein i) hb.symm
      _ = kleinPerm a b (rightKlein i 4) :=
        congrArg (fun q : S8 => q 4) (klein_commute a b i).2


private def blockSwap : S8 := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

private def localSwap : Fin 3 → S8 := ![1, swap 0 2, swap 0 3]

private def actor (b : Bool) (i : Fin 3) : S8 :=
  (if b then blockSwap else 1) * localSwap i

private theorem actor_mem : ∀ b i, actor b i ∈ fourStabilizer := by decide

private theorem isolate_left : ∀ a b : Fin 4, a ≠ 0 →
    ∃ i j : Fin 3,
      localSwap j *
        (localSwap i * kleinPerm a b * (localSwap i)⁻¹ * kleinPerm a b) *
          (localSwap j)⁻¹ = leftKlein 1 := by decide

private theorem swap_blocks : ∀ a b : Fin 4,
    blockSwap * kleinPerm a b * blockSwap⁻¹ = kleinPerm b a := by decide

private theorem left_orbit : ∀ a : Fin 4, a ≠ 0 →
    ∃ i : Fin 3, actor false i * leftKlein 1 * (actor false i)⁻¹ = leftKlein a := by decide

private theorem right_orbit : ∀ a : Fin 4, a ≠ 0 →
    ∃ i : Fin 3, actor true i * leftKlein 1 * (actor true i)⁻¹ = rightKlein a := by decide

private theorem left_one_mem (A : Subgroup S8)
    (hN : fourStabilizer ≤ normalizer (A : Set S8))
    {a b : Fin 4} (ha : a ≠ 0) (hx : kleinPerm a b ∈ A) : leftKlein 1 ∈ A := by
  obtain ⟨i, j, he⟩ := isolate_left a b ha
  have hm (i : Fin 3) : localSwap i ∈ fourStabilizer := by
    simpa only [actor, Bool.false_eq_true, ↓reduceIte, one_mul] using actor_mem false i
  rw [← he]
  exact (hN (hm j) _).mp (A.mul_mem ((hN (hm i) _).mp hx) hx)

/-- Every invariant subgroup of the two block Klein groups is zero or the whole group. -/
theorem klein_irreducible (A : Subgroup S8) (hA : A ≤ kleinGroup)
    (hN : fourStabilizer ≤ normalizer (A : Set S8)) : A = ⊥ ∨ A = kleinGroup := by
  classical
  by_cases hz : A = ⊥
  · exact Or.inl hz
  right
  obtain ⟨x, hx, hx1⟩ := (A.bot_or_exists_ne_one).resolve_left hz
  obtain ⟨a, b, rfl⟩ := hA hx
  have h1 : leftKlein 1 ∈ A := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        exact hx1 (by simp [ha, hb, kleinPerm, leftKlein, rightKlein])
      have hy := (hN (show blockSwap ∈ fourStabilizer from by decide) _).mp hx
      rw [swap_blocks] at hy
      exact left_one_mem A hN hb hy
    · exact left_one_mem A hN ha hx
  apply le_antisymm hA
  rintro x ⟨a, b, rfl⟩
  apply A.mul_mem
  · by_cases ha : a = 0
    · simp [ha, leftKlein]
    · obtain ⟨i, hi⟩ := left_orbit a ha
      rw [← hi]
      exact (hN (actor_mem false i) _).mp h1
  · by_cases hb : b = 0
    · simp [hb, rightKlein]
    · obtain ⟨i, hi⟩ := right_orbit b hb
      rw [← hi]
      exact (hN (actor_mem true i) _).mp h1

private theorem klein_ne_bot : kleinGroup ≠ ⊥ := by
  intro h
  have hm : leftKlein 1 ∈ kleinGroup := ⟨1, 0, by simp [kleinPerm, rightKlein]⟩
  rw [h, mem_bot] at hm
  exact (by decide : leftKlein 1 ≠ 1) hm

/-- The embedded two-core is exactly the product of the two double-transposition groups. -/
theorem fourStabilizer_pCoreIn : fourStabilizer.pCoreIn 2 = kleinGroup := by
  let P := fourStabilizer.pCoreIn 2
  have hKP : kleinGroup ≤ P :=
    le_pCoreIn_of_normalizes klein_pgroup klein_le_four four_normalizes_klein
  have hHP : fourStabilizer ≤ normalizer (P : Set S8) :=
    fourStabilizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image fourStabilizer (pCore 2 fourStabilizer))
  let Z := (center P).map P.subtype
  have hHZ : fourStabilizer ≤ normalizer (Z : Set S8) :=
    hHP.trans (normalizer_le_normalizer_characteristic_image P (center P))
  have hn : (kleinGroup.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKP).mpr
      ((pCoreIn_le 2 fourStabilizer).trans four_normalizes_klein)
  let : Nontrivial kleinGroup := (nontrivial_iff_ne_bot _).mpr klein_ne_bot
  let : Nontrivial (kleinGroup.subgroupOf P) :=
    (subgroupOfEquivOfLe hKP).toEquiv.nontrivial
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_pCoreIn 2 fourStabilizer⟩
  obtain ⟨x, hx, hxZ⟩ := exists_nontrivial_center_mem_normal (kleinGroup.subgroupOf P) (p := 2)
  have hne : kleinGroup ⊓ Z ≠ ⊥ := by
    intro he
    have hm : ((x : P) : S8) ∈ kleinGroup ⊓ Z := ⟨x.property, ⟨x, hxZ, rfl⟩⟩
    rw [he, mem_bot] at hm
    exact hx (Subtype.ext (Subtype.ext hm))
  have he : kleinGroup ⊓ Z = kleinGroup :=
    (klein_irreducible _ inf_le_left
      ((le_inf four_normalizes_klein hHZ).trans inf_normalizer_le_normalizer_inf)).resolve_left hne
  have hKZ : kleinGroup ≤ Z := he ▸ inf_le_right
  apply le_antisymm _ hKP
  apply le_trans _ klein_centralizer_le
  intro g hg k hk
  obtain ⟨z, hz, rfl⟩ := hKZ hk
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨g, hg⟩).symm

/-- The four-block stabilizer acts irreducibly on its actual embedded two-core. -/
theorem fourStabilizer_core_irreducible (A : Subgroup S8)
    (hA : A ≤ fourStabilizer.pCoreIn 2)
    (hN : fourStabilizer ≤ normalizer (A : Set S8)) :
    A = ⊥ ∨ A = fourStabilizer.pCoreIn 2 := by
  rw [fourStabilizer_pCoreIn] at hA ⊢
  exact klein_irreducible A hA hN

end Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
