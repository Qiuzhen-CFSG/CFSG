module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.Swapping
public import Theory.ElementaryAbelian.Basic

/-!
# The three marked transvections in the mixed eight-point actor

The even part of the mixed actor is enumerated by the eight products of
three fixed-point-free involutions. These are the products of `(01)(23)`
with the three nonidentity elements of the regular Klein group on `{4,5,6,7}`.
The enumeration is transported through the actual exceptional comparison,
so it describes the original natural linear group, not an unrelated model.
The transvection marking itself is an explicit input owned by NaturalMarking.

Source: Aschbacher–Smith, H.9.3(6), printed pp.391–392 (PDF pp.402–403).
-/

@[expose] public section
namespace BinaryNaturalDual.FourActors.A2Module
open Equiv Subgroup BinaryLinear.OuterCyclic

/-- The three fixed-point-free involutions of the mixed even actor. -/
def axisPermutation : Fin 3 → S :=
  ![swap 0 1 * swap 2 3 * (swap 4 5 * swap 6 7),
    swap 0 1 * swap 2 3 * (swap 4 6 * swap 5 7),
    swap 0 1 * swap 2 3 * (swap 4 5 * swap 6 7) * (swap 4 6 * swap 5 7)]

/-- Products in the three distinguished involutions, in binary order. -/
def evenWord : Fin 8 → S :=
  ![1, axisPermutation 0, axisPermutation 1, axisPermutation 0 * axisPermutation 1,
    axisPermutation 2, axisPermutation 0 * axisPermutation 2,
    axisPermutation 1 * axisPermutation 2,
    axisPermutation 0 * axisPermutation 1 * axisPermutation 2]

private def fullWord (i : Fin 2 × Fin 8) : S :=
  if i.1 = 0 then evenWord i.2 else swap 0 1 * evenWord i.2

private def wordGroup : Subgroup S where
  carrier := {q | ∃ i, q = fullWord i}
  one_mem' := ⟨(0, 0), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (by decide +kernel : ∀ i j, ∃ k, fullWord i * fullWord j = fullWord k) i j
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact (by decide +kernel : ∀ i, ∃ j, (fullWord i)⁻¹ = fullWord j) i

private theorem axisPermutation_mem (i : Fin 3) : axisPermutation i ∈ permutationA2 := by
  have h0 : swap (0 : Fin 8) 1 ∈ permutationA2 := subset_closure (by simp)
  have h1 : swap (2 : Fin 8) 3 ∈ permutationA2 := subset_closure (by simp)
  have h2 : swap (4 : Fin 8) 5 * swap 6 7 ∈ permutationA2 := subset_closure (by simp)
  have h3 : swap (4 : Fin 8) 6 * swap 5 7 ∈ permutationA2 := subset_closure (by simp)
  fin_cases i
  · exact permutationA2.mul_mem (permutationA2.mul_mem h0 h1) h2
  · exact permutationA2.mul_mem (permutationA2.mul_mem h0 h1) h3
  · exact permutationA2.mul_mem (permutationA2.mul_mem (permutationA2.mul_mem h0 h1) h2) h3

private theorem evenWord_mem (i : Fin 8) : evenWord i ∈ permutationA2 := by
  have h0 := axisPermutation_mem 0
  have h1 := axisPermutation_mem 1
  have h2 := axisPermutation_mem 2
  fin_cases i
  · exact permutationA2.one_mem
  · exact h0
  · exact h1
  · exact permutationA2.mul_mem h0 h1
  · exact h2
  · exact permutationA2.mul_mem h0 h2
  · exact permutationA2.mul_mem h1 h2
  · exact permutationA2.mul_mem (permutationA2.mul_mem h0 h1) h2

private theorem wordGroup_eq : wordGroup = permutationA2 := by
  apply le_antisymm
  · rintro q ⟨i, rfl⟩
    dsimp [fullWord]
    split
    · exact evenWord_mem _
    · exact permutationA2.mul_mem (subset_closure (by simp)) (evenWord_mem _)
  · apply (closure_le _).mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(1, 0), by decide +kernel⟩
    · exact ⟨(1, 7), by decide +kernel⟩
    · exact ⟨(0, 6), by decide +kernel⟩
    · exact ⟨(0, 5), by decide +kernel⟩

theorem evenWord_even (i : Fin 8) : evenWord i ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.mpr ((by decide +kernel : ∀ i, (evenWord i).sign = 1) i)

/-- Exact enumeration of the actual inner part, including the identity. -/
theorem mem_B2_iff (a : M) : a ∈ B2 ↔ ∃ i, permutationEquiv a = evenWord i := by
  constructor
  · rintro ⟨ha, hi⟩
    change permutationEquiv a ∈ permutationA2 at ha
    rw [← wordGroup_eq] at ha
    obtain ⟨⟨j, i⟩, he⟩ := ha
    have hs := Perm.mem_alternatingGroup.mp ((permutationEquiv_mem_alternating a).mpr hi)
    fin_cases j
    · exact ⟨i, he⟩
    · rw [he] at hs
      change (swap (0 : Fin 8) 1 * evenWord i).sign = 1 at hs
      rw [map_mul, Perm.mem_alternatingGroup.mp (evenWord_even i)] at hs
      norm_num [Perm.sign_swap] at hs
  · rintro ⟨i, hi⟩
    refine ⟨?_, (permutationEquiv_mem_alternating a).mp ?_⟩
    · change permutationEquiv a ∈ permutationA2
      rw [hi]
      exact evenWord_mem i
    · rw [hi]
      exact evenWord_even i

/-- The corresponding genuine natural linear transformations. -/
noncomputable def linearWord (i : Fin 8) : G :=
  linearAlternatingEquiv.symm ⟨evenWord i, evenWord_even i⟩

@[simp] theorem linearWord_permutation (i : Fin 8) :
    (linearAlternatingEquiv (linearWord i)).val = evenWord i := by
  simp [linearWord]

@[simp] theorem conj_linearWord (i : Fin 8) :
    permutationEquiv (MulAut.conj (linearWord i)) = evenWord i := by
  rw [permutationEquiv_inner, linearWord_permutation]

/-- Natural generators indexed by the three transvections, without an arbitrary choice. -/
noncomputable def axisLinear (i : Fin 3) : G := linearWord (![1, 2, 4] i)

@[simp] theorem axisLinear_permutation (i : Fin 3) :
    (linearAlternatingEquiv (axisLinear i)).val = axisPermutation i := by
  rw [axisLinear, linearWord_permutation]
  fin_cases i <;> rfl

theorem conj_axisLinear_mem (i : Fin 3) : MulAut.conj (axisLinear i) ∈ B2 :=
  (mem_B2_iff _).mpr ⟨![1, 2, 4] i, conj_linearWord _⟩

theorem mem_innerPreimage_B2_iff (g : G) : g ∈ innerPreimage B2 ↔ ∃ i, g = linearWord i := by
  change MulAut.conj g ∈ B2 ↔ _
  rw [mem_B2_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, linearAlternatingEquiv.injective (Subtype.ext ?_)⟩
    rw [linearWord_permutation, ← permutationEquiv_inner]
    exact hi
  · rintro ⟨i, rfl⟩
    exact ⟨i, conj_linearWord i⟩

theorem linearWord_injective : Function.Injective linearWord := by
  intro i j hij
  apply (by decide +kernel : Function.Injective evenWord)
  simpa only [linearWord_permutation] using congrArg (fun g : G => (linearAlternatingEquiv g).val) hij

@[simp] theorem linearWord_zero : linearWord 0 = 1 := by
  apply linearAlternatingEquiv.injective
  apply Subtype.ext
  rw [linearWord_permutation, map_one]
  rfl

theorem axisLinear_injective : Function.Injective axisLinear := by
  intro i j hij
  apply (by decide : Function.Injective (fun i : Fin 3 => (![1, 2, 4] i : Fin 8)))
  exact linearWord_injective hij

theorem axisLinear_ne_one (i : Fin 3) : axisLinear i ≠ 1 := by
  intro hi
  have h := linearWord_injective (hi.trans linearWord_zero.symm)
  exact (by decide : ∀ i : Fin 3, (![1, 2, 4] i : Fin 8) ≠ 0) i h

/-- Exactly the three displayed transformations are transvections, conditional
only on the permitted universal exceptional marking theorem. -/
theorem isTransvection_iff_axisLinear
    (hmark : ∀ g : G, IsTransvection g ↔
      (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2})
    {g : G} (hg : g ∈ innerPreimage B2) : IsTransvection g ↔ ∃ i, g = axisLinear i := by
  obtain ⟨i, rfl⟩ := (mem_innerPreimage_B2_iff g).mp hg
  rw [hmark, linearWord_permutation]
  have ht : ∀ i, (evenWord i).cycleType = {2, 2, 2, 2} ↔ i = 1 ∨ i = 2 ∨ i = 4 :=
    by decide +kernel
  rw [ht]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨j, hj⟩
    have hi := linearWord_injective hj
    fin_cases j <;> simp_all [axisLinear]

/-- The complete word expression, now inside the original natural linear group. -/
theorem linearWord_eq_products (i : Fin 8) :
    linearWord i =
      ![1, axisLinear 0, axisLinear 1, axisLinear 0 * axisLinear 1,
        axisLinear 2, axisLinear 0 * axisLinear 2, axisLinear 1 * axisLinear 2,
        axisLinear 0 * axisLinear 1 * axisLinear 2] i := by
  apply linearAlternatingEquiv.injective
  apply Subtype.ext
  rw [linearWord_permutation]
  fin_cases i <;> simp [evenWord, axisLinear_permutation]

/-- The displayed involutions generate the whole actual inner part. -/
theorem innerPreimage_B2_eq_closure :
    innerPreimage B2 = closure (Set.range axisLinear) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, rfl⟩ := (mem_innerPreimage_B2_iff g).mp hg
    have h (i : Fin 3) : axisLinear i ∈ closure (Set.range axisLinear) :=
      subset_closure ⟨i, rfl⟩
    rw [linearWord_eq_products]
    fin_cases i
    · exact one_mem _
    · exact h 0
    · exact h 1
    · exact mul_mem (h 0) (h 1)
    · exact h 2
    · exact mul_mem (h 0) (h 2)
    · exact mul_mem (h 1) (h 2)
    · exact mul_mem (mul_mem (h 0) (h 1)) (h 2)
  · apply (closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact conj_axisLinear_mem i

/-- All common natural fixed vectors are already fixed by the three marked axes. -/
theorem mem_naturalFixed_B2_iff (x : X) :
    x ∈ naturalFixed B2 ↔ ∀ i : Fin 3, axisLinear i x = x := by
  constructor
  · intro hx i
    exact (mem_naturalFixed B2 x).mp hx _ (conj_axisLinear_mem i)
  · intro hx
    apply (mem_naturalFixed B2 x).mpr
    intro g hg
    obtain ⟨i, rfl⟩ := (mem_innerPreimage_B2_iff g).mp hg
    rw [linearWord_eq_products]
    fin_cases i <;> simp [hx]

/-- Subspace equality, retaining the literal three natural axes. -/
theorem naturalFixed_B2_eq_iInf :
    naturalFixed B2 = ⨅ i : Fin 3, BinaryNaturalDual.fixedSpace (axisLinear i) := by
  ext x
  simp only [mem_naturalFixed_B2_iff, Submodule.mem_iInf, mem_fixedSpace]

/-- The exact order of the actual inner part; no permutation-group order oracle is used. -/
theorem card_B2 : Nat.card B2 = 8 := by
  let f : Fin 8 → B2 := fun i => ⟨MulAut.conj (linearWord i),
    (mem_B2_iff _).mpr ⟨i, conj_linearWord i⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply (by decide +kernel : Function.Injective evenWord)
      simpa only [f, conj_linearWord] using
        congrArg (fun a : B2 => permutationEquiv a.val) h
    · intro a
      obtain ⟨i, hi⟩ := (mem_B2_iff a.val).mp a.property
      refine ⟨i, Subtype.ext (permutationEquiv.injective ?_)⟩
      exact (conj_linearWord i).trans hi.symm
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)

/-- The three axis transformations commute as actual linear maps. -/
theorem axisLinear_commute (i j : Fin 3) : Commute (axisLinear i) (axisLinear j) := by
  apply linearAlternatingEquiv.injective
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul, axisLinear_permutation]
  exact (by decide +kernel : ∀ i j, axisPermutation i * axisPermutation j =
    axisPermutation j * axisPermutation i) i j

theorem axisLinear_square (i : Fin 3) : axisLinear i ^ 2 = 1 := by
  apply linearAlternatingEquiv.injective
  apply Subtype.ext
  simp only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, axisLinear_permutation]
  exact (by decide +kernel : ∀ i, axisPermutation i ^ 2 = 1) i

/-- Products of distinct displayed transvections are not transvections.
This distinguishes the three axes in the subsequent linear calculation. -/
theorem axisLinear_mul_not_transvection
    (hmark : ∀ g : G, IsTransvection g ↔
      (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2})
    {i j : Fin 3} (hij : i ≠ j) : ¬ IsTransvection (axisLinear i * axisLinear j) := by
  rw [hmark]
  simp only [map_mul, Subgroup.coe_mul, axisLinear_permutation]
  exact (by decide +kernel : ∀ i j : Fin 3, i ≠ j →
    (axisPermutation i * axisPermutation j).cycleType ≠ {2, 2, 2, 2}) i j hij

theorem axisLinear_isTransvection
    (hmark : ∀ g : G, IsTransvection g ↔
      (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2}) (i : Fin 3) :
    IsTransvection (axisLinear i) :=
  (isTransvection_iff_axisLinear hmark (conj_axisLinear_mem i)).mpr ⟨i, rfl⟩

/-- Every word is an involution, including the identity word. -/
theorem linearWord_square (i : Fin 8) : linearWord i ^ 2 = 1 := by
  apply linearAlternatingEquiv.injective
  apply Subtype.ext
  simp only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, linearWord_permutation]
  exact (by decide +kernel : ∀ i, evenWord i ^ 2 = 1) i

/-- Every non-axis, nonidentity element has the permitted two-dimensional
natural fixed space. This does not yet identify it with the common fixed space. -/
theorem other_fixedSpace_finrank
    (hdim : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → ¬ IsTransvection g →
      Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 2)
    {g : G} (hg : g ∈ innerPreimage B2) (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 2 := by
  obtain ⟨i, rfl⟩ := (mem_innerPreimage_B2_iff g).mp hg
  exact hdim _ (linearWord_square i) hg1 hgt

/-- Common fixed vectors in the genuine contragredient summand. -/
noncomputable def dualFixed (A : Subgroup M) : Submodule (ZMod 2) (Module.Dual (ZMod 2) X) :=
  ⨅ g : innerPreimage A, BinaryNaturalDual.fixedSpace g.val.symm.dualMap

@[simp] theorem mem_dualFixed (A : Subgroup M) (f : Module.Dual (ZMod 2) X) :
    f ∈ dualFixed A ↔ ∀ g : G, MulAut.conj g ∈ A → g.symm.dualMap f = f := by
  simp only [dualFixed, Submodule.mem_iInf, mem_fixedSpace]
  exact Subtype.forall

/-- For inner actors the fixed module is the literal product of its natural
and dual fixed subspaces. -/
theorem actorFixed_eq_prod (d : CoordinateAction 4) {A : Subgroup M} (hA : A ≤ inner) :
    actorFixed d A = (naturalFixed A).prod (dualFixed A) := by
  ext v
  simp only [mem_actorFixed, Submodule.mem_prod, mem_naturalFixed, mem_dualFixed]
  constructor
  · intro h
    constructor
    · intro g hg
      have hv := congrArg Prod.fst (h _ hg)
      simpa only [d.on_inner, naturalDualRepresentation_apply] using hv
    · intro g hg
      have hv := congrArg Prod.snd (h _ hg)
      simpa only [d.on_inner, naturalDualRepresentation_apply] using hv
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨g, rfl⟩ := hA ha
    rw [d.on_inner, naturalDualRepresentation_apply, h1 g ha, h2 g ha]

/-- The permitted elementary-abelian premise supplies literal commutation. -/
theorem A2_commute [IsElementaryAbelian 2 A2] {a b : M}
    (ha : a ∈ A2) (hb : b ∈ A2) : a * b = b * a :=
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A2) ⟨b, hb⟩)

/-- The source's diagonal formula, with its group-theoretic hypotheses discharged. -/
theorem actorFixed_A2_iff [IsElementaryAbelian 2 A2] (d : CoordinateAction 4)
    {a : M} (ha : a ∈ A2) (haB : a ∉ B2) (v : V) :
    v ∈ actorFixed d A2 ↔ ∃ x ∈ naturalFixed B2,
      (x, 0) + d.representation a (x, 0) = v := by
  apply actorFixed_eq_outer_diagonal d A2 (fun _ hb _ hc => A2_commute hb hc) a ha
  · exact elemPow_eq_one_of_isElementaryAbelian a ha
  · exact fun hi => haB ⟨ha, hi⟩

/-- The numerical conclusion is reduced to the genuine natural fixed space. -/
theorem actorFixed_A2_finrank [IsElementaryAbelian 2 A2] (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d A2) = Module.finrank (ZMod 2) (naturalFixed B2) :=
  actorFixed_finrank d A2 (fun _ hb _ hc => A2_commute hb hc)
    transposition transposition_mem_A2
    (elemPow_eq_one_of_isElementaryAbelian transposition transposition_mem_A2) transposition_outer

end BinaryNaturalDual.FourActors.A2Module
