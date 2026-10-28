module
public import Theory.Representation.BinarySevenCode.WeightTwoResidual
public import Theory.GroupAction.OddTransitiveTwoCore

/-!
# The two-core on the five complementary letters

An actor stabilizing a weight-two word and containing its literal A₅ fixer
acts transitively on the five complementary letters. Its normal two-core
has a fixed letter, and normality then makes every complementary letter
fixed. Consequently it fixes every word vanishing on the support pair.

This is the core-action calculation in Aschbacher--Smith, Lemma 12.3.7(2),
printed p.809. The source application retains the original point residual
and its embedded two-core.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace BinarySevenCode.WeightTwoGeometry

abbrev Complement (w : EvenWord) := {i : Fin 7 // i ∈ (support w)ᶜ}
abbrev symmetricStabilizer (w : EvenWord) :=
  MulAction.stabilizer (Equiv.Perm (Fin 7)) (support w : Set (Fin 7))

theorem mem_symmetricStabilizer (g : Equiv.Perm (Fin 7)) (w : EvenWord) :
    g ∈ symmetricStabilizer w ↔ evenRepresentation g w = w := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  constructor
  · intro h
    apply Subtype.ext
    funext i
    apply (by decide : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y)
    have hi := h i
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hi
    simp only [support, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  · intro h i
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hi := congrArg (fun v : EvenWord => v.val i) h
    change w.val (g.symm i) = w.val i at hi
    simp only [support, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    change w.val (g.symm i) ≠ 0 ↔ w.val i ≠ 0
    rw [hi]

theorem stabilizer_mem_support (w : EvenWord) (g : symmetricStabilizer w) (i : Fin 7) :
    g.val i ∈ support w ↔ i ∈ support w := by
  have hg := g.property
  rw [MulAction.mem_stabilizer_iff] at hg
  have h := Set.ext_iff.mp hg (g.val i)
  simpa only [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, Finset.mem_coe] using h.symm

def complementPermutation (w : EvenWord) : symmetricStabilizer w →*
    Equiv.Perm (Complement w) where
  toFun g :=
    { toFun i := ⟨g.val i, Finset.mem_compl.mpr (fun h =>
        (Finset.mem_compl.mp i.property) ((stabilizer_mem_support w g i).mp h))⟩
      invFun i := ⟨g.val.symm i, Finset.mem_compl.mpr (fun h =>
        (Finset.mem_compl.mp i.property) ((stabilizer_mem_support w g⁻¹ i).mp h))⟩
      left_inv i := Subtype.ext (g.val.symm_apply_apply i)
      right_inv i := Subtype.ext (g.val.apply_symm_apply i) }
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

theorem complement_card (w : EvenWord) (hw : weight w.val = 2) :
    Nat.card (Complement w) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,Finset.card_compl]
  change 7 - weight w.val = 5
  rw [hw]

theorem five_transitive_complement (w : EvenWord) (hw : weight w.val = 2)
    (i j : Complement w) : ∃ a : five w, a.val.val i = j := by
  let : MulAction.IsPretransitive (alternatingGroup (Complement w)) (Complement w) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by rw [complement_card w hw]; decide)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Complement w)) i j
  let e := Atlas.Families.Alternating.stabilizerComplementEquiv (support w)
  refine ⟨e.symm g,?_⟩
  have he := Atlas.Families.Alternating.stabilizerComplementEquiv_apply (support w) (e.symm g) i
  change ((e (e.symm g)).val i).val = (e.symm g).val.val i at he
  rw [e.apply_symm_apply] at he
  exact he.symm.trans (congrArg Subtype.val hg)

variable {H : Type*} [Group H]
/-- The two-core of an actor containing the literal A₅ fixes its five letters. -/
theorem twoCore_fixes_complement (w : EvenWord) (hw : weight w.val = 2)
    (f : H →* symmetricStabilizer w)
    (hf : ∀ a : five w, ∃ h : H, (f h).val = a.val.val)
    (q : pCore 2 H) (i : Complement w) : (f q).val i = i := by
  let π := (complementPermutation w).comp f
  let : MulAction H (Complement w) := MulAction.compHom (Complement w) π
  obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := H)).nonempty_fixed_point_of_prime_not_dvd_card
    (Complement w) (by rw [complement_card w hw]; decide)
  obtain ⟨a,ha⟩ := five_transitive_complement w hw j i
  obtain ⟨h,hh⟩ := hf a
  have hi : h • j = i := Subtype.ext ((congrArg (fun s : Equiv.Perm (Fin 7) => s j) hh).trans ha)
  have hfix : i ∈ MulAction.fixedPoints (pCore 2 H) (Complement w) :=
    hi ▸ smul_mem_fixedPoints_of_normal h hj
  exact congrArg Subtype.val (hfix q)

/-- A permutation fixing the complementary letters fixes every word supported there. -/
theorem fixes_word_of_complement_fixed (w x : EvenWord)
    (g : symmetricStabilizer w)
    (hg : ∀ i : Complement w, g.val i = i)
    (hx : ∀ i ∈ support w, x.val i = 0) : evenRepresentation g.val x = x := by
  apply Subtype.ext
  funext i
  change x.val (g.val.symm i) = x.val i
  by_cases hi : i ∈ support w
  · rw [hx i hi, hx (g.val.symm i) ((stabilizer_mem_support w g⁻¹ i).mpr hi)]
  · have he := hg ⟨i,Finset.mem_compl.mpr hi⟩
    have hgi : g.val.symm i = i := (Equiv.symm_apply_eq _).mpr he.symm
    rw [hgi]

end BinarySevenCode.WeightTwoGeometry
