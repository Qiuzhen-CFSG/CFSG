module
public import Theory.Representation.BinarySevenCode.WeightTwoCore

/-!
# The two block actions of a weight-four word stabilizer

Restriction to the support and its complement gives the full independent
permutation groups on those sets. At weight four they have sizes four and
three. The resulting S₄ × S₃ marking retains both evaluation formulas;
it therefore identifies the actual source factors rather than just the
isomorphism type of the stabilizer.

Source: Aschbacher--Smith, the paragraph preceding 12.3.13, printed p.811.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinarySevenCode.WeightFourLocal
open WeightTwoGeometry

abbrev Support (w : EvenWord) := {i : Fin 7 // i ∈ support w}

def supportPermutation (w : EvenWord) : symmetricStabilizer w →* Equiv.Perm (Support w) where
  toFun g :=
    { toFun i := ⟨g.val i,(stabilizer_mem_support w g i).mpr i.property⟩
      invFun i := ⟨g.val.symm i,(stabilizer_mem_support w g⁻¹ i).mpr i.property⟩
      left_inv i := Subtype.ext (g.val.symm_apply_apply i)
      right_inv i := Subtype.ext (g.val.apply_symm_apply i) }
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

def blockHom (w : EvenWord) : symmetricStabilizer w →*
    (Equiv.Perm (Support w) × Equiv.Perm (Complement w)) :=
  (supportPermutation w).prod (complementPermutation w)

private def blockLetters (w : EvenWord) : Support w ⊕ Complement w ≃ Fin 7 where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if hi : i ∈ support w then Sum.inl ⟨i,hi⟩
    else Sum.inr ⟨i,Finset.mem_compl.mpr hi⟩
  left_inv := by
    rintro (i | i)
    · simp [i.property]
    · simp [Finset.mem_compl.mp i.property]
  right_inv i := by
    dsimp only
    split_ifs <;> rfl

theorem blockHom_bijective (w : EvenWord) : Function.Bijective (blockHom w) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ support w
    · exact congrArg (fun p : Equiv.Perm (Support w) => (p ⟨i,hi⟩).val)
        (congrArg Prod.fst he)
    · exact congrArg (fun p : Equiv.Perm (Complement w) =>
          (p ⟨i,Finset.mem_compl.mpr hi⟩).val) (congrArg Prod.snd he)
  · rintro ⟨a,b⟩
    let e := blockLetters w
    let g := e.permCongr (Equiv.sumCongr a b)
    have hs (i : Support w) : g i = a i := by
      change e (Equiv.sumCongr a b (e.symm (e (Sum.inl i)))) = _
      rw [e.symm_apply_apply]
      rfl
    have hc (i : Complement w) : g i = b i := by
      change e (Equiv.sumCongr a b (e.symm (e (Sum.inr i)))) = _
      rw [e.symm_apply_apply]
      rfl
    have hmem (i : Fin 7) : g i ∈ support w ↔ i ∈ support w := by
      by_cases hi : i ∈ support w
      · rw [hs ⟨i,hi⟩]
        exact iff_of_true (a ⟨i,hi⟩).property hi
      · rw [hc ⟨i,Finset.mem_compl.mpr hi⟩]
        exact iff_of_false (Finset.mem_compl.mp (b ⟨i,Finset.mem_compl.mpr hi⟩).property) hi
    have hg : g ∈ symmetricStabilizer w := by
      rw [mem_symmetricStabilizer]
      apply Subtype.ext
      funext i
      apply (by decide : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y)
      have h := hmem (g.symm i)
      rw [g.apply_symm_apply] at h
      simpa only [evenRepresentation_apply,support,Finset.mem_filter,Finset.mem_univ,true_and] using h.symm
    refine ⟨⟨g,hg⟩,Prod.ext ?_ ?_⟩
    · apply Equiv.ext
      intro i
      exact Subtype.ext (hs i)
    · apply Equiv.ext
      intro i
      exact Subtype.ext (hc i)

/-- The full word stabilizer acts independently on its two literal blocks. -/
def blockEquiv (w : EvenWord) : symmetricStabilizer w ≃*
    (Equiv.Perm (Support w) × Equiv.Perm (Complement w)) :=
  MulEquiv.ofBijective (blockHom w) (blockHom_bijective w)

theorem support_card (w : EvenWord) (hw : weight w.val = 4) :
    Fintype.card (Support w) = 4 := by
  change Fintype.card ↥(support w) = 4
  rw [Fintype.card_coe]
  exact hw

theorem complement_card (w : EvenWord) (hw : weight w.val = 4) :
    Fintype.card (Complement w) = 3 := by
  rw [Fintype.card_coe,Finset.card_compl]
  change 7 - weight w.val = 3
  rw [hw]

def fourLetters (w : EvenWord) (hw : weight w.val = 4) : Support w ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (support_card w hw)

def threeLetters (w : EvenWord) (hw : weight w.val = 4) : Complement w ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (complement_card w hw)

/-- The source S₄ × S₃ marking, obtained by restricting permutations to the
support and its complement, then relabelling these same two sets. -/
def pointEquiv (w : EvenWord) (hw : weight w.val = 4) : symmetricStabilizer w ≃*
    (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  (blockEquiv w).trans (MulEquiv.prodCongr
    (Equiv.permCongrHom (fourLetters w hw)) (Equiv.permCongrHom (threeLetters w hw)))

theorem pointEquiv_first (w : EvenWord) (hw : weight w.val = 4)
    (g : symmetricStabilizer w) (i : Support w) :
    (pointEquiv w hw g).1 (fourLetters w hw i) =
      fourLetters w hw (supportPermutation w g i) := by
  change (fourLetters w hw).permCongr _ ((fourLetters w hw) i) = _
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]

theorem pointEquiv_second (w : EvenWord) (hw : weight w.val = 4)
    (g : symmetricStabilizer w) (i : Complement w) :
    (pointEquiv w hw g).2 (threeLetters w hw i) =
      threeLetters w hw (complementPermutation w g i) := by
  change (threeLetters w hw).permCongr _ ((threeLetters w hw) i) = _
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]

end BinarySevenCode.WeightFourLocal
