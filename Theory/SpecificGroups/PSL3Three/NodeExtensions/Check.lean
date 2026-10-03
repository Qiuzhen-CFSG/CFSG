module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check

/-!
# Exact extension certificates for the fixed SL₃(3) nodes

A proper extension carries words in both directions and a determinant-one
conjugator. A whole-group extension carries words for the ambient generators;
`ambient_wordSubgroup_eq_top` supplies the reverse containment in the actual
matrix group. The Boolean checks below certify matrix equations in the kernel.

Source: `SubgroupEnumeration.ExtensionWords.sound` and the elementary
one-generator extension argument used for GLS III, Theorem 6.5.3.
-/
namespace Matrix.PSL3Three.CertifiedEnumeration.ExtensionCheck
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck

/-- Untrusted data for one exact extension, with the original node numbering. -/
public inductive Witness (n : Nat) where
  | proper (target : Fin 50) (conjugator : MatrixCode)
      (words : ExtensionWords n ((generatorCodes target).length + (generatorCodes target).length))
  | top (backward : Fin 4 → List (Fin (n + 2)))

@[expose] public def allFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.ofFn f).all id

public theorem allFin_sound {n : Nat} {f : Fin n → Bool}
    (h : allFin f = true) : ∀ i, f i = true := by
  simpa [allFin, List.all_eq_true] using h

@[expose] public def wordsCheck {n m : Nat} (w : ExtensionWords n m)
    (gen : Fin n → SL) (target : Fin m → SL) (x g : SL) : Bool :=
  allFin (fun i => matrixEq (evalWord target (w.forward i)).val
    (g * gen i * g⁻¹).val) &&
  matrixEq (evalWord target w.newGenerator).val (g * x * g⁻¹).val &&
  allFin (fun j => matrixEq (g * evalWord (extensionGen gen x) (w.backward j) * g⁻¹).val
    (target j).val)

private theorem map_evalWord {n : Nat} (f : SL →* SL) (gen : Fin n → SL)
    (w : List (Fin n)) :
    evalWord (fun i => f (gen i)) w = f (evalWord gen w) := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih => simp only [evalWord, ih, map_mul]

public theorem wordsCheck_sound {n m : Nat} (w : ExtensionWords n m)
    (gen : Fin n → SL) (target : Fin m → SL) (x g : SL)
    (h : wordsCheck w gen target x g = true) :
    w.Valid gen target x (MulAut.conj g).toMonoidHom := by
  simp only [wordsCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hf, hx⟩, hb⟩ := h
  refine ⟨fun i => Subtype.ext (matrixEq_sound (allFin_sound hf i)),
    Subtype.ext (matrixEq_sound hx), fun j => ?_⟩
  rw [map_evalWord]
  exact Subtype.ext (matrixEq_sound (allFin_sound hb j))

@[expose] public def check {n : Nat} (gen : Fin n → SL) (x : SL) : Witness n → Bool
  | .proper j c w =>
    if h : codeDet c = 1 then
      wordsCheck w gen (nodeGenerator j) x (finiteModelEquiv ⟨c, h⟩)
    else false
  | .top w => allFin (fun j => matrixEq (evalWord (extensionGen gen x) (w j)).val
      (ambientGenerator j).val)

public theorem sound (i : Fin 50) (x : SL)
    (w : Witness ((generatorCodes i).length + (generatorCodes i).length))
    (h : check (nodeGenerator i) x w = true) :
    Represented node (properNode i ⊔ Subgroup.zpowers x) := by
  cases w with
  | proper j c w =>
    simp only [check] at h
    split at h
    next hc =>
      refine ⟨j.castSucc, finiteModelEquiv ⟨c, hc⟩, ?_⟩
      rw [node_castSucc, properNode_eq_wordSubgroup, properNode_eq_wordSubgroup]
      exact w.sound (nodeGenerator i) symmInv (nodeGenerator_inv i)
        (nodeGenerator j) symmInv (nodeGenerator_inv j) x _
        (wordsCheck_sound w _ _ _ _ h)
    next => contradiction
  | top w =>
    have heq : properNode i ⊔ Subgroup.zpowers x = ⊤ := by
      apply top_unique
      rw [← ambient_wordSubgroup_eq_top]
      apply wordSubgroup_le
      intro j
      have hw := Subtype.ext (matrixEq_sound (allFin_sound h j))
      rw [← hw, properNode_eq_wordSubgroup]
      exact evalWord_mem _ _ (extensionGen_mem (nodeGenerator i) symmInv (nodeGenerator_inv i) x) _
    exact ⟨50, 1, by simp [heq]⟩

end Matrix.PSL3Three.CertifiedEnumeration.ExtensionCheck
