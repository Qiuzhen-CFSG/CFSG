module
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Generators
/-!
# A lower bound for the M23 involution centralizer

We exhibit 2688 centralizing elements as products of two families of generator
words. The 16 words in the first family have distinct images of point 16.
The 168 words in the second family fix that point and have distinct images
of the ordered triple (1, 2, 3). Evaluation at 16 and then left cancellation
prove that all 16 × 168 products are distinct.

The finite word certificates are checked by kernel reduction against the
certified generator tables. The words were found by permutation calculations;
those calculations are used only to supply witnesses, not to establish the
cardinality claim.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.21, printed p.657 (PDF p.674).
-/

namespace Sporadic.Mathieu.M23Geometry
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private abbrev C := Subgroup.centralizer ({involutionRepresentative} : Set M23)
private def wordElement : List (Fin 7) → C
  | [] => 1
  | j :: w => involutionCentralizerGenerator j * wordElement w
private def wordAction : List (Fin 7) → Fin 23 → Fin 23
  | [] => id
  | j :: w => fun x => involutionCentralizerGeneratorTable j (wordAction w x)
private theorem wordElement_apply (w : List (Fin 7)) (x : Fin 23) :
    ((wordElement w).val.val) x = wordAction w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change involutionCentralizerGeneratorTable j (((wordElement w).val.val) x) = _
    rw [ih]
    rfl
private def translationWords : Fin 16 → List (Fin 7) :=
  ![[],
    [0],
    [1],
    [1,0],
    [2],
    [2,0],
    [2,1],
    [2,1,0],
    [3],
    [3,0],
    [3,1],
    [3,1,0],
    [3,2],
    [3,2,0],
    [3,2,1],
    [3,2,1,0]]

private def linearWords : Fin 168 → List (Fin 7) :=
  ![[],
    [4],
    [5],
    [6],
    [4,4],
    [5,4],
    [6,4],
    [4,5],
    [5,5],
    [6,5],
    [4,6],
    [5,6],
    [6,6],
    [5,4,4],
    [6,4,4],
    [4,5,4],
    [5,5,4],
    [6,5,4],
    [4,6,4],
    [5,6,4],
    [6,6,4],
    [6,4,5],
    [6,5,5],
    [4,6,5],
    [5,6,5],
    [6,6,5],
    [4,4,6],
    [5,4,6],
    [6,4,6],
    [4,5,6],
    [5,5,6],
    [6,5,6],
    [4,6,6],
    [5,6,6],
    [4,5,4,4],
    [5,5,4,4],
    [6,5,4,4],
    [4,6,4,4],
    [5,6,4,4],
    [6,6,4,4],
    [6,4,5,4],
    [6,5,5,4],
    [4,6,5,4],
    [6,6,5,4],
    [4,4,6,4],
    [5,4,6,4],
    [6,4,6,4],
    [4,5,6,4],
    [5,5,6,4],
    [4,6,6,4],
    [5,6,6,4],
    [4,6,4,5],
    [5,6,4,5],
    [6,6,4,5],
    [4,6,5,5],
    [5,6,5,5],
    [6,6,5,5],
    [4,4,6,5],
    [5,4,6,5],
    [6,4,6,5],
    [4,5,6,5],
    [5,5,6,5],
    [6,5,6,5],
    [4,6,6,5],
    [5,6,6,5],
    [5,4,4,6],
    [6,4,4,6],
    [4,5,4,6],
    [5,5,4,6],
    [4,6,4,6],
    [5,6,4,6],
    [6,6,4,6],
    [6,4,5,6],
    [4,6,5,6],
    [4,4,6,6],
    [5,4,6,6],
    [6,4,6,6],
    [4,5,6,6],
    [6,4,5,4,4],
    [6,5,5,4,4],
    [4,6,5,4,4],
    [6,6,5,4,4],
    [4,4,6,4,4],
    [4,5,6,4,4],
    [5,5,6,4,4],
    [4,6,4,5,4],
    [6,6,4,5,4],
    [4,4,6,5,4],
    [5,4,6,5,4],
    [5,4,4,6,4],
    [4,5,4,6,4],
    [5,5,4,6,4],
    [4,6,4,6,4],
    [5,6,4,6,4],
    [6,6,4,6,4],
    [6,4,5,6,4],
    [4,4,6,6,4],
    [5,4,6,6,4],
    [6,4,6,6,4],
    [4,5,6,6,4],
    [4,4,6,4,5],
    [4,5,6,4,5],
    [5,5,6,4,5],
    [4,5,6,5,5],
    [5,5,6,5,5],
    [6,5,6,5,5],
    [5,4,4,6,5],
    [4,5,4,6,5],
    [5,5,4,6,5],
    [4,6,4,6,5],
    [5,6,4,6,5],
    [6,4,5,6,5],
    [4,6,5,6,5],
    [4,4,6,6,5],
    [5,4,6,6,5],
    [6,4,6,6,5],
    [4,5,6,6,5],
    [4,5,4,4,6],
    [5,5,4,4,6],
    [6,5,4,4,6],
    [5,6,4,4,6],
    [6,4,5,4,6],
    [5,4,6,4,6],
    [6,4,6,4,6],
    [4,5,6,4,6],
    [4,6,6,4,6],
    [6,6,4,5,6],
    [4,4,6,5,6],
    [6,4,6,5,6],
    [6,4,4,6,6],
    [4,5,4,6,6],
    [4,6,4,6,6],
    [4,4,6,5,4,4],
    [5,4,4,6,4,4],
    [4,4,6,4,5,4],
    [5,5,4,4,6,4],
    [6,5,4,4,6,4],
    [6,4,5,4,6,4],
    [5,4,6,4,6,4],
    [6,4,6,4,6,4],
    [4,5,6,4,6,4],
    [4,6,6,4,6,4],
    [6,6,4,5,6,4],
    [6,4,4,6,6,4],
    [4,5,4,6,6,4],
    [5,4,4,6,4,5],
    [6,4,5,6,4,5],
    [6,4,5,6,5,5],
    [5,5,4,4,6,5],
    [6,4,5,4,6,5],
    [6,4,6,4,6,5],
    [4,5,6,4,6,5],
    [6,6,4,5,6,5],
    [4,4,6,5,6,5],
    [6,4,6,5,6,5],
    [6,4,4,6,6,5],
    [4,5,4,6,6,5],
    [6,4,5,4,4,6],
    [6,6,5,4,4,6],
    [5,5,6,4,4,6],
    [4,6,4,5,4,6],
    [4,5,4,6,4,6],
    [4,4,6,6,4,6],
    [6,4,6,6,4,6],
    [6,4,6,4,6,6],
    [6,6,5,4,4,6,4],
    [4,6,4,5,4,6,4],
    [6,4,6,6,4,6,4]]

private theorem translation_separates :
    Function.Injective (fun i : Fin 16 => wordAction (translationWords i) 16) := by
  decide +kernel

private theorem linear_fixes (i : Fin 168) : wordAction (linearWords i) 16 = 16 := by
  revert i
  decide +kernel

private theorem linear_separates :
    Function.Injective (fun i : Fin 168 =>
      (wordAction (linearWords i) 1, wordAction (linearWords i) 2,
        wordAction (linearWords i) 3)) := by
  decide +kernel

private def centralizerProduct (ij : Fin 16 × Fin 168) : C :=
  wordElement (translationWords ij.1) * wordElement (linearWords ij.2)

private theorem centralizerProduct_injective : Function.Injective centralizerProduct := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have h16 := congrArg (fun g : C => g.val.val (16 : Fin 23)) h
  change (wordElement (translationWords i)).val.val
      ((wordElement (linearWords j)).val.val 16) =
    (wordElement (translationWords k)).val.val
      ((wordElement (linearWords l)).val.val 16) at h16
  simp only [wordElement_apply, linear_fixes] at h16
  have hik : i = k := translation_separates h16
  subst k
  have hjl : wordElement (linearWords j) = wordElement (linearWords l) :=
    mul_left_cancel h
  have ht := congrArg (fun g : C =>
    (g.val.val (1 : Fin 23), g.val.val (2 : Fin 23), g.val.val (3 : Fin 23))) hjl
  simp only [wordElement_apply] at ht
  have hindex : j = l := linear_separates ht
  subst l
  rfl

/-- The centralizer of the representative involution of M23 has at least 2688 elements. -/
public theorem involutionRepresentative_centralizer_card_lower :
    2688 ≤ Nat.card (Subgroup.centralizer ({involutionRepresentative} : Set M23)) := by
  have h := Nat.card_le_card_of_injective centralizerProduct centralizerProduct_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

end
end Sporadic.Mathieu.M23Geometry
