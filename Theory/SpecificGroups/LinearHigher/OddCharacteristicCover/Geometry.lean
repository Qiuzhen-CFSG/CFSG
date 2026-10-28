module

public import Theory.SpecificGroups.LinearHigher.TorusAction
public import Mathlib.Data.ZMod.Basic

/-!
# Root geometry in degree four

Two Weyl words exchange disjoint roots without changing their coefficients.
An unused fourth coordinate and the signs of diagonal torus words supply the
remaining geometric identities for the central-cover calculation.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, elementary matrix example.
-/

open scoped commutatorElement MatrixGroups
namespace Theory.SpecificGroups.LinearHigher.OddCharacteristicCover
open SteinbergWords
variable {F : Type*} [Field F]

public theorem projectiveRoot_zero (r : Root 4) : projectiveRoot r (0:F)=1 := by
  simp [projectiveRoot,matrixRoot,Matrix.SpecialLinearGroup.transvection_coeff_zero]

public theorem projectiveRoot_pow (r : Root 4) (a : F) (n : ℕ) :
    projectiveRoot r a ^ n = projectiveRoot r ((n:F)*a) := by
  induction n with
  | zero => simp [projectiveRoot_zero]
  | succ n hn =>
    rw [pow_succ,hn,projectiveRoot_relations.add]
    congr 1
    push_cast
    ring

public theorem exists_outside_overlap (r s : Root 4)
    (h : r.val.1=s.val.1 ∨ r.val.2=s.val.2) :
    ∃ m : Fin 4, m ≠ r.val.1 ∧ m ≠ r.val.2 ∧ m ≠ s.val.1 ∧ m ≠ s.val.2 := by
  have hh : ∀ i j k l : Fin 4, i=k ∨ j=l →
      ∃ m : Fin 4, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l := by decide
  exact hh _ _ _ _ h

public theorem exists_fourth (i j k : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  have hh : ∀ i j k : Fin 4, ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by decide
  exact hh i j k

public theorem disjoint_root_swap (r s : Root 4)
    (h13 : r.val.1 ≠ s.val.1) (h14 : r.val.1 ≠ s.val.2)
    (h23 : r.val.2 ≠ s.val.1) (h24 : r.val.2 ≠ s.val.2) :
    ∃ t : PSL(4,F),
      (∀ a, t*projectiveRoot r a*t⁻¹=projectiveRoot s a) ∧
      (∀ a, t*projectiveRoot s a*t⁻¹=projectiveRoot r a) := by
  rcases r with ⟨⟨i,j⟩,hij⟩
  rcases s with ⟨⟨k,l⟩,hkl⟩
  change i ≠ k at h13
  change i ≠ l at h14
  change j ≠ k at h23
  change j ≠ l at h24
  refine ⟨weylWord projectiveRoot i k h13 1 * weylWord projectiveRoot j l h24 1,?_,?_⟩
  · intro a
    rw [← MulAut.conj_apply]
    change MulAut.conj (weylWord (projectiveRoot (F:=F)) i k h13 1 *
      weylWord projectiveRoot j l h24 1) (projectiveRoot (root i j hij) a) =
      projectiveRoot (root k l hkl) a
    rw [map_mul,MulAut.mul_apply,
      weylWord_conj_other_incoming projectiveRoot_relations j l i h24 hij h14,
      weylWord_conj_outgoing projectiveRoot_relations i k l h13 h14 hkl]
    simp
  · intro a
    rw [← MulAut.conj_apply]
    change MulAut.conj (weylWord (projectiveRoot (F:=F)) i k h13 1 *
      weylWord projectiveRoot j l h24 1) (projectiveRoot (root k l hkl) a) =
      projectiveRoot (root i j hij) a
    rw [map_mul,MulAut.mul_apply,
      weylWord_conj_incoming projectiveRoot_relations j l k h24 h23.symm hkl,
      weylWord_conj_other_outgoing projectiveRoot_relations i k j h13 hij h23.symm]
    simp

public theorem rootWeight_sign (i j : Fin 4) (r : Root 4) :
    ∃ b : Bool, (rootWeight i j (-1 : Fˣ) r : F)=if b then -1 else 1 := by
  have hh : (rootWeight i j (-1 : Fˣ) r : F)=1 ∨
      (rootWeight i j (-1 : Fˣ) r : F)=-1 := by
    dsimp [rootWeight,torusWeight]
    split_ifs <;> simp
  rcases hh with hh | hh
  · exact ⟨false,hh⟩
  · exact ⟨true,hh⟩

public theorem rootWeight_chain (i j k a b : Fin 4) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Fˣ) :
    (rootWeight a b u (root i j hij) : F) *
      (rootWeight a b u (root j k hjk) : F) = (rootWeight a b u (root i k hik) : F) := by
  have hh : rootWeight a b u (root i j hij) * rootWeight a b u (root j k hjk) =
      rootWeight a b u (root i k hik) := by
    dsimp [rootWeight,root]
    simp [div_eq_mul_inv,mul_assoc]
  exact congrArg (fun x : Fˣ => (x:F)) hh

end Theory.SpecificGroups.LinearHigher.OddCharacteristicCover