module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Cells
public import Mathlib.Algebra.CharP.Two

/-!
# A negative simple root in every nonidentity G₂ Weyl cell

For each of the eleven nonidentity Weyl representatives, one displayed
positive root is carried to a negative simple root. The identities are checked
on the eight octonion coordinates in characteristic two. They use parameter
one, so no choice of a nonzero field scalar is needed.

This is the root-descent step for the larger-field argument on
Aschbacher–Smith, printed p.1144. Coordinate formulas are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.SolvableSylowPlacement
open Explicit
variable {F : Type*} [Field F]

private def descentRoot (i : Fin 12) : Model F :=
  ![rootA 1, rootE 1, rootF 1, rootB 1, rootD 1, rootA 1,
    rootC 1, rootA 1, rootC 1, rootB 1, rootD 1, rootE 1] i

private theorem descentRoot_mem (i : Fin 12) : descentRoot (F := F) i ∈ unipotent := by
  fin_cases i <;> apply Subgroup.subset_closure <;> simp [descentRoot]

private theorem descent_conjugate_1 :
    weylRep 1 * descentRoot (F := F) 1 * (weylRep 1)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  rfl

private theorem descent_conjugate_2 :
    weylRep 2 * descentRoot (F := F) 2 * (weylRep 2)⁻¹ =
      weylS * rootF 1 * weylS⁻¹ := by
  rfl

variable [CharP F 2]

private theorem descent_conjugate_3 :
    weylRep 3 * descentRoot (F := F) 3 * (weylRep 3)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootB, rootBEquiv, rootBLinear, rootBApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_4 :
    weylRep 4 * descentRoot (F := F) 4 * (weylRep 4)⁻¹ =
      weylS * rootF 1 * weylS⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootD, rootDEquiv, rootDLinear, rootDApply,
      rootF, rootFEquiv, rootFLinear, rootFApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_5 :
    weylRep 5 * descentRoot (F := F) 5 * (weylRep 5)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootA, rootAEquiv, rootALinear, rootAApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_6 :
    weylRep 6 * descentRoot (F := F) 6 * (weylRep 6)⁻¹ =
      weylS * rootF 1 * weylS⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootC, rootCEquiv, rootCLinear, rootCApply,
      rootF, rootFEquiv, rootFLinear, rootFApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]
  ac_rfl

private theorem descent_conjugate_7 :
    weylRep 7 * descentRoot (F := F) 7 * (weylRep 7)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootA, rootAEquiv, rootALinear, rootAApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_8 :
    weylRep 8 * descentRoot (F := F) 8 * (weylRep 8)⁻¹ =
      weylS * rootF 1 * weylS⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootC, rootCEquiv, rootCLinear, rootCApply,
      rootF, rootFEquiv, rootFLinear, rootFApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]
  ac_rfl

private theorem descent_conjugate_9 :
    weylRep 9 * descentRoot (F := F) 9 * (weylRep 9)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootB, rootBEquiv, rootBLinear, rootBApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_10 :
    weylRep 10 * descentRoot (F := F) 10 * (weylRep 10)⁻¹ =
      weylS * rootF 1 * weylS⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootD, rootDEquiv, rootDLinear, rootDApply,
      rootF, rootFEquiv, rootFLinear, rootFApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

private theorem descent_conjugate_11 :
    weylRep 11 * descentRoot (F := F) 11 * (weylRep 11)⁻¹ =
      weylR * rootE 1 * weylR⁻¹ := by
  simp only [weylRep, descentRoot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      CharTwo.neg_eq, CharTwo.sub_eq_add]

/-- Each nonidentity Weyl representative takes a positive-root element to
one of the two opposite simple-root elements at parameter one. -/
theorem exists_negative_simple_conjugate (i : Fin 12) (hi : i ≠ 0) :
    ∃ x ∈ unipotent (K := F),
      weylRep i * x * (weylRep i)⁻¹ = weylR * rootE 1 * weylR⁻¹ ∨
      weylRep i * x * (weylRep i)⁻¹ = weylS * rootF 1 * weylS⁻¹ := by
  refine ⟨descentRoot i, descentRoot_mem i, ?_⟩
  fin_cases i
  · exact (hi rfl).elim
  · exact Or.inl descent_conjugate_1
  · exact Or.inr descent_conjugate_2
  · exact Or.inl descent_conjugate_3
  · exact Or.inr descent_conjugate_4
  · exact Or.inl descent_conjugate_5
  · exact Or.inr descent_conjugate_6
  · exact Or.inl descent_conjugate_7
  · exact Or.inr descent_conjugate_8
  · exact Or.inl descent_conjugate_9
  · exact Or.inr descent_conjugate_10
  · exact Or.inl descent_conjugate_11

/-- The opposite simple root is the first reflection of the alternating word:
odd published indices start with `R`, and nonzero even indices start with `S`.
Retaining this marking allows a subgroup to remove the first reflection and
repeat the descent on the shorter word. -/
theorem exists_negative_simple_conjugate_with_parity (i : Fin 12) (hi : i ≠ 0) :
    ∃ x ∈ unipotent (K := F),
      (i.val % 2 = 1 ∧
        weylRep i * x * (weylRep i)⁻¹ = weylR * rootE 1 * weylR⁻¹) ∨
      (i.val % 2 = 0 ∧
        weylRep i * x * (weylRep i)⁻¹ = weylS * rootF 1 * weylS⁻¹) := by
  refine ⟨descentRoot i, descentRoot_mem i, ?_⟩
  fin_cases i
  · exact (hi rfl).elim
  · exact Or.inl ⟨rfl, descent_conjugate_1⟩
  · exact Or.inr ⟨rfl, descent_conjugate_2⟩
  · exact Or.inl ⟨rfl, descent_conjugate_3⟩
  · exact Or.inr ⟨rfl, descent_conjugate_4⟩
  · exact Or.inl ⟨rfl, descent_conjugate_5⟩
  · exact Or.inr ⟨rfl, descent_conjugate_6⟩
  · exact Or.inl ⟨rfl, descent_conjugate_7⟩
  · exact Or.inr ⟨rfl, descent_conjugate_8⟩
  · exact Or.inl ⟨rfl, descent_conjugate_9⟩
  · exact Or.inr ⟨rfl, descent_conjugate_10⟩
  · exact Or.inl ⟨rfl, descent_conjugate_11⟩

end Atlas.G2.SolvableSylowPlacement
