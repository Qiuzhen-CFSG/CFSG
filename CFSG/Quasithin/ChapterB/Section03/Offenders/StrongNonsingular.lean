module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Classification
public import Theory.Representation.BinaryPermutation.EightCoreLine
public import Theory.Representation.BinaryPermutation.EightGeometry

/-!
# Strong offenders fix a nonsingular point of the natural six-space

B.3.2 identifies each strong offender on the natural eight-letter module
with a conjugate of the group of four disjoint transpositions. That group
fixes the class of one of its pairs. The half-weight form makes that class
nonsingular, and conjugation transports it through the same natural action.

Source: Aschbacher--Smith, Proposition B.3.2, printed pp.83--84, combined
manuscript of 1 March 2004. The point is used in the source 12.6.15 argument.
-/

public section
open Subgroup Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation BinaryPermutation.EightNonsingular
open BinaryPermutation.TerminalOrthogonal.Eight

theorem strong_natural_eight_fixes_nonsingular (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : IsStrongOffender (naturalRepresentation (Fin 8)) A) :
    ∃ w : natural (Fin 8), form w ≠ 0 ∧ ∀ a ∈ A, naturalRepresentation (Fin 8) a w = w := by
  let w := coreToNatural (Fin 8) (pair 0 1)
  have hw : form w ≠ 0 := by
    rw [(EightGeometry.nonsingular_core_iff _).mpr
      (.inl (EightCoreLine.pair_weight 0 1 (by decide)))]
    exact one_ne_zero
  have hfix : ∀ a ∈ D 8, naturalRepresentation (Fin 8) a w = w := by
    intro a ha
    change a ∈ Subgroup.closure {g | ∃ i : Fin (8 / 2), i.val < 8 / 2 ∧ g = pairSwap 8 i} at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i,_,rfl⟩ := hg
      have he : coreRepresentation (Fin 8) (pairSwap 8 i) (pair 0 1) = pair 0 1 := by
        fin_cases i <;> decide +kernel
      exact (coreToNatural_equivariant (pairSwap 8 i) (pair 0 1)).symm.trans
        (congrArg (coreToNatural (Fin 8)) he)
    | one => simp
    | mul a b _ _ ha hb => simp only [map_mul,Module.End.mul_apply,hb,ha]
    | inv a _ ha =>
      have he := congrArg (naturalRepresentation (Fin 8) a⁻¹) ha
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at he
      exact he.symm
  obtain ⟨g,rfl⟩ := (isStrongOffender_natural_iff (.inr rfl) A).mp hA
  refine ⟨naturalRepresentation (Fin 8) g w,?_,?_⟩
  · rwa [form_invariant]
  · rintro _ ⟨a,ha,rfl⟩
    change naturalRepresentation (Fin 8) (g*a*g⁻¹) (naturalRepresentation (Fin 8) g w) = _
    rw [←Module.End.mul_apply,←map_mul]
    simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply,hfix a ha]
end CFSG.Quasithin.ChapterB.Offenders
