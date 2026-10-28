module

public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# Three generators of the second M₁₂ parabolic

The marked left quaternion element, right quaternion element, and moving
cubic generate the actual normalizer of the natural four. The two remaining
generators in its existing five-generator word certificate are short words
in these three. Hence the existing complete 192-element certificate proves
homomorphism extensionality on only three images.

These are the literal marked elements of Aschbacher--Smith 14.2.21 and the
M₁₂ branch of F.1.12, printed pp.988 and 263. No new parabolic enumeration
or group presentation is assumed.
-/

@[expose] public section
noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
open SylowEnumeration
set_option maxRecDepth 1000000

/-- The first left quaternion element, first right quaternion element, and
moving cubic in the actual natural-four normalizer. -/
def secondGenerator (i : Fin 3) : secondParabolic :=
  ⟨![leftI, rightI, movingActor] i, by
    fin_cases i
    · exact core_le_secondParabolic ((mem_core _).mpr ⟨.a 1, .a 0, by decide +kernel⟩)
    · exact core_le_secondParabolic ((mem_core _).mpr ⟨.a 0, .a 1, by decide +kernel⟩)
    · exact movingActor_mem⟩

def secondEvaluate : List (Fin 3) → secondParabolic
  | [] => 1
  | i :: is => secondGenerator i * secondEvaluate is

@[simp] theorem secondGenerator_zero : (secondGenerator 0 : M12) = leftI := rfl
@[simp] theorem secondGenerator_one : (secondGenerator 1 : M12) = rightI := rfl
@[simp] theorem secondGenerator_two : (secondGenerator 2 : M12) = movingActor := rfl

private theorem secondEvaluate_leftJ :
    (secondEvaluate [1, 2, 0, 1, 2, 0, 2, 2] : M12) = leftJ := by
  decide +kernel

private theorem secondEvaluate_rightJ :
    (secondEvaluate [2, 0, 2, 2, 0, 2] : M12) = rightJ := by
  decide +kernel

private def localGeneratorWord (i : Fin 5) : List (Fin 3) :=
  ![[0], [1, 2, 0, 1, 2, 0, 2, 2], [1], [2, 0, 2, 2, 0, 2], [2]] i

private theorem localGenerator_eq_secondEvaluate (i : Fin 5) :
    localGenerator i = (secondEvaluate (localGeneratorWord i) : M12) := by
  fin_cases i
  · change leftI = (secondGenerator 0 * 1 : secondParabolic)
    rw [mul_one]
    rfl
  · exact secondEvaluate_leftJ.symm
  · change rightI = (secondGenerator 1 * 1 : secondParabolic)
    rw [mul_one]
    rfl
  · exact secondEvaluate_rightJ.symm
  · change movingActor = (secondGenerator 2 * 1 : secondParabolic)
    rw [mul_one]
    rfl

private theorem secondEvaluate_append (u v : List (Fin 3)) :
    secondEvaluate (u ++ v) = secondEvaluate u * secondEvaluate v := by
  induction u with
  | nil => simp only [List.nil_append, secondEvaluate, one_mul]
  | cons i w ih => simp only [List.cons_append, secondEvaluate, ih, mul_assoc]

private theorem secondEvaluate_word (w : List (Fin 5)) :
    ∃ v : List (Fin 3), (secondEvaluate v : M12) = localWord w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons i w ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨localGeneratorWord i ++ v, ?_⟩
    rw [secondEvaluate_append]
    change (secondEvaluate (localGeneratorWord i) : M12) *
      (secondEvaluate v : M12) = localGenerator i * localWord w
    rw [← localGenerator_eq_secondEvaluate, hv]

private theorem secondEvaluate_surjective : Function.Surjective secondEvaluate := by
  intro x
  have h : (x : M12).val ∈ wordCarrier :=
    (mem_wordCarrier_iff _).mpr
      ⟨(mem_M12_iff_preservesBlocks _).mp x.val.property,
        (mem_secondParabolic_iff _).mp x.property⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have he : wordElement i = (x : M12) := Subtype.ext hi
  obtain ⟨v, hv⟩ := secondEvaluate_word (wordTable[i.val]'(by rw [wordTable_size]; exact i.isLt))
  refine ⟨v, ?_⟩
  apply Subtype.ext
  exact hv.trans he

/-- Homomorphisms out of the actual second parabolic are determined by its
three marked generator images. -/
theorem second_hom_ext {G : Type*} [Group G]
    (f g : secondParabolic →* G)
    (h : ∀ i : Fin 3, f (secondGenerator i) = g (secondGenerator i)) : f = g := by
  have hw (w : List (Fin 3)) : f (secondEvaluate w) = g (secondEvaluate w) := by
    induction w with
    | nil => simp only [secondEvaluate, map_one]
    | cons i w ih => simp only [secondEvaluate, map_mul, h, ih]
  apply MonoidHom.ext
  intro x
  obtain ⟨w, rfl⟩ := secondEvaluate_surjective x
  exact hw w

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
