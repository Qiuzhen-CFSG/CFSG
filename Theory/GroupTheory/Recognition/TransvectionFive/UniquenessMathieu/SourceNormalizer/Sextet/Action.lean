module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Census

/-!
# The additive action on the six exceptional four-groups

An additive symmetry of the 45-point locus permutes the six intrinsic
four-subgroups in its complement. Construct that permutation homomorphism
from the actual images of their coordinate sets. This is the action used
in source 40.4; kernel order and surjectivity are separate assertions.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4, p.218.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)

/-- The additive symmetry group of the six exceptional triples. -/
def symmetryGroup : Subgroup (Equiv.Perm Code) where
  carrier := {f | (∀ x y, f (x ^^^ y) = f x ^^^ f y) ∧
    (∀ x, exceptional (f x) = exceptional x)}
  one_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hp⟩ ⟨hg, hq⟩
    exact ⟨fun x y => by change f (g (x ^^^ y)) = f (g x) ^^^ f (g y); rw [hg, hf],
      fun x => (hp (g x)).trans (hq x)⟩
  inv_mem' := by
    rintro f ⟨hf, hp⟩
    constructor
    · intro x y
      change f.symm (x ^^^ y) = f.symm x ^^^ f.symm y
      apply f.injective
      rw [f.apply_symm_apply, hf, f.apply_symm_apply, f.apply_symm_apply]
    · intro x
      exact (hp (f.symm x)).symm.trans (congrArg exceptional (f.apply_symm_apply x))

theorem mem_symmetryGroup (f : Equiv.Perm Code) : f ∈ symmetryGroup ↔
    (∀ x y, f (x ^^^ y) = f x ^^^ f y) ∧
      (∀ x, exceptional (f x) = exceptional x) := Iff.rfl

theorem symmetry_zero (f : symmetryGroup) : f.val 0 = 0 := by
  have h := f.property.1 0 0
  simpa using h

/-- Every additive symmetry sends each literal four-element subset to another. -/
theorem exists_line_image (f : symmetryGroup) (i : Fin 6) :
    ∃ j : Fin 6, (line i).image f.val = line j := by
  have h := generators_exceptional i
  obtain ⟨j, hj⟩ := exceptional_triple (f.val (generators i).1) (f.val (generators i).2)
    (fun he => generators_distinct i (f.val.injective he))
    ((f.property.2 _).trans h.1) ((f.property.2 _).trans h.2.1)
    (by rw [← f.property.1, f.property.2]; exact h.2.2)
  refine ⟨j, ?_⟩
  simpa only [line, Finset.image_insert, Finset.image_singleton, symmetry_zero,
    f.property.1] using hj

private def move (f : symmetryGroup) (i : Fin 6) : Fin 6 :=
  (exists_line_image f i).choose

private theorem move_image (f : symmetryGroup) (i : Fin 6) :
    line (move f i) = (line i).image f.val :=
  (exists_line_image f i).choose_spec.symm

private theorem move_one (i : Fin 6) : move 1 i = i := by
  apply line_injective
  rw [move_image]
  change (line i).image id = line i
  exact Finset.image_id

private theorem move_mul (f g : symmetryGroup) (i : Fin 6) :
    move (f * g) i = move f (move g i) := by
  apply line_injective
  rw [move_image, move_image, move_image, Finset.image_image]
  rfl

/-- The action on the six four-groups, retaining their original embeddings. -/
def permutation (f : symmetryGroup) : Equiv.Perm (Fin 6) where
  toFun := move f
  invFun := move f⁻¹
  left_inv i := by rw [← move_mul, inv_mul_cancel, move_one]
  right_inv i := by rw [← move_mul, mul_inv_cancel, move_one]

/-- The six-point permutation representation of the actual additive symmetry group. -/
def action : symmetryGroup →* Equiv.Perm (Fin 6) where
  toFun := permutation
  map_one' := Equiv.ext move_one
  map_mul' f g := Equiv.ext (move_mul f g)

/-- The action is defined by the images of the four-groups, not by an abstract group tag. -/
theorem action_line (f : symmetryGroup) (i : Fin 6) :
    line (action f i) = (line i).image f.val := move_image f i

/-- Membership in the represented line is exactly the image of original membership. -/
theorem action_mem_line (f : symmetryGroup) (i : Fin 6) (x : Code) :
    f.val x ∈ line (action f i) ↔ x ∈ line i := by
  rw [action_line, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact f.val.injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
