module

public import Theory.SpecificGroups.Lyons.GebhardtPresentation
public import Theory.GroupTheory.PresentedGroupBounds

/-!+# Double-coset contracts for the Gebhardt presentation

The four nonidentity representatives are the inverses of the conjugating words
`z`, `zdz`, `zdBz`, and `zdcdz` in Gebhardt, Experimental Mathematics 9 (2000),
333–338, Section 3B. This orientation agrees with right cosets `H * r`: a
relation `w⁻¹ * x * w = y`, with `x,y ∈ H`, rewrites `w⁻¹ * x = y * w⁻¹`.

Right multiplication by a local generator preserves a double coset. Thus only
the two signed outer-generator transitions are needed to prove coverage by
these five double cosets. No finiteness or matrix realization is assumed here.
The outer transitions and the finite transversals are separate proof inputs;
this module does not assert that either has been constructed.
-/

namespace Lyons.Gebhardt
@[expose] public section

/-- The source's five candidate right-double-coset representatives. -/
def doubleCosetRepresentative (i : Fin 5) : Presentation :=
  match i.val with
  | 0 => 1
  | 1 => (PresentedGroup.mk relators (word "z"))⁻¹
  | 2 => (PresentedGroup.mk relators (word "zdz"))⁻¹
  | 3 => (PresentedGroup.mk relators (word "zdBz"))⁻¹
  | _ => (PresentedGroup.mk relators (word "zdcdz"))⁻¹

@[simp] theorem doubleCosetRepresentative_zero : doubleCosetRepresentative 0 = 1 := rfl

theorem local_generator_mem (i : Alphabet) (hi : i.val < 4) :
    generator i ∈ localSubgroup :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

/-- The first outer relation, interpreted in the abstract presentation. -/
theorem z_conjugate_a :
    (generator 4)⁻¹ * generator 0 * generator 4 = ((generator 0)⁻¹) ^ 3 := by
  have hm : equationRelator (conjugate (word "a") (word "z")) (word "AAA") ∈
      relators := by
    simp only [relators, Set.mem_ofPred_eq, List.mem_append]
    exact Or.inr (by simp [outerRelators])
  have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem hm
  simpa [conjugate, word, letter, mul_assoc, pow_succ, generator, PresentedGroup.of]
    using he

/-- A certified local transition at the first nontrivial representative. -/
theorem doubleCosetRepresentative_one_mul_a :
    doubleCosetRepresentative 1 * generator 0 =
      ((generator 0)⁻¹) ^ 3 * doubleCosetRepresentative 1 := by
  have he := congrArg (fun x : Presentation => x * (generator 4)⁻¹) z_conjugate_a
  simpa [doubleCosetRepresentative, word, letter, mul_assoc, generator, PresentedGroup.of]
    using he

/-- The remaining transitions after quotienting the representative family by
right multiplication by the local subgroup. Both fields are group equalities. -/
structure OuterDoubleCosetTransitions : Prop where
  step : ∀ (i : Fin 5) (h : localSubgroup),
    ∃ (k : localSubgroup) (j : Fin 5) (l : localSubgroup),
      doubleCosetRepresentative i * h.val * generator 4 =
        k.val * (doubleCosetRepresentative j * l.val)
  inv_step : ∀ (i : Fin 5) (h : localSubgroup),
    ∃ (k : localSubgroup) (j : Fin 5) (l : localSubgroup),
      doubleCosetRepresentative i * h.val * (generator 4)⁻¹ =
        k.val * (doubleCosetRepresentative j * l.val)

/-- The infinite representative family obtained by allowing a local suffix. -/
def doubleCosetGeneratorCover (outer : OuterDoubleCosetTransitions) :
    Subgroup.GeneratorCosetCover localSubgroup generator (Fin 5 × localSubgroup) where
  repr p := doubleCosetRepresentative p.1 * p.2.val
  initial := (0, 1)
  initial_eq := by simp
  step p a := by
    by_cases ha : a.val < 4
    · refine ⟨1, (p.1, p.2 * ⟨generator a, local_generator_mem a ha⟩), ?_⟩
      simp only [Subgroup.coe_one, Subgroup.coe_mul, one_mul, mul_assoc]
    · have he : a = 4 := Fin.ext (by have := a.isLt; omega)
      subst a
      obtain ⟨k, j, l, hh⟩ := outer.step p.1 p.2
      exact ⟨k, (j, l), hh⟩
  inv_step p a := by
    by_cases ha : a.val < 4
    · refine ⟨1, (p.1, p.2 * ⟨(generator a)⁻¹,
        localSubgroup.inv_mem (local_generator_mem a ha)⟩), ?_⟩
      simp only [Subgroup.coe_one, Subgroup.coe_mul, one_mul, mul_assoc]
    · have he : a = 4 := Fin.ext (by have := a.isLt; omega)
      subst a
      obtain ⟨k, j, l, hh⟩ := outer.inv_step p.1 p.2
      exact ⟨k, (j, l), hh⟩

/-- Word induction upgrades the signed transitions to coverage of the entire
abstract presentation by the five candidate double cosets. -/
theorem doubleCosets_cover (outer : OuterDoubleCosetTransitions) (x : Presentation) :
    ∃ (k : localSubgroup) (i : Fin 5) (h : localSubgroup),
      x = k.val * (doubleCosetRepresentative i * h.val) := by
  obtain ⟨k, ⟨i, h⟩, hx⟩ :=
    (doubleCosetGeneratorCover outer).covers closure_range_generator x
  exact ⟨k, i, h, hx⟩

/-- A bounded right-coset transversal for the union of the five double cosets.
This assertion concerns only local suffixes, without asserting that the five
double cosets exhaust the presented group. Repeated representatives are allowed. -/
structure DoubleCosetTransversal where
  repr : Fin 8835156 → Presentation
  initial : Fin 8835156
  initial_eq : repr initial = 1
  cover : ∀ (i : Fin 5) (h : localSubgroup),
    ∃ (k : localSubgroup) (j : Fin 8835156),
      doubleCosetRepresentative i * h.val = k.val * repr j

end
end Lyons.Gebhardt
