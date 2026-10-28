module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.Representation.MathieuCodeRestriction.Actions

/-!
# Native incidence used by the AS91 cycle argument

Lines are the actual octad trios of the fixed Witt design, and planes are its
sextets. Incidence means that every octad of the trio is the union of two
tetrads of the sextet. The last two line types use the radical of the literal
triple-intersection form on the Golay code. Working before quotienting by the
all-one word gives the same membership test for an octad in C(l).

These definitions do not assume any of the finite incidence conclusions of
AS91 §§2–3. Source: Aschbacher–Segev (1991), pp.593–596, especially (3.4).
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise

abbrev Line := Trio
abbrev Plane := Sextet

theorem line_parts_injective : Function.Injective Trio.parts := by
  intro l m he
  cases l
  cases m
  congr

theorem plane_parts_injective : Function.Injective Sextet.parts := by
  intro π σ he
  cases π
  cases σ
  congr

def Incident (l : Line) (π : Plane) : Prop :=
  ∀ A ∈ l.parts, ∃ B ∈ π.parts, ∃ C ∈ π.parts, B ≠ C ∧ A = B ∪ C

def Coplanar (l m : Line) : Prop := ∃ π, Incident l π ∧ Incident m π

/-- The preimage in the twelve-dimensional code of AS91's R(A). -/
def radical (A : Finset (Fin 24)) : Submodule (ZMod 2) MathieuCode.golay where
  carrier := {v | ∀ w : MathieuCode.golay, ∑ i ∈ A, v.val i * w.val i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw u
    simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hv u, hw u, zero_add]
  smul_mem' := by
    intro c v hv w
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum, hv w, mul_zero]

/-- The source sum of the three octad radicals, before dividing by the
common all-one word. -/
def radicalSum (l : Line) : Submodule (ZMod 2) MathieuCode.golay :=
  ⨆ A : {A // A ∈ l.parts}, radical A.val

def octadsInRadicalSum (l m : Line) : Set (Finset (Fin 24)) :=
  {A | A ∈ m.parts ∧ ∃ v : MathieuCode.golay,
    v ∈ radicalSum l ∧ v.val = fun i => if i ∈ A then 1 else 0}

/-- AS91 (3.4)'s five geometric line types. These are predicates on literal
native trios, not arbitrarily chosen relations on ambient lines. -/
def Delta (i : Fin 5) (l m : Line) : Prop :=
  match i.val with
  | 0 => l.parts = m.parts
  | 1 => l.parts ≠ m.parts ∧ (l.parts ∩ m.parts).Nonempty
  | 2 => Disjoint l.parts m.parts ∧ Coplanar l m
  | 3 => (octadsInRadicalSum l m).ncard = 1
  | _ => octadsInRadicalSum l m = ∅

theorem incident_of_parts_eq {l m : Line} (he : l.parts = m.parts)
    {π : Plane} (hl : Incident l π) : Incident m π := by
  intro A hA
  exact hl A (he ▸ hA)

theorem coplanar_symm {l m : Line} (h : Coplanar l m) : Coplanar m l := by
  obtain ⟨π, hl, hm⟩ := h
  exact ⟨π, hm, hl⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
