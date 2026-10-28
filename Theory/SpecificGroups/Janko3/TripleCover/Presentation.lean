module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# A central cubic presentation above the J₃ presentation

We use the seven relators of ATLAS `3J3G1-P1`, together with the explicit
relations saying that `z = (x*y)^19` is central and has cube one. This defines
a group, not an assertion that it is already the triple cover. Its perfectness
follows from the exponent sums of the sixth and seventh relators. Its quotient
by `⟨z⟩` has the original eight-relator J₃ presentation.

The model projection and the kernel calculation are in `Projection`. A matrix
representation detecting `z` and faithfulness of the original J₃ presentation
are independent inputs to the final construction.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/3J3G1-P1 .
All words use the same multiplication and inverse convention as
`RecognitionPresentation.relator`.
-/

namespace Sporadic.Janko3.TripleCover

open Subgroup

/-- The seven ATLAS cover relators and three central cubic relations. -/
@[expose] public def relator {G : Type*} [Group G] (a b : G) : Fin 10 → G
  | 0 => RecognitionPresentation.relator a b 0
  | 1 => RecognitionPresentation.relator a b 1
  | 2 => RecognitionPresentation.relator a b 2
  | 3 => RecognitionPresentation.relator a b 4
  | 4 => RecognitionPresentation.relator a b 5
  | 5 => RecognitionPresentation.relator a b 6
  | 6 => RecognitionPresentation.relator a b 7 * (a * b) ^ 19
  | 7 => ((a * b) ^ 19) ^ 3
  | 8 => (a * b) ^ 19 * a * ((a * b) ^ 19)⁻¹ * a⁻¹
  | 9 => (a * b) ^ 19 * b * ((a * b) ^ 19)⁻¹ * b⁻¹

public theorem map_relator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 10) :
    f (relator a b i) = relator (f a) (f b) i := by
  fin_cases i <;> simp only [relator, RecognitionPresentation.map_relator,
    map_mul, map_inv, map_pow]

/-- Literal word identities, without any assertion about the generated group. -/
@[expose] public def Satisfies {G : Type*} [Group G] (a b : G) : Prop :=
  ∀ i : Fin 10, relator a b i = 1

@[expose] public def rels : Set (FreeGroup Bool) :=
  Set.range (relator (FreeGroup.of false) (FreeGroup.of true))

/-- The candidate cover carrier. Finiteness and a nontrivial kernel are proved
separately, not included in its definition. -/
public abbrev Presentation := PresentedGroup rels

@[expose] public def x : Presentation := PresentedGroup.of false
@[expose] public def y : Presentation := PresentedGroup.of true
@[expose] public def z : Presentation := (x * y) ^ 19

public theorem presentation_satisfies : Satisfies x y := by
  intro i
  change relator ((PresentedGroup.mk rels) (FreeGroup.of false))
    ((PresentedGroup.mk rels) (FreeGroup.of true)) i = 1
  rw [← map_relator (PresentedGroup.mk rels)]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- Evaluation at any pair satisfying all ten literal identities. -/
@[expose] public def evaluation {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : Presentation →* G :=
  PresentedGroup.toGroup (f := fun t : Bool => if t then b else a) (by
    rintro r ⟨i, rfl⟩
    rw [map_relator]
    simpa only [FreeGroup.lift_apply_of, Bool.false_eq_true, ↓reduceIte] using h i)

@[simp] public theorem evaluation_x {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : evaluation h x = a := PresentedGroup.toGroup.of _

@[simp] public theorem evaluation_y {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : evaluation h y = b := PresentedGroup.toGroup.of _

@[simp] public theorem evaluation_z {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : evaluation h z = (a * b) ^ 19 := by
  simp only [z, map_pow, map_mul, evaluation_x, evaluation_y]

/-- A witness representation detecting the marked scalar proves that the
central cubic generator survives in the abstract presentation. -/
public theorem z_ne_one_of_representation {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) (hne : (a * b) ^ 19 ≠ 1) : z ≠ 1 := by
  intro hz
  apply hne
  simpa only [evaluation_z, map_one] using congrArg (evaluation h) hz

public theorem x_sq : x ^ 2 = 1 := presentation_satisfies 0
public theorem y_cube : y ^ 3 = 1 := presentation_satisfies 1
public theorem z_cube : z ^ 3 = 1 := presentation_satisfies 7

public theorem z_mul_x : z * x = x * z := by
  have h : z * x * z⁻¹ * x⁻¹ = 1 := presentation_satisfies 8
  have h' : z * x * z⁻¹ = x := eq_of_mul_inv_eq_one h
  exact (mul_inv_eq_iff_eq_mul).mp h'

public theorem z_mul_y : z * y = y * z := by
  have h : z * y * z⁻¹ * y⁻¹ = 1 := presentation_satisfies 9
  have h' : z * y * z⁻¹ = y := eq_of_mul_inv_eq_one h
  exact (mul_inv_eq_iff_eq_mul).mp h'

public theorem z_mem_center : z ∈ center Presentation := by
  apply mem_center_iff.mpr
  intro g
  have h : g ∈ centralizer ({z} : Set Presentation) := by
    apply PresentedGroup.generated_by rels
    intro t
    cases t
    · exact mem_centralizer_singleton_iff.mpr z_mul_x.symm
    · exact mem_centralizer_singleton_iff.mpr z_mul_y.symm
  exact mem_centralizer_singleton_iff.mp h

public theorem zpowers_z_le_center : zpowers z ≤ center Presentation :=
  zpowers_le.mpr z_mem_center

public instance central_cyclic_normal : (zpowers z).Normal := by
  constructor
  intro g hg a
  have h := mem_center_iff.mp (zpowers_z_le_center hg) a
  simpa only [h, mul_assoc, mul_inv_cancel, mul_one] using hg

private theorem generators_trivial_in_commutative
    {G : Type*} [CommGroup G] {a b : G} (h : Satisfies a b) : a = 1 ∧ b = 1 := by
  have ha : a ^ 2 = 1 := h 0
  have hb : b ^ 3 = 1 := h 1
  have h6 : a ^ 25 * b ^ 3 = 1 := by
    calc
      a ^ 25 * b ^ 3 = relator a b 5 := by
        dsimp [relator, RecognitionPresentation.relator]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_pow, ofMul_inv]
        abel
      _ = 1 := h 5
  have ha1 : a = 1 := by
    have he : a ^ 25 * b ^ 3 = (a ^ 2) ^ 12 * a * b ^ 3 := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow]
      abel
    rw [he, ha, hb, one_pow, one_mul, mul_one] at h6
    exact h6
  have h7 : a ^ 47 * b ^ 31 = 1 := by
    calc
      a ^ 47 * b ^ 31 = relator a b 6 := by
        dsimp [relator, RecognitionPresentation.relator]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_pow, ofMul_inv]
        abel
      _ = 1 := h 6
  have hb1 : b = 1 := by
    have he : a ^ 47 * b ^ 31 = a ^ 47 * (b ^ 3) ^ 10 * b := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow]
      abel
    rw [he, ha1, hb, one_pow, one_pow, one_mul, one_mul] at h7
    exact h7
  exact ⟨ha1, hb1⟩

/-- The candidate is perfect before any finiteness or model-recognition input.
The two long ATLAS relators kill both generators in its abelianization. -/
public instance presentation_perfect : Group.IsPerfect Presentation := by
  let f : Presentation →* Abelianization Presentation := Abelianization.of
  have h : Satisfies (f x) (f y) := by
    intro i
    rw [← map_relator, presentation_satisfies, map_one]
  obtain ⟨hx, hy⟩ := generators_trivial_in_commutative h
  constructor
  apply top_unique
  intro g _
  rw [← Abelianization.ker_of]
  apply PresentedGroup.generated_by rels
  intro t
  cases t
  · exact hx
  · exact hy

end Sporadic.Janko3.TripleCover
