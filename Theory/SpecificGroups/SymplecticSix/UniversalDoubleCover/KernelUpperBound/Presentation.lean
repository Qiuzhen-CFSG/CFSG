module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.FinCases

/-!
# The seven ATLAS relations and their free central extension

Use the seven words in the downloadable Magma presentation `S62G1-P1.M`.
Both of its redundant relations are retained. The commutator convention in
that file is `x⁻¹ y⁻¹ x y`, which is written out below. The central extension
is F/[F,R], with F free on the two generators and R the normal closure of
these seven words. Its map to F/R has central kernel by construction.

This fixes the finite algebraic problem needed for the multiplier upper
bound. It asserts neither that F/R is the matrix group nor that the kernel
on the derived subgroup has order two; these are separate proof obligations.

Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, *ATLAS of Finite Group
Representations*, https://brauer.maths.qmul.ac.uk/Atlas/clas/S62/mag/S62G1-P1.M,
retrieved 8 October 2026. See Aschbacher–Smith I.1.1, printed p.407, for the
universal-cover convention. No code is ported from the local ATLAS project.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation

/-- Magma's commutator convention, retained literally in the sourced words. -/
def sourceCommutator {H : Type*} [Group H] (x y : H) : H := x⁻¹ * y⁻¹ * x * y

/-- The full downloadable presentation, retaining both optional relations. -/
def word {H : Type*} [Group H] (x y : H) : Fin 7 → H :=
  ![x ^ 2, y ^ 7, (x * y) ^ 9, (x * y ^ 2) ^ 12,
    sourceCommutator x (y * x * y * x * y) ^ 2,
    sourceCommutator x y ^ 3, sourceCommutator x (y ^ 2) ^ 2]

theorem map_word {H K : Type*} [Group H] [Group K] (f : H →* K)
    (x y : H) (i : Fin 7) : f (word x y i) = word (f x) (f y) i := by
  fin_cases i <;> simp [word, sourceCommutator]

abbrev Free := FreeGroup Bool

def relator : Fin 7 → Free := word (FreeGroup.of false) (FreeGroup.of true)

abbrev Presented := PresentedGroup (Set.range relator)

def generator (i : Bool) : Presented := PresentedGroup.of i

def relations : Subgroup Free := Subgroup.normalClosure (Set.range relator)

instance relations_normal : relations.Normal := by
  unfold relations
  infer_instance

/-- The projection imposing precisely the seven source words. -/
def toPresented : Free →* Presented := PresentedGroup.mk (Set.range relator)

theorem toPresented_surjective : Function.Surjective toPresented :=
  PresentedGroup.mk_surjective _

@[simp] theorem toPresented_relator (i : Fin 7) : toPresented (relator i) = 1 :=
  PresentedGroup.one_of_mem ⟨i, rfl⟩

@[simp] theorem toPresented_eq_one_iff (x : Free) : toPresented x = 1 ↔ x ∈ relations :=
  PresentedGroup.mk_eq_one_iff

open scoped commutatorElement

/-- Kill commutators with relations, without killing the relations themselves. -/
def centralRelations : Subgroup Free := ⁅(⊤ : Subgroup Free), relations⁆

instance centralRelations_normal : centralRelations.Normal := by
  unfold centralRelations
  infer_instance

abbrev Central := Free ⧸ centralRelations

def toCentral : Free →* Central := QuotientGroup.mk' centralRelations

def centralGenerator (i : Bool) : Central := toCentral (FreeGroup.of i)

/-- The genuine quotient map F/[F,R] → F/R. -/
def centralProjection : Central →* Presented :=
  QuotientGroup.lift centralRelations toPresented (by
    intro x hx
    exact toPresented_eq_one_iff x |>.mpr (Subgroup.commutator_le_right _ _ hx))

@[simp] theorem centralProjection_toCentral (x : Free) :
    centralProjection (toCentral x) = toPresented x := rfl

theorem centralProjection_surjective : Function.Surjective centralProjection := by
  intro x
  obtain ⟨y, rfl⟩ := toPresented_surjective x
  exact ⟨toCentral y, rfl⟩

theorem centralProjection_ker_le_center :
    centralProjection.ker ≤ Subgroup.center Central := by
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective centralRelations x
  have hxR : x ∈ relations := (toPresented_eq_one_iff x).mp hx
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective centralRelations y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) hxR)

/-- The last relator has zero exponent sums and detects the double-cover kernel. -/
def defect : Central := toCentral (relator 6)

theorem defect_mem_kernel : defect ∈ centralProjection.ker := by
  change toPresented (relator 6) = 1
  exact toPresented_relator 6

theorem defect_mem_commutator : defect ∈ commutator Central := by
  have h : sourceCommutator (centralGenerator false) (centralGenerator true ^ 2) ∈
      commutator Central := by
    simpa [sourceCommutator, commutatorElement_def, commutator] using
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        (g₁ := (centralGenerator false)⁻¹) (g₂ := (centralGenerator true ^ 2)⁻¹))
  have hp := (commutator Central).pow_mem h 2
  simpa [defect, relator, map_word, word, centralGenerator, sourceCommutator] using hp

/-- Any evaluation making the seven words central factors through F/[F,R]. -/
def descend {H : Type*} [Group H] (f : Free →* H)
    (hf : ∀ i, f (relator i) ∈ Subgroup.center H) : Central →* H :=
  QuotientGroup.lift centralRelations f (by
    have hR : relations ≤ (Subgroup.center H).comap f := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i, rfl⟩
      exact hf i
    apply Subgroup.commutator_le.mpr
    intro x _ y hy
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hR hy) (f x)))

@[simp] theorem descend_toCentral {H : Type*} [Group H] (f : Free →* H)
    (hf : ∀ i, f (relator i) ∈ Subgroup.center H) (x : Free) :
    descend f hf (toCentral x) = f x := rfl

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
