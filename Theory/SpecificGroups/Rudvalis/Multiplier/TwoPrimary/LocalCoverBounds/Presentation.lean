module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.FinCases

/-!
# A two-generator presentation candidate for the actual Rudvalis max4

The seven words were discovered by GAP on the original ATLAS max4 generators.
`ModelMap` checks them on the certified five-point base. Completeness is a
separate obligation: no identification of the presented group is asserted here.
The central group is literally F/[F,R], where R is their normal closure.

This is the local presentation route to Aschbacher--Smith I.1.3(1), p.407.
See `source/README.md` for the discovery script, marking and attribution.
The free-central construction follows the existing symplectic-six
`UniversalDoubleCover.KernelUpperBound.Presentation` implementation.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation

/-- All seven literal relations, with the original first generator marked. -/
def word {H : Type*} [Group H] (x y : H) : Fin 7 → H :=
  ![x ^ 2, y ^ 3, (x * y⁻¹ * x * y) ^ 4, (y⁻¹ * x) ^ 14,
    ((x * y) * (x * y⁻¹) ^ 3 * (x * y) ^ 3 * (x * y⁻¹) ^ 3 *
      (x * y) * (x * y⁻¹) ^ 2) ^ 2,
    ((y * x) ^ 4 * (y⁻¹ * x) * (y * x) ^ 2 * (y⁻¹ * x) ^ 2) ^ 3,
    ((x * y) ^ 5 * (x * y⁻¹) ^ 3) ^ 4]

theorem map_word {H K : Type*} [Group H] [Group K] (f : H →* K)
    (x y : H) (i : Fin 7) : f (word x y i) = word (f x) (f y) i := by
  fin_cases i <;> simp [word]

abbrev Free := FreeGroup Bool

def relator : Fin 7 → Free := word (FreeGroup.of false) (FreeGroup.of true)

abbrev Presented := PresentedGroup (Set.range relator)

def generator (i : Bool) : Presented := PresentedGroup.of i

def relations : Subgroup Free := Subgroup.normalClosure (Set.range relator)

instance relations_normal : relations.Normal := by
  unfold relations
  infer_instance

/-- The projection imposing precisely the seven words. -/
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

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation
