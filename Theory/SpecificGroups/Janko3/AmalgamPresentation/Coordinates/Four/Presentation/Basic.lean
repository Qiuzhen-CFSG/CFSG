module

public import Theory.GroupTheory.CosetWordCertificate
public import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.FinCases

/-!
# The exact second local presentation of the J₃ rank-three amalgam

These are exactly the second block of five relators in
`Scratch/J3AmalgamComparison/Algebra/local-relators.json`, in its original
two-generator order. The first generator has order dividing six. A signed
480-coset cover of that cyclic subgroup gives the order bound 2880.
The evaluation map transfers the bound to any pair satisfying these words,
without assuming that its ambient group is finite.
-/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation
open Subgroup.CosetWordCertificate

/-- The exact second local block, in its original generator order. -/
def relator {G : Type*} [Group G] (a c : G) : Fin 5 → G
  | 0 => c ^ 3
  | 1 => a ^ 6
  | 2 => c * a * c * a * a * c * a * c * a * a
  | 3 => a * c⁻¹ * a⁻¹ * a⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ * a⁻¹ * a⁻¹ * c⁻¹ * a * a
  | 4 => a⁻¹ * c * a⁻¹ * c * a⁻¹ * c * a * c * a⁻¹ * c * a⁻¹ * c⁻¹ * a⁻¹ * a⁻¹

def Satisfies {G : Type*} [Group G] (a c : G) : Prop :=
  ∀ i : Fin 5, relator a c i = 1

theorem map_relator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a c : G) (i : Fin 5) :
    f (relator a c i) = relator (f a) (f c) i := by
  fin_cases i <;> simp only [relator, map_mul, map_inv, map_pow]

def rels : Set (FreeGroup Bool) :=
  Set.range (relator (FreeGroup.of false) (FreeGroup.of true))

/-- The group defined by the second local block of the amalgam. -/
abbrev Carrier := PresentedGroup rels

def a : Carrier := PresentedGroup.of false

def z : Carrier := PresentedGroup.of true

def generator : Bool → Carrier := PresentedGroup.of

theorem generator_satisfies : Satisfies a z := by
  intro i
  change relator ((PresentedGroup.mk rels) (FreeGroup.of false))
    ((PresentedGroup.mk rels) (FreeGroup.of true)) i = 1
  rw [← map_relator (PresentedGroup.mk rels)]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

theorem generator_generates : Subgroup.closure (Set.range generator) = ⊤ :=
  PresentedGroup.closure_range_of rels

/-- A satisfying pair induces the canonical evaluation homomorphism. -/
def evaluation {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) : Carrier →* G :=
  PresentedGroup.toGroup (f := fun t : Bool => if t then v else u) (by
    rintro r ⟨i, rfl⟩
    rw [map_relator]
    simpa only [FreeGroup.lift_apply_of, Bool.false_eq_true, ↓reduceIte] using h i)

@[simp] theorem evaluation_a {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) : evaluation h a = u := PresentedGroup.toGroup.of _

@[simp] theorem evaluation_z {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) : evaluation h z = v := PresentedGroup.toGroup.of _

/-- The evaluation has exactly the intended two-generator subgroup as its image. -/
theorem evaluation_range {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) : (evaluation h).range = Subgroup.closure ({u, v} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    have ht : t ∈ Subgroup.closure (Set.range generator) := by
      rw [generator_generates]
      trivial
    induction ht using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      cases b
      · change evaluation h a ∈ _
        rw [evaluation_a]
        exact Subgroup.subset_closure (by simp)
      · change evaluation h z ∈ _
        rw [evaluation_z]
        exact Subgroup.subset_closure (by simp)
    | one => simp only [map_one]; exact Subgroup.one_mem _
    | mul w t _ _ hw ht => simpa only [map_mul] using Subgroup.mul_mem _ hw ht
    | inv w _ hw => simpa only [map_inv] using Subgroup.inv_mem _ hw
  · apply (Subgroup.closure_le _).mpr
    intro t ht
    rcases ht with rfl | rfl
    · exact ⟨a, evaluation_a h⟩
    · exact ⟨z, evaluation_z h⟩

/-- The subgroup for the small local enumeration. -/
def cyclicSubgroup : Subgroup Carrier := Subgroup.zpowers a

/-- Finiteness comes from the sixth-power relation alone. -/
theorem cyclicSubgroup_finite_card :
    Finite cyclicSubgroup ∧ Nat.card cyclicSubgroup ≤ 6 := by
  have hz : a ^ 6 = 1 := generator_satisfies 1
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hz⟩
  refine ⟨hfin.finite_zpowers.to_subtype, ?_⟩
  rw [cyclicSubgroup, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hz

/-- Signed words for the local certificate; `false` is `a` and `true` is `z`. -/
def relatorWord : Fin 5 → Word Bool
  | 0 => [(true, true), (true, true), (true, true)]
  | 1 => [(false, true), (false, true), (false, true), (false, true), (false, true), (false, true)]
  | 2 => [(true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true)]
  | 3 => [(false, true), (true, false), (false, false), (false, false), (false, false), (true, false), (false, false), (false, false), (false, false), (true, false), (false, true), (false, true)]
  | 4 => [(false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, true), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (false, false)]

/-- The signed words are literally the five algebraic relators. -/
theorem relatorWord_eq {G : Type*} [Group G] (u v : G) (i : Fin 5) :
    eval (fun b : Bool => if b then v else u) (relatorWord i) = relator u v i := by
  fin_cases i <;> simp [relatorWord, eval_cons, relator, pow_succ, mul_assoc]

def relatorWords (r : Nat) : Word Bool :=
  if h : r < 5 then relatorWord ⟨r, h⟩ else []

theorem generator_relators (r : Nat) : eval generator (relatorWords r) = 1 := by
  have he : (fun b : Bool => if b then z else a) = generator := by
    funext b
    cases b <;> rfl
  by_cases hr : r < 5
  · rw [relatorWords, dif_pos hr, ← he, relatorWord_eq]
    exact generator_satisfies ⟨r, hr⟩
  · simp [relatorWords, hr]

/-- Only the positive `a` loop is admitted as a subgroup generator. -/
def allowed (b : Letter Bool) : Bool := decide (b = (false, true))

theorem certificate_valid (D : Definitions Bool) :
    Valid ⟨D.parent, D.letter, relatorWords, allowed⟩ cyclicSubgroup generator
      (D.repr generator) := by
  apply D.valid
  · intro b hb
    have hb' : b = (false, true) := by simpa [allowed] using hb
    subst b
    simp [eval_letter, generator, a, cyclicSubgroup]
  · exact generator_relators

/-- A signed 480-coset cover bounds this presentation. -/
theorem finite_card_of_cover
    (C : Subgroup.GeneratorCosetCover cyclicSubgroup generator (Fin 480)) :
    Finite Carrier ∧ Nat.card Carrier ≤ 2880 := by
  let : Finite cyclicSubgroup := cyclicSubgroup_finite_card.1
  obtain ⟨hfin, hcard⟩ := C.finite_card_le generator_generates
  refine ⟨hfin, hcard.trans ?_⟩
  simpa using Nat.mul_le_mul_right 480 cyclicSubgroup_finite_card.2

/-- A finite local presentation bounds its actual image, with no ambient
finiteness assumption. The bound applies to the literal generated subgroup. -/
theorem closure_finite_card_of_local {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) (hlocal : Finite Carrier ∧ Nat.card Carrier ≤ 2880) :
    Finite (Subgroup.closure ({u, v} : Set G)) ∧
      Nat.card (Subgroup.closure ({u, v} : Set G)) ≤ 2880 := by
  let : Finite Carrier := hlocal.1
  rw [← evaluation_range h]
  have hsurj := (evaluation h).rangeRestrict_surjective
  exact ⟨Finite.of_surjective _ hsurj,
    (Nat.card_le_card_of_surjective _ hsurj).trans hlocal.2⟩

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation
