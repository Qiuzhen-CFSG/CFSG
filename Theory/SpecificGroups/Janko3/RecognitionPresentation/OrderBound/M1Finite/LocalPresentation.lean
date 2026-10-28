module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.EnumerationSetup
public import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.FinCases

/-!
# A local presentation for the J₃ subgroup order argument

The six words below were discovered in the permutation image of the literal
ATLAS subgroup `M1`. They define a separate presented group. No claim that the
last four words hold in the abstract J₃ presentation is made here.

Two independent inputs suffice for the intended subgroup bound: prove those
four word identities from the original eight relators, and certify a cover of
this local presentation by 2040 cosets of its order-at-most-four cyclic subgroup.
The evaluation homomorphism then surjects onto the literal subgroup generated
by the two supplied elements, transferring both finiteness and the bound 8160.

Source: ATLAS J3G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
Candidate discovery and untrusted certificate data are documented in `source/README.md`.
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation
open Subgroup.CosetWordCertificate

/-- The exact six candidate words, with the original generator order `x,z`. -/
def relator {G : Type*} [Group G] (a c : G) : Fin 6 → G
  | 0 => a ^ 2
  | 1 => c ^ 4
  | 2 => (a * c⁻¹) ^ 6
  | 3 => a * c⁻¹ * a * c * a * (c * a * c) ^ 2 * a * c⁻¹ *
      (c⁻¹ * a) ^ 2 * c * (a * c * a * c⁻¹ ^ 2) ^ 2
  | 4 => (c⁻¹ * a) ^ 2 * c * ((c * a) ^ 2 * c⁻¹ * a) ^ 2 * c⁻¹ * a *
      c⁻¹ ^ 2 * (a * c⁻¹ * a * c) ^ 2 * a
  | 5 => a * c * a * c⁻¹ * a * c * (a * c⁻¹ * a * c * a * c⁻¹) ^ 2 *
      (c⁻¹ * a) ^ 2 * c * (a * c * a * c⁻¹) ^ 2

def Satisfies {G : Type*} [Group G] (a c : G) : Prop :=
  ∀ i : Fin 6, relator a c i = 1

theorem map_relator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a c : G) (i : Fin 6) :
    f (relator a c i) = relator (f a) (f c) i := by
  fin_cases i <;> simp only [relator, map_mul, map_inv, map_pow]

def rels : Set (FreeGroup Bool) :=
  Set.range (relator (FreeGroup.of false) (FreeGroup.of true))

/-- This is a separate six-relator group, not the J₃ presentation or a model. -/
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
def cyclicSubgroup : Subgroup Carrier := Subgroup.zpowers z

/-- Finiteness comes from the fourth-power relation alone. -/
theorem cyclicSubgroup_finite_card :
    Finite cyclicSubgroup ∧ Nat.card cyclicSubgroup ≤ 4 := by
  have hz : z ^ 4 = 1 := generator_satisfies 1
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hz⟩
  refine ⟨hfin.finite_zpowers.to_subtype, ?_⟩
  rw [cyclicSubgroup, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hz

/-- Signed words for the local certificate; `false` is `a` and `true` is `z`. -/
def relatorWord : Fin 6 → Word Bool
  | 0 => [(false, true), (false, true)]
  | 1 => [(true, true), (true, true), (true, true), (true, true)]
  | 2 => [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)]
  | 3 => [(false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true), (true, true), (false, true), (true, false), (true, false)]
  | 4 => [(true, false), (false, true), (true, false), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)]
  | 5 => [(false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)]

/-- The signed words are literally the six algebraic relators. -/
theorem relatorWord_eq {G : Type*} [Group G] (u v : G) (i : Fin 6) :
    eval (fun b : Bool => if b then v else u) (relatorWord i) = relator u v i := by
  fin_cases i <;> simp [relatorWord, eval_cons, relator, pow_succ, mul_assoc]

def relatorWords (r : Nat) : Word Bool :=
  if h : r < 6 then relatorWord ⟨r, h⟩ else []

theorem generator_relators (r : Nat) : eval generator (relatorWords r) = 1 := by
  have he : (fun b : Bool => if b then z else a) = generator := by
    funext b
    cases b <;> rfl
  by_cases hr : r < 6
  · rw [relatorWords, dif_pos hr, ← he, relatorWord_eq]
    exact generator_satisfies ⟨r, hr⟩
  · simp [relatorWords, hr]

/-- Only the positive `z` loop is admitted as a subgroup generator. -/
def allowed (b : Letter Bool) : Bool := decide (b = (true, true))

theorem certificate_valid (D : Definitions Bool) :
    Valid ⟨D.parent, D.letter, relatorWords, allowed⟩ cyclicSubgroup generator
      (D.repr generator) := by
  apply D.valid
  · intro b hb
    have hb' : b = (true, true) := by simpa [allowed] using hb
    subst b
    simp [eval_letter, generator, z, cyclicSubgroup]
  · exact generator_relators

/-- The signed 2040-coset cover is the sole remaining input for the local bound. -/
theorem finite_card_of_cover
    (C : Subgroup.GeneratorCosetCover cyclicSubgroup generator (Fin 2040)) :
    Finite Carrier ∧ Nat.card Carrier ≤ 8160 := by
  let : Finite cyclicSubgroup := cyclicSubgroup_finite_card.1
  obtain ⟨hfin, hcard⟩ := C.finite_card_le generator_generates
  refine ⟨hfin, hcard.trans ?_⟩
  simpa using Nat.mul_le_mul_right 2040 cyclicSubgroup_finite_card.2

/-- A finite local presentation bounds its actual image, with no ambient
finiteness assumption. This is the transfer used by the literal `M1`. -/
theorem closure_finite_card {G : Type*} [Group G] {u v : G}
    (h : Satisfies u v) (hlocal : Finite Carrier ∧ Nat.card Carrier ≤ 8160) :
    Finite (Subgroup.closure ({u, v} : Set G)) ∧
      Nat.card (Subgroup.closure ({u, v} : Set G)) ≤ 8160 := by
  let : Finite Carrier := hlocal.1
  rw [← evaluation_range h]
  have hsurj := (evaluation h).rangeRestrict_surjective
  exact ⟨Finite.of_surjective _ hsurj,
    (Nat.card_le_card_of_surjective _ hsurj).trans hlocal.2⟩

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation

namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite

/-- The exact four missing identities in the original eight-relator group.
This predicate carries no finiteness, model faithfulness or order-bound premise. -/
def RemainingRelations : Prop :=
  ∀ i : Fin 4,
    LocalPresentation.relator x (m1Word x y) ⟨i.val + 2, by omega⟩ = 1

/-- The first two local relations follow already from source relators zero and seven. -/
theorem satisfies_of_remaining (h : RemainingRelations) :
    LocalPresentation.Satisfies x (m1Word x y) := by
  intro i
  fin_cases i
  · exact presentation_satisfies 0
  · exact m1Word_four presentation_satisfies
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite
