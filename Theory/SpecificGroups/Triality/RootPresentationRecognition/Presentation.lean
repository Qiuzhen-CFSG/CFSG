module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.BruhatCollection
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The explicit finite signed triality presentation

Take the free group on the twelve root families over the actual cubic and
fixed fields. The relators are exactly additivity, the fifteen positive
exchanges, the signed simple Weyl actions, the finite braid, and the specified
torus equations. Weyl and torus elements are root words, not extra generators.
The quotient satisfies these equations and its root families generate it.
The abstract Bruhat collector proves that this universal group is finite.

Evaluation into any group satisfying the equations is constructed through the
free-group quotient, preserves all signed roots and defined words, and is
surjective when those roots generate. No model homomorphism or faithfulness is
an input. Verifying the full equations in the genuine model and proving the
model evaluation faithful remain separate steps.

Source: GLS3 2.3.5 and 2.4.5, 2.4.7–8. As in the source, 2.4.8 supplies the
concrete relations; it is not used as a converse presentation theorem.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.Presentation
open Parabolics RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
open ConcreteBruhat.TorusCoordinates
variable {n : ℕ} {hn : 0 < n}
local notation "P" => binaryParameters n hn

inductive Generator (n : ℕ) (hn : 0 < n)
  | short : Bool → Fin 3 → ExtensionField (binaryParameters n hn) → Generator n hn
  | long : Bool → Fin 3 → fixedField (binaryParameters n hn) → Generator n hn

def xShort (s : Bool) (i : Fin 3) (t : ExtensionField P) : FreeGroup (Generator n hn) :=
  FreeGroup.of (.short s i t)
def xLong (s : Bool) (i : Fin 3) (t : fixedField P) : FreeGroup (Generator n hn) :=
  FreeGroup.of (.long s i t)
def nA (t : (ExtensionField P)ˣ) := xShort true 0 t.val * xShort false 0 (t⁻¹).val * xShort true 0 t.val
def nB (t : (fixedField P)ˣ) := xLong true 0 t.val * xLong false 0 (t⁻¹).val * xLong true 0 t.val
def torus (p : TorusParameters n hn) := nA p.1 * nA 1 * (nB p.2 * nB 1)

inductive Relator : FreeGroup (Generator n hn) → Prop
  | short_zero : ∀ s i, Relator ((xShort s i 0) * (1)⁻¹)
  | short_add : ∀ s i a b, Relator ((xShort s i (a+b)) * (xShort s i a * xShort s i b)⁻¹)
  | long_zero : ∀ s i, Relator ((xLong s i 0) * (1)⁻¹)
  | long_add : ∀ s i a b, Relator ((xLong s i (a+b)) * (xLong s i a * xLong s i b)⁻¹)
  | short0_long1 : ∀ s t, Relator ((xShort true 0 s * xLong true 1 t) * (xLong true 1 t * xShort true 0 s)⁻¹)
  | short0_long2 : ∀ s t, Relator ((xShort true 0 s * xLong true 2 t) * (xLong true 2 t * xShort true 0 s)⁻¹)
  | long0_short1 : ∀ s t, Relator ((xLong true 0 s * xShort true 1 t) * (xShort true 1 t * xLong true 0 s)⁻¹)
  | long0_short2 : ∀ s t, Relator ((xLong true 0 s * xShort true 2 t) * (xShort true 2 t * xLong true 0 s)⁻¹)
  | long0_long2 : ∀ s t, Relator ((xLong true 0 s * xLong true 2 t) * (xLong true 2 t * xLong true 0 s)⁻¹)
  | short1_long1 : ∀ s t, Relator ((xShort true 1 s * xLong true 1 t) * (xLong true 1 t * xShort true 1 s)⁻¹)
  | short1_long2 : ∀ s t, Relator ((xShort true 1 s * xLong true 2 t) * (xLong true 2 t * xShort true 1 s)⁻¹)
  | short2_long1 : ∀ s t, Relator ((xShort true 2 s * xLong true 1 t) * (xLong true 1 t * xShort true 2 s)⁻¹)
  | short2_long2 : ∀ s t, Relator ((xShort true 2 s * xLong true 2 t) * (xLong true 2 t * xShort true 2 s)⁻¹)
  | long1_long2 : ∀ s t, Relator ((xLong true 1 s * xLong true 2 t) * (xLong true 2 t * xLong true 1 s)⁻¹)
  | short0_long0 : ∀ s t, Relator ((xShort true 0 s * xLong true 0 t) * (xLong true 0 t * xShort true 0 s * xShort true 1 (s*t.val) *
        xShort true 2 (s * fieldFrobenius P s * t.val) * xLong true 1 (cubicNorm P s * t))⁻¹)
  | short0_short1 : ∀ s t, Relator ((xShort true 0 s * xShort true 1 t) * (xShort true 1 t * xShort true 0 s * xShort true 2 (higherCoefficient P s t) *
        xLong true 1 (cubicTrace P (s * fieldFrobenius P s *
          fieldFrobenius P (fieldFrobenius P t))) *
        xLong true 2 (cubicTrace P (s * fieldFrobenius P t *
          fieldFrobenius P (fieldFrobenius P t))))⁻¹)
  | short0_short2 : ∀ s t, Relator ((xShort true 0 s * xShort true 2 t) * (xShort true 2 t * xShort true 0 s *
        xLong true 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)))⁻¹)
  | short1_short2 : ∀ s t, Relator ((xShort true 1 s * xShort true 2 t) * (xShort true 2 t * xShort true 1 s *
        xLong true 2 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)))⁻¹)
  | long_exchange : ∀ s t, Relator ((xLong true 0 s * xLong true 1 t) * (xLong true 1 t * xLong true 0 s * xLong true 2 (s*t))⁻¹)
  | nA_sq : Relator ((nA 1 ^ 2) * (1)⁻¹)
  | nB_sq : Relator ((nB 1 ^ 2) * (1)⁻¹)
  | braid : Relator (((nA 1 * nB 1) ^ 6) * (1)⁻¹)
  | arms_short0 : ∀ s t, Relator ((nA 1 * xShort s 0 t * (nA 1)⁻¹) * (xShort (!s) 0 t)⁻¹)
  | arms_short1 : ∀ s t, Relator ((nA 1 * xShort s 1 t * (nA 1)⁻¹) * (xShort s 2 (fieldFrobenius P (fieldFrobenius P t)))⁻¹)
  | arms_short2 : ∀ s t, Relator ((nA 1 * xShort s 2 t * (nA 1)⁻¹) * (xShort s 1 (fieldFrobenius P t))⁻¹)
  | arms_long : ∀ s i t, Relator ((nA 1 * xLong s i t * (nA 1)⁻¹) * (xLong s (![1, 0, 2] i) t)⁻¹)
  | central_short : ∀ s i t, Relator ((nB 1 * xShort s i t * (nB 1)⁻¹) * (xShort s (![1, 0, 2] i) t)⁻¹)
  | central_long0 : ∀ s t, Relator ((nB 1 * xLong s 0 t * (nB 1)⁻¹) * (xLong (!s) 0 t)⁻¹)
  | central_long1 : ∀ s t, Relator ((nB 1 * xLong s 1 t * (nB 1)⁻¹) * (xLong s 2 t)⁻¹)
  | central_long2 : ∀ s t, Relator ((nB 1 * xLong s 2 t * (nB 1)⁻¹) * (xLong s 1 t)⁻¹)
  | torus_mul : ∀ p q, Relator ((torus (p*q)) * (torus p * torus q)⁻¹)
  | torus_short : ∀ p s i t, Relator ((torus p * xShort s i t * (torus p)⁻¹) * (xShort s i ((if s then (shortCharacter p i).val else
      ((shortCharacter p i)⁻¹).val) * t))⁻¹)
  | torus_long : ∀ p s i t, Relator ((torus p * xLong s i t * (torus p)⁻¹) * (xLong s i ((if s then (longCharacter p i).val else
      ((longCharacter p i)⁻¹).val) * t))⁻¹)
  | torus_arms : ∀ p, Relator ((nA 1 * torus p * (nA 1)⁻¹) * (torus (fixedUnit P p.2 / p.1, p.2))⁻¹)
  | torus_central : ∀ p, Relator ((nB 1 * torus p * (nB 1)⁻¹) * (torus (p.1, normUnit p.1 / p.2))⁻¹)

def relators : Set (FreeGroup (Generator n hn)) := {w | Relator w}
abbrev Universal (n : ℕ) (hn : 0 < n) := PresentedGroup (relators (n := n) (hn := hn))

def shortHom (s : Bool) (i : Fin 3) : Multiplicative (ExtensionField P) →* Universal n hn where
  toFun a := PresentedGroup.of (.short s i a.toAdd)
  map_one' := by
    exact (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short_zero s i)).trans (map_one _)
  map_mul' a b := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.short_add s i a.toAdd b.toAdd)

def longHom (s : Bool) (i : Fin 3) : Multiplicative (fixedField P) →* Universal n hn where
  toFun a := PresentedGroup.of (.long s i a.toAdd)
  map_one' := by
    exact (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long_zero s i)).trans (map_one _)
  map_mul' a b := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.long_add s i a.toAdd b.toAdd)

def roots : SignedRoots (n := n) (hn := hn) (Universal n hn) where
  positive := ⟨shortHom true, longHom true⟩
  negativeShort := shortHom false
  negativeLong := longHom false

@[simp] theorem mk_short (s : Bool) (i : Fin 3) (t : ExtensionField P) :
    PresentedGroup.mk relators (xShort s i t) = (roots (n := n) (hn := hn)).shortSigned s i t := by cases s <;> rfl
@[simp] theorem mk_long (s : Bool) (i : Fin 3) (t : fixedField P) :
    PresentedGroup.mk relators (xLong s i t) = (roots (n := n) (hn := hn)).longSigned s i t := by cases s <;> rfl
@[simp] theorem mk_nA (t : (ExtensionField P)ˣ) :
    PresentedGroup.mk relators (nA t) = roots.nA t := by
  simp only [nA, map_mul, mk_short]; rfl
@[simp] theorem mk_nB (t : (fixedField P)ˣ) :
    PresentedGroup.mk relators (nB t) = roots.nB t := by
  simp only [nB, map_mul, mk_long]; rfl
@[simp] theorem mk_torus (p : TorusParameters n hn) :
    PresentedGroup.mk relators (torus p) = roots.torus p := by
  simp only [torus, map_mul, mk_nA, mk_nB]; rfl

theorem positiveRelations : (roots (n := n) (hn := hn)).positive.Relations where
  commuting := {
    short0_long1 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short0_long1 s t)
    short0_long2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short0_long2 s t)
    long0_short1 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long0_short1 s t)
    long0_short2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long0_short2 s t)
    long0_long2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long0_long2 s t)
    short1_long1 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short1_long1 s t)
    short1_long2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short1_long2 s t)
    short2_long1 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short2_long1 s t)
    short2_long2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short2_long2 s t)
    long1_long2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long1_long2 s t)
  }
  shortExchange := {
    short0_long0 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short0_long0 s t)
    short0_short1 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short0_short1 s t)
    short0_short2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short0_short2 s t)
    short1_short2 := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.short1_short2 s t)
  }
  longExchange := by
      intro s t
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.long_exchange s t)

theorem relations : (roots (n := n) (hn := hn)).Relations where
  positiveRelations := positiveRelations
  nA_sq := by
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.nA_sq )
  nB_sq := by
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.nB_sq )
  braid := by
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.braid )
  arms_short0 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.arms_short0 _ t)
  arms_short1 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.arms_short1 _ t)
  arms_short2 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.arms_short2 _ t)
  arms_long := by
      intro s i t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.arms_long _ i t)
  central_short := by
      intro s i t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.central_short _ i t)
  central_long0 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.central_long0 _ t)
  central_long1 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.central_long1 _ t)
  central_long2 := by
      intro s t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.central_long2 _ t)
  mul := by
      intro p q
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.torus_mul p q)
  short := by
      intro p s i t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.torus_short p _ i t)
  long := by
      intro p s i t
      cases s <;> exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.torus_long p _ i t)
  arms := by
      intro p
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.torus_arms p)
  central := by
      intro p
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Relator.torus_central p)

variable {Y : Type*} [Group Y]
def assignment (L : SignedRoots (n := n) (hn := hn) Y) : Generator n hn → Y
  | .short s i t => L.shortSigned s i t
  | .long s i t => L.longSigned s i t

@[simp] theorem eval_short (L : SignedRoots (n := n) (hn := hn) Y) (s i t) :
    FreeGroup.lift (assignment L) (xShort s i t) = L.shortSigned s i t := FreeGroup.lift_apply_of
@[simp] theorem eval_long (L : SignedRoots (n := n) (hn := hn) Y) (s i t) :
    FreeGroup.lift (assignment L) (xLong s i t) = L.longSigned s i t := FreeGroup.lift_apply_of
@[simp] theorem eval_nA (L : SignedRoots (n := n) (hn := hn) Y) (t) :
    FreeGroup.lift (assignment L) (nA t) = L.nA t := by
  simp only [nA, map_mul, eval_short]; rfl
@[simp] theorem eval_nB (L : SignedRoots (n := n) (hn := hn) Y) (t) :
    FreeGroup.lift (assignment L) (nB t) = L.nB t := by
  simp only [nB, map_mul, eval_long]; rfl
@[simp] theorem eval_torus (L : SignedRoots (n := n) (hn := hn) Y) (p) :
    FreeGroup.lift (assignment L) (torus p) = L.torus p := by
  simp only [torus, map_mul, eval_nA, eval_nB]; rfl

private theorem eval_relator (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations)
    (w : FreeGroup (Generator n hn)) (hw : Relator w) :
    FreeGroup.lift (assignment L) w = 1 := by
  cases hw with
  | short_zero s i =>
      simp only [map_mul, map_inv, map_one, eval_short]
      exact mul_inv_eq_one.mpr (by cases s <;> exact map_one _)
  | short_add s i a b =>
      simp only [map_mul, map_inv, eval_short]
      exact mul_inv_eq_one.mpr (by cases s <;> exact map_mul _ _ _)
  | long_zero s i =>
      simp only [map_mul, map_inv, map_one, eval_long]
      exact mul_inv_eq_one.mpr (by cases s <;> exact map_one _)
  | long_add s i a b =>
      simp only [map_mul, map_inv, eval_long]
      exact mul_inv_eq_one.mpr (by cases s <;> exact map_mul _ _ _)
  | short0_long1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short0_long1 s t).eq)
  | short0_long2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short0_long2 s t).eq)
  | long0_short1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.long0_short1 s t).eq)
  | long0_short2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.long0_short2 s t).eq)
  | long0_long2 s t =>
      simp only [map_mul, map_inv, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.long0_long2 s t).eq)
  | short1_long1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short1_long1 s t).eq)
  | short1_long2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short1_long2 s t).eq)
  | short2_long1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short2_long1 s t).eq)
  | short2_long2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.short2_long2 s t).eq)
  | long1_long2 s t =>
      simp only [map_mul, map_inv, eval_long]
      exact mul_inv_eq_one.mpr ((R.positiveRelations.commuting.long1_long2 s t).eq)
  | short0_long0 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr (R.positiveRelations.shortExchange.short0_long0 s t)
  | short0_short1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr (R.positiveRelations.shortExchange.short0_short1 s t)
  | short0_short2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr (R.positiveRelations.shortExchange.short0_short2 s t)
  | short1_short2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_long]
      exact mul_inv_eq_one.mpr (R.positiveRelations.shortExchange.short1_short2 s t)
  | long_exchange s t =>
      simp only [map_mul, map_inv, eval_long]
      exact mul_inv_eq_one.mpr (R.positiveRelations.longExchange s t)
  | nA_sq  =>
      simp only [map_mul, map_inv, map_pow, map_one, eval_nA]
      exact mul_inv_eq_one.mpr (R.nA_sq)
  | nB_sq  =>
      simp only [map_mul, map_inv, map_pow, map_one, eval_nB]
      exact mul_inv_eq_one.mpr (R.nB_sq)
  | braid  =>
      simp only [map_mul, map_inv, map_pow, map_one, eval_nA, eval_nB]
      exact mul_inv_eq_one.mpr (R.braid)
  | arms_short0 s t =>
      simp only [map_mul, map_inv, eval_short, eval_nA]
      exact mul_inv_eq_one.mpr (R.arms_short0 s t)
  | arms_short1 s t =>
      simp only [map_mul, map_inv, eval_short, eval_nA]
      exact mul_inv_eq_one.mpr (R.arms_short1 s t)
  | arms_short2 s t =>
      simp only [map_mul, map_inv, eval_short, eval_nA]
      exact mul_inv_eq_one.mpr (R.arms_short2 s t)
  | arms_long s i t =>
      simp only [map_mul, map_inv, eval_long, eval_nA]
      exact mul_inv_eq_one.mpr (R.arms_long s i t)
  | central_short s i t =>
      simp only [map_mul, map_inv, eval_short, eval_nB]
      exact mul_inv_eq_one.mpr (R.central_short s i t)
  | central_long0 s t =>
      simp only [map_mul, map_inv, eval_long, eval_nB]
      exact mul_inv_eq_one.mpr (R.central_long0 s t)
  | central_long1 s t =>
      simp only [map_mul, map_inv, eval_long, eval_nB]
      exact mul_inv_eq_one.mpr (R.central_long1 s t)
  | central_long2 s t =>
      simp only [map_mul, map_inv, eval_long, eval_nB]
      exact mul_inv_eq_one.mpr (R.central_long2 s t)
  | torus_mul p q =>
      simp only [map_mul, map_inv, eval_torus]
      exact mul_inv_eq_one.mpr (R.mul p q)
  | torus_short p s i t =>
      simp only [map_mul, map_inv, eval_short, eval_torus]
      exact mul_inv_eq_one.mpr (R.short p s i t)
  | torus_long p s i t =>
      simp only [map_mul, map_inv, eval_long, eval_torus]
      exact mul_inv_eq_one.mpr (R.long p s i t)
  | torus_arms p =>
      simp only [map_mul, map_inv, eval_nA, eval_torus]
      exact mul_inv_eq_one.mpr (R.arms p)
  | torus_central p =>
      simp only [map_mul, map_inv, eval_nB, eval_torus]
      exact mul_inv_eq_one.mpr (R.central p)

/-- Universal evaluation is constructed solely from the displayed equations. -/
def lift (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) : Universal n hn →* Y :=
  PresentedGroup.toGroup (f := assignment L) (by intro w hw; exact eval_relator L R w hw)

@[simp] theorem lift_short (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) (s i t) :
    lift L R (roots.shortSigned s i t) = L.shortSigned s i t := by
  cases s <;> exact PresentedGroup.toGroup.of _
@[simp] theorem lift_long (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) (s i t) :
    lift L R (roots.longSigned s i t) = L.longSigned s i t := by
  cases s <;> exact PresentedGroup.toGroup.of _


namespace RootMembership
variable {Y : Type*} [Group Y] (L : SignedRoots (n := n) (hn := hn) Y)

theorem short_mem (s : Bool) (i : Fin 3) (t : ExtensionField P) :
    L.shortSigned s i t ∈ L.signedClosure := by
  cases s
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨(i,t),rfl⟩))
  · apply Subgroup.mem_sup_left
    apply Subgroup.subset_closure
    fin_cases i
    · exact ⟨(0,(fun _ => t,0)),rfl⟩
    · exact ⟨(2,(fun _ => t,0)),rfl⟩
    · exact ⟨(3,(fun _ => t,0)),rfl⟩

theorem long_mem (s : Bool) (i : Fin 3) (t : fixedField P) :
    L.longSigned s i t ∈ L.signedClosure := by
  cases s
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨(i,t),rfl⟩))
  · apply Subgroup.mem_sup_left
    apply Subgroup.subset_closure
    fin_cases i
    · exact ⟨(1,(0,fun _ => t)),rfl⟩
    · exact ⟨(4,(0,fun _ => t)),rfl⟩
    · exact ⟨(5,(0,fun _ => t)),rfl⟩

theorem closure_le (H : Subgroup Y)
    (hs : ∀ s i t, L.shortSigned s i t ∈ H) (hl : ∀ s i t, L.longSigned s i t ∈ H) :
    L.signedClosure ≤ H := by
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨i,v⟩,rfl⟩
    fin_cases i <;> first | exact hs true _ _ | exact hl true _ _
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨⟨i,t⟩,rfl⟩ | ⟨⟨i,t⟩,rfl⟩)
    · exact hs false i t
    · exact hl false i t
end RootMembership

/-- The twelve literal root families generate the universal group. -/
theorem generates : (roots (n := n) (hn := hn)).signedClosure = ⊤ := by
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by relators roots.signedClosure _ g
  intro j
  cases j with
  | short s i t =>
      have h := RootMembership.short_mem (roots (n := n) (hn := hn)) s i t
      cases s <;> exact h
  | long s i t =>
      have h := RootMembership.long_mem (roots (n := n) (hn := hn)) s i t
      cases s <;> exact h

/-- Finiteness is proved by the abstract Bruhat collector, not imposed on the presentation. -/
instance finiteUniversal : Finite (Universal n hn) :=
  SignedRoots.finite_of_generated roots relations generates

/-- Evaluation is onto whenever the supplied signed roots generate. -/
theorem lift_surjective (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations)
    (hg : L.signedClosure = ⊤) : Function.Surjective (lift L R) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hg]
  apply RootMembership.closure_le
  · intro s i t
    exact ⟨roots.shortSigned s i t,lift_short L R s i t⟩
  · intro s i t
    exact ⟨roots.longSigned s i t,lift_long L R s i t⟩

@[simp] theorem lift_nA (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) (t) :
    lift L R (roots.nA t) = L.nA t := by
  have hs := lift_short L R true 0 t.val
  have hn' := lift_short L R false 0 (t⁻¹).val
  change lift L R (roots.shortSigned true 0 t.val * roots.shortSigned false 0 (t⁻¹).val *
    roots.shortSigned true 0 t.val) = _
  simp only [map_mul, hs, hn']
  rfl

@[simp] theorem lift_nB (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) (t) :
    lift L R (roots.nB t) = L.nB t := by
  have hs := lift_long L R true 0 t.val
  have hn' := lift_long L R false 0 (t⁻¹).val
  change lift L R (roots.longSigned true 0 t.val * roots.longSigned false 0 (t⁻¹).val *
    roots.longSigned true 0 t.val) = _
  simp only [map_mul, hs, hn']
  rfl

@[simp] theorem lift_torus (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations) (p) :
    lift L R (roots.torus p) = L.torus p := by
  simp only [SignedRoots.torus, SignedRoots.hA, SignedRoots.hB, map_mul, lift_nA, lift_nB]

end Triality.Standard.RootPresentationRecognition.Presentation
