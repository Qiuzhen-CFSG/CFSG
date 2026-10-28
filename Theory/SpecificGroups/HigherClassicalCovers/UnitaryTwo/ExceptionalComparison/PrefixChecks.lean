module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PrefixData
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Bounded checks of the matrix-word prefixes

Check every adjacent matrix-prefix multiplication and each endpoint. The
unitary relators evaluate to identity; the symplectic relators evaluate to
identity or negative identity, hence vanish in the literal center quotient.
The universal property of a presented group therefore supplies two actual
homomorphisms, with their prescribed values on both generators.

This is a construction step toward PSU₄(2) ≅ PSp₄(3), the comparison used in
Aschbacher–Smith I.1.4(1), printed p.408, and GLS3 §2.2/§2.7. The finite
presentation bound and the matrix-group generation/counting arguments are
separate obligations; relations alone do not establish the comparison.
-/

@[expose] public section
open Matrix Atlas.Algebra
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

def letterValue {G α : Type*} [Group G] (g : α → G) : Option (α × Bool) → G
  | none => 1
  | some (i, b) => if b then g i else (g i)⁻¹

theorem wordValue_eq_range {G α : Type*} [Group G] (g : α → G) (w : List (α × Bool)) :
    FreeGroup.lift g (FreeGroup.mk w) =
      ((List.range w.length).map fun k => letterValue g (w[k]?)).prod := by
  induction w with
  | nil => simp [letterValue, FreeGroup.lift_mk]
  | cons a w ih =>
    rw [FreeGroup.lift_mk, List.map_cons, List.prod_cons, List.length_cons,
      List.prod_range_succ']
    rw [FreeGroup.lift_mk] at ih
    simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ, letterValue,
      Bool.cond_eq_ite] using congrArg (fun z => (if a.2 then g a.1 else (g a.1)⁻¹) * z) ih

theorem prefixProduct {M : Type*} [Monoid M] (f c : ℕ → M) (n : ℕ)
    (h0 : c 0 = 1) (hstep : ∀ k < n, c k * f k = c (k+1)) :
    ((List.range n).map f).prod = c n := by
  induction n with
  | zero => simpa using h0.symm
  | succ n ih =>
    rw [List.prod_range_succ, ih (fun k hk => hstep k (by omega))]
    exact hstep n (by omega)

def unitaryValue : StandardSU →* Matrix (Fin 4) (Fin 4) F :=
  (Units.coeHom _).comp standardForm.specialSubgroup.subtype

def symplecticValue : Sp (ZMod 3) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  (Matrix.symplecticGroup (Fin 2) (ZMod 3)).subtype

def unitaryLetter (r : Fin 11) (k : ℕ) : Matrix (Fin 4) (Fin 4) F :=
  unitaryValue (letterValue unitaryGenerator ((relatorWord r)[k]?))
def symplecticLetter (r : Fin 11) (k : ℕ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  symplecticValue (letterValue symplecticGenerator ((relatorWord r)[k]?))

theorem unitaryPrefix_zero : ∀ r, unitaryPrefix r 0 = 1 := by decide +kernel
theorem unitaryPrefix_step : ∀ (r : Fin 11) (k : Fin 24),
    unitaryPrefix r k.val * unitaryLetter r k.val = unitaryPrefix r (k.val+1) := by
  decide +kernel

theorem unitaryPrefix_end : ∀ r, unitaryPrefix r (relatorWord r).length = 1 := by
  decide +kernel

theorem symplecticPrefix_zero : ∀ r, symplecticPrefix r 0 = 1 := by
  decide +kernel

theorem symplecticPrefix_step : ∀ (r : Fin 11) (k : Fin 24),
    symplecticPrefix r k.val * symplecticLetter r k.val = symplecticPrefix r (k.val+1) := by
  decide +kernel

theorem symplecticPrefix_end : ∀ r,
    symplecticPrefix r (relatorWord r).length = 1 ∨
    symplecticPrefix r (relatorWord r).length = -1 := by
  decide +kernel

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
