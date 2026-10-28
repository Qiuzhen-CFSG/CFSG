module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Data
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Executable tests for the concrete place certificates

The packed point maps are already certified against the Parrott generators.
The first test checks commutation with the marked involution. The second
checks that conjugation sends both generators of the marked four-group
into its four explicit elements. Equalities are tested at the three points
0, 1, 2, which form a certified base for the Atlas group.

This module defines the tests and identifies the evaluated words. Their
equivalence with place membership is a separate mathematical obligation.
Source: Parrott (1972), p.683; RelativeParabolicNormalizers/FirstCentralizer
and SecondNormalizer identify the relevant intrinsic subgroups.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
open OuterOddSubgroups.OverlapCentralizers

/-- Certified packed permutations in the original generator order. -/
def fastAssignment : ParrottGenerator → Equiv.Perm (Fin 1600)
  | .r1 => Packed.perm 0
  | .r8 => Packed.perm 1
  | .s1 => Packed.perm 2
  | .s2 => Packed.perm 3
  | .s3 => Packed.perm 4
  | .s4 => Packed.perm 5
  | .s5 => Packed.perm 6
  | .s6 => Packed.perm 7
  | .s7 => Packed.perm 8
  | .s8 => Packed.perm 9

theorem fastAssignment_eq (s : ParrottGenerator) :
    fastAssignment s = (atlas1600ParrottAssignment s).val := by
  rw [atlas1600ParrottAssignment_val]
  cases s <;> simp [fastAssignment, Packed.perm_eq, Packed.generator,
    Atlas1600ParrottData.permutation]

/-- Packed evaluation of a place's literal conjugating word. -/
def fastConjugator (j : Fin 38) : Equiv.Perm (Fin 1600) :=
  ((placeWord j).map fastAssignment).prod

private theorem val_prod (l : List Atlas1600Group) :
    l.prod.val = (l.map (fun x : Atlas1600Group => x.val)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change a.val * l.prod.val = a.val * (l.map (fun x : Atlas1600Group => x.val)).prod
      rw [ih]

theorem fastConjugator_eq (j : Fin 38) :
    fastConjugator j = (placeConjugator j).val := by
  rw [fastConjugator, placeConjugator, val_prod, List.map_map]
  rw [show fastAssignment = (fun s => (atlas1600ParrottAssignment s).val) from
    funext fastAssignment_eq]
  rfl

/-- Packed evaluation with the same mixed-radix convention. -/
def fastNormalForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  fastAssignment .s1 ^ (n.val % 2) *
    fastAssignment .s2 ^ (n.val / 2 % 2) *
    fastAssignment .s3 ^ (n.val / 4 % 4) *
    fastAssignment .s4 ^ (n.val / 16 % 2) *
    fastAssignment .s5 ^ (n.val / 32 % 4) *
    fastAssignment .s6 ^ (n.val / 128 % 2) *
    fastAssignment .s7 ^ (n.val / 256 % 4) *
    fastAssignment .s8 ^ (n.val / 1024 % 2)

theorem fastNormalForm_eq (n : Fin 2048) :
    fastNormalForm n = (atlas1600SylowTwoNormalForm n).val := by
  simp only [fastNormalForm, fastAssignment_eq, atlas1600SylowTwoNormalForm_val,
    atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]

/-- Packed evaluation of a representative row. -/
def rowPerm (r : Row) : Equiv.Perm (Fin 1600) :=
  let j : Fin 38 := ⟨r.1 % 38, Nat.mod_lt _ (by decide)⟩
  let n : Fin 2048 := ⟨r.1 / 38 % 2048, Nat.mod_lt _ (by decide)⟩
  let rotation := if j.val < 17 then fastAssignment .s1 * fastAssignment .r1
    else fastAssignment .s8 * fastAssignment .r8
  let w := fastConjugator j
  w * (fastNormalForm n * rotation ^ (r.1 / (38 * 2048))) * w⁻¹

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : Nat) : (x ^ n).val = x.val ^ n := rfl

theorem rowPerm_eq (r : Row) : rowPerm r = (rowElement r).val := by
  simp only [rowPerm, rowElement, fastConjugator_eq, fastNormalForm_eq,
    fastAssignment_eq, val_mul, val_inv, val_pow]
  split_ifs <;> rfl

/-- Comparison at the three certified base points. -/
def sameBase (a b : Equiv.Perm (Fin 1600)) : Bool :=
  (a 0 == b 0) && (a 1 == b 1) && (a 2 == b 2)

/-- The marked central involution as a packed permutation. -/
def centralPerm : Equiv.Perm (Fin 1600) := fastAssignment .s1 * fastAssignment .s5 ^ 2

/-- The second generator of the marked four-group. -/
def matePerm : Equiv.Perm (Fin 1600) :=
  fastAssignment .s1 * fastAssignment .s2 * fastAssignment .s3 ^ 2

/-- Test whether conjugation by g sends z into the marked four-group.
Writing g*z = h*g avoids evaluation of the inverse of g. -/
def centerImageTest (g z : Equiv.Perm (Fin 1600)) : Bool :=
  sameBase (g * z) g || sameBase (g * z) (centralPerm * g) ||
    sameBase (g * z) (matePerm * g) || sameBase (g * z) (centralPerm * matePerm * g)

/-- A three-point test for membership in one literal conjugate parabolic. -/
def placeTest (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : Bool :=
  let w := fastConjugator j
  let a := w⁻¹ * g * w
  if j.val < 17 then sameBase (a * centralPerm) (centralPerm * a)
  else centerImageTest a centralPerm && centerImageTest a matePerm

/-- The two candidate masks share a listed place. -/
def sharesPlace (t : Fin 18) (a b : Row) : Bool :=
  (placePattern t).any (fun j => rowMember a j && rowMember b j)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
