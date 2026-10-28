module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Packed permutations for the Fi23 prefix chain

The two auxiliary subgroups use explicit forward and inverse tables. Checking
one inverse identity suffices, since an injective self-map of a finite type is
surjective. This constructs actual permutations without assuming any group
recognition. The balanced Boolean checker is reused from the Fi23 comparison.

The tables invert the original right-action witnesses, matching CycleEncoding.
Their intended application is the three-point bound for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperData

/-- Read a zero-based letter from a block of 256 fifteen-bit entries. -/
def lookup (blocks : Nat → Nat) (x : Fin 31671) : Fin 31671 :=
  Fin.ofNat 31671 ((blocks (x.val / 256) >>> (15 * (x.val % 256))) % 32768)

/-- A checked left inverse gives both inverse laws on the finite letter set. -/
def permOfLeftInverse (f g : Fin 31671 → Fin 31671)
    (h : Function.LeftInverse g f) : Equiv.Perm (Fin 31671) where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_surjective (Finite.surjective_of_injective h.injective)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperData
