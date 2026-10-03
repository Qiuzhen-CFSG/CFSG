module

public import Theory.SpecificGroups.ReeTwo.Sylow

/-!
# Two additional binary characters for the Ree two Sylow model

The sum of core coordinates for roots 4, 5 and 6 is additive under the
verified core multiplication. It is fixed by both specified complement
generators, so it extends to the full centralizer. Restriction to the Sylow
model gives a nontrivial binary character. Multiplication by the existing
cyclic-four parity character gives another nontrivial character.

These are candidates for the alternative-character route to the q = 2
fusion obstruction. No ambient fusion invariance is asserted. The proofs
use the root actions from Shinoda (1975), (2.3) and the Weyl table, pp. 81--83;
the global motivation is van Beek (2024), Proposition 3.1.
-/

@[expose] public section

namespace ReeTwo
namespace Core

/-- Sum of the coordinates of roots 4, 5 and 6. -/
def binaryCharacter : Core →* FiveFour.Cyclic 2 where
  toFun x := Multiplicative.ofAdd (x.b1 + x.b2 + x.b3)
  map_one' := by decide +kernel
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.b1 + y.b1) + (x.b2 + y.b2) + (x.b3 + y.b3)) =
      Multiplicative.ofAdd (x.b1 + x.b2 + x.b3 + (y.b1 + y.b2 + y.b3))
    congr 1
    ring

private theorem binaryCharacter_a : binaryCharacter.comp a.toMonoidHom = binaryCharacter := by
  apply hom_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    binaryCharacter (a (root i)) = binaryCharacter (root i))

private theorem binaryCharacter_r : binaryCharacter.comp r.toMonoidHom = binaryCharacter := by
  apply hom_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    binaryCharacter (r (root i)) = binaryCharacter (root i))

/-- The entire specified complement fixes the binary core character. -/
theorem binaryCharacter_complement (t : complement) (x : Core) :
    binaryCharacter ((t : MulAut Core) x) = binaryCharacter x := by
  let P (a : MulAut Core) := ∀ x, binaryCharacter (a x) = binaryCharacter x
  have hmul (a b : MulAut Core) (ha : P a) (hb : P b) : P (a * b) := by
    intro x
    exact (ha (b x)).trans (hb x)
  have hpow (a : MulAut Core) (ha : P a) (n : ℕ) : P (a ^ n) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih => exact hmul _ _ ih ha
  have ha : P a := DFunLike.congr_fun binaryCharacter_a
  have hr : P r := DFunLike.congr_fun binaryCharacter_r
  obtain ⟨i, j, rfl⟩ := complement_normal_form t
  exact hmul _ _ (hpow _ (hmul _ _ (hpow _ ha 2) hr) i) (hpow _ ha j) x
end Core

namespace Centralizer

/-- The complement-invariant core character extended to the centralizer. -/
def coreCharacter : Centralizer →* FiveFour.Cyclic 2 where
  toFun x := Core.binaryCharacter x.left
  map_one' := Core.binaryCharacter.map_one
  map_mul' x y := by
    change Core.binaryCharacter (x.left * (x.right : MulAut Core) y.left) = _
    rw [map_mul, Core.binaryCharacter_complement]

@[simp] theorem coreCharacter_root (i : CoreRoot) :
    coreCharacter (root i) = Core.binaryCharacter (Core.root i) := rfl

@[simp] theorem coreCharacter_rootOne : coreCharacter rootOne = 1 :=
  Core.binaryCharacter.map_one
end Centralizer

namespace SylowModel

/-- Restriction of the core character to the concrete Sylow model. -/
def coreCharacter : SylowModel →* FiveFour.Cyclic 2 :=
  Centralizer.coreCharacter.comp embedding

/-- Product of the core character and cyclic-four parity. -/
def mixedCharacter : SylowModel →* FiveFour.Cyclic 2 := coreCharacter * character

@[simp] theorem coreCharacter_root (i : CoreRoot) :
    coreCharacter (root i) = Core.binaryCharacter (Core.root i) := by
  simp [coreCharacter]

@[simp] theorem coreCharacter_rootOne : coreCharacter rootOne = 1 := by
  simp [coreCharacter]

/-- Root 4 detects the core character. -/
theorem coreCharacter_nontrivial : coreCharacter (root 1) ≠ 1 := by
  rw [coreCharacter_root]
  decide +kernel

/-- Root 4 also detects the mixed character. -/
theorem mixedCharacter_nontrivial : mixedCharacter (root 1) ≠ 1 := by
  simpa [mixedCharacter] using coreCharacter_nontrivial

@[simp] theorem mixedCharacter_rootOne :
    mixedCharacter rootOne = character rootOne := by
  simp [mixedCharacter]

end SylowModel

namespace Centralizer

/-- The mixed character also extends over the full centralizer. -/
noncomputable def mixedCharacter : Centralizer →* FiveFour.Cyclic 2 :=
  coreCharacter * character

@[simp] theorem coreCharacter_embedding (g : SylowModel) :
    coreCharacter (SylowModel.embedding g) = SylowModel.coreCharacter g := rfl

@[simp] theorem mixedCharacter_embedding (g : SylowModel) :
    mixedCharacter (SylowModel.embedding g) = SylowModel.mixedCharacter g := by
  simp [mixedCharacter, SylowModel.mixedCharacter]

end Centralizer
end ReeTwo
