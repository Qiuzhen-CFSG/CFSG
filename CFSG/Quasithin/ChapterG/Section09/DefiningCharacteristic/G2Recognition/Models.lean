module

public import Theory.Representation.G2Natural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finiteness

/-!
# The binary actions used in G.9.3(10)

These are scalar restrictions of the actual trace-zero split-octonion quotient
action. The full group and its commutator subgroup have separate actions,
including at the binary field. The tower formula computes the binary degree
as six times the field degree, for an arbitrary finite field witness.

This module constructs the target actions; recognition of arbitrary irreducible
representations is a separate obligation.

Source: Aschbacher--Smith, G.9.3(10), printed pp.354,356--357; the natural
module convention is the one in `Theory.Representation.G2Natural`.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

attribute [local instance] ZMod.algebra

variable (F : Type*) [Field F] [CharP F 2]

/-- The genuine natural G₂ action restricted to the binary field. -/
def naturalBinary : Representation (ZMod 2) (Atlas.G2.Model F)
    (Atlas.G2.Natural.Space F) :=
  Representation.restrictScalars (Atlas.G2.Natural.action F)

/-- The restriction to the actual derived subgroup, including G₂(2)′. -/
def derivedNaturalBinary : Representation (ZMod 2) (commutator (Atlas.G2.Model F))
    (Atlas.G2.Natural.Space F) :=
  Representation.restrictScalars (Atlas.G2.Natural.derivedAction F)

@[simp] theorem naturalBinary_apply (g : Atlas.G2.Model F)
    (v : Atlas.G2.Natural.Space F) :
    naturalBinary F g v = Atlas.G2.Natural.action F g v := rfl

@[simp] theorem derivedNaturalBinary_apply (g : commutator (Atlas.G2.Model F))
    (v : Atlas.G2.Natural.Space F) :
    derivedNaturalBinary F g v = naturalBinary F g.val v := rfl

/-- The field cardinality, rather than a chosen field label, determines the
binary dimension of the octonion quotient. -/
theorem naturalBinary_degree [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (Atlas.G2.Natural.Space F) = 6 * n := by
  let : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) F = 2 ^ n
    rw [← hF]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  rw [← Module.finrank_mul_finrank (ZMod 2) F (Atlas.G2.Natural.Space F),
    hd, Atlas.G2.Natural.finrank_space]
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
