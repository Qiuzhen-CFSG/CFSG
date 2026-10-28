module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Two-point transport over the binary field

Distinct nonzero binary vectors determine distinct projective points.
The standard two-transitivity of the full linear group on projective
points therefore transports two ordered distinct nonzero vectors exactly.
This is the natural L₃(2) orbit calculation in Aschbacher--Smith 14.7.12,
printed p.1046; no special dimension or matrix enumeration is needed.
-/

public section
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem projective_eq_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk (ZMod 2) v hv = Projectivization.mk (ZMod 2) w hw ↔ v = w := by
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a,ha⟩
    have he : a = 1 := Subsingleton.elim _ _
    simpa [he] using ha.symm
  · rintro rfl
    exact ⟨1,one_smul _ _⟩

/-- The full binary linear group transports ordered distinct nonzero vector pairs. -/
theorem exists_linearEquiv_pair (a b c d : V)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : V ≃ₗ[ZMod 2] V, g a = c ∧ g b = d := by
  have hab' : Projectivization.mk (ZMod 2) a ha ≠ Projectivization.mk (ZMod 2) b hb :=
    fun he => hab ((projective_eq_iff a b ha hb).mp he)
  have hcd' : Projectivization.mk (ZMod 2) c hc ≠ Projectivization.mk (ZMod 2) d hd :=
    fun he => hcd ((projective_eq_iff c d hc hd).mp he)
  obtain ⟨g,hg,hg'⟩ := MulAction.is_two_pretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive (V ≃ₗ[ZMod 2] V)
      (Projectivization (ZMod 2) V) 2) hab' hcd'
  exact ⟨g,(projective_eq_iff _ _ _ _).mp hg,(projective_eq_iff _ _ _ _).mp hg'⟩
end BinaryLinear
