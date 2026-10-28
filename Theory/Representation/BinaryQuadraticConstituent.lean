module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Field.ZMod

/-!
# Singular irreducible constituents of binary quadratic spaces

An invariant polar form gives an intertwiner from a representation to its
contragredient for the same actor. On a non-self-dual irreducible module it
vanishes. The remaining binary quadratic form is linear; irreducibility and
dimension greater than one force this linear functional to vanish as well.

For two complementary submodules, nondegeneracy of the ambient polar form
and singularity of the first make the cross pairing injective. Equal dimensions
then give an equivariant identification with the dual of the second.

This supplies the orthogonal-space argument used by Aschbacher–Smith,
combined manuscript (1 March 2004), 15.3.58, printed p.1149.
-/

@[expose] public section

open Representation

namespace Representation.BinaryQuadraticConstituent
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- The invariant polar form is an intertwiner for the same actor. -/
def polarIntertwiner (ρ : Representation (ZMod 2) A V)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ a v, q (ρ a v) = q v) :
    IntertwiningMap ρ ρ.dual where
  toLinearMap := q.polarBilin
  isIntertwining' a := by
    ext v w
    change q.polarBilin (ρ a v) w = q.polarBilin v (ρ a⁻¹ w)
    have h : q.polarBilin (ρ a v) (ρ a (ρ a⁻¹ w)) =
        q.polarBilin v (ρ a⁻¹ w) := by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hq]
    simpa only [ρ.self_inv_apply] using h

theorem polar_eq_zero_of_not_self_dual
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ a v, q (ρ a v) = q v)
    (hdual : ¬ Nonempty (Representation.Equiv ρ ρ.dual)) :
    q.polarBilin = 0 := by
  let f := polarIntertwiner ρ q hq
  rcases IsIrreducible.injective_or_eq_zero f with hi | hz
  · have hs : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp : Module.finrank (ZMod 2) V =
          Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V))).mp hi
    exact False.elim (hdual ⟨f.ofBijective ⟨hi, hs⟩⟩)
  · exact congrArg IntertwiningMap.toLinearMap hz

/-- With zero polar form a binary quadratic form is linear. -/
def linearOfPolarZero (q : QuadraticForm (ZMod 2) V) (h : q.polarBilin = 0) :
    V →ₗ[ZMod 2] ZMod 2 where
  toFun := q
  map_add' v w := by
    have hz := LinearMap.congr_fun (LinearMap.congr_fun h v) w
    change q (v + w) - q v - q w = 0 at hz
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)
  map_smul' a v := by
    rw [q.map_smul]
    rw [show a * a = a from (by decide : ∀ a : ZMod 2, a * a = a) a]
    rfl

theorem quadratic_eq_zero_of_not_self_dual
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    [FiniteDimensional (ZMod 2) V]
    (hdim : 1 < Module.finrank (ZMod 2) V)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ a v, q (ρ a v) = q v)
    (hdual : ¬ Nonempty (Representation.Equiv ρ ρ.dual)) : q = 0 := by
  let l := linearOfPolarZero q (polar_eq_zero_of_not_self_dual ρ q hq hdual)
  let f : IntertwiningMap ρ (Representation.trivial (ZMod 2) A (ZMod 2)) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ
      (Representation.trivial (ZMod 2) A (ZMod 2)) l hq
  rcases IsIrreducible.injective_or_eq_zero f with hi | hz
  · have hd := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hi
    simp only [Module.finrank_self] at hd
    omega
  · ext v
    exact congrArg (fun f : IntertwiningMap ρ
      (Representation.trivial (ZMod 2) A (ZMod 2)) => f v) hz

end Representation.BinaryQuadraticConstituent

namespace Representation.BinaryQuadraticConstituent
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V)
variable (q : QuadraticForm (ZMod 2) V) (hq : ∀ a v, q (ρ a v) = q v)

/-- Restrict the polar pairing to two actual invariant subspaces. -/
def crossPairing (J₁ J₂ : Subrepresentation ρ) :
    IntertwiningMap J₁.toRepresentation J₂.toRepresentation.dual where
  toLinearMap := q.polarBilin.compl₁₂ J₁.toSubmodule.subtype J₂.toSubmodule.subtype
  isIntertwining' a := by
    ext v w
    change q.polarBilin (ρ a v.val) w.val = q.polarBilin v.val (ρ a⁻¹ w.val)
    exact LinearMap.congr_fun
      (LinearMap.congr_fun ((polarIntertwiner ρ q hq).isIntertwining' a) v.val) w.val

theorem crossPairing_injective
    (J₁ J₂ : Subrepresentation ρ)
    (hc : IsCompl J₁.toSubmodule J₂.toSubmodule)
    (hnd : q.polarBilin.Nondegenerate)
    (hsing : ∀ v ∈ J₁.toSubmodule, q v = 0) :
    Function.Injective (crossPairing ρ q hq J₁ J₂) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  apply Subtype.ext
  apply hnd.1
  intro w
  obtain ⟨x, y, hxy, _⟩ := Submodule.existsUnique_add_of_isCompl hc w
  rw [← hxy, map_add]
  have hx : q.polarBilin v.val x.val = 0 := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hsing _ v.property, hsing _ x.property,
      hsing _ (J₁.toSubmodule.add_mem v.property x.property), sub_zero]
  have hy : q.polarBilin v.val y.val = 0 := LinearMap.congr_fun hv y
  rw [hx, hy, add_zero]

/-- A nondegenerate polar form pairs equal-dimensional complementary singular
submodules equivariantly for their original, common actor. -/
noncomputable def crossPairingEquiv [FiniteDimensional (ZMod 2) V]
    (J₁ J₂ : Subrepresentation ρ)
    (hc : IsCompl J₁.toSubmodule J₂.toSubmodule)
    (hnd : q.polarBilin.Nondegenerate)
    (hsing : ∀ v ∈ J₁.toSubmodule, q v = 0)
    (hdim : Module.finrank (ZMod 2) J₁.toSubmodule =
      Module.finrank (ZMod 2) J₂.toSubmodule) :
    Representation.Equiv J₁.toRepresentation J₂.toRepresentation.dual := by
  let f := crossPairing ρ q hq J₁ J₂
  have hi : Function.Injective f := crossPairing_injective ρ q hq J₁ J₂ hc hnd hsing
  exact f.ofBijective ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim)).mp hi⟩

theorem crossPairingEquiv_apply [FiniteDimensional (ZMod 2) V]
    (J₁ J₂ : Subrepresentation ρ)
    (hc : IsCompl J₁.toSubmodule J₂.toSubmodule)
    (hnd : q.polarBilin.Nondegenerate)
    (hsing : ∀ v ∈ J₁.toSubmodule, q v = 0)
    (hdim : Module.finrank (ZMod 2) J₁.toSubmodule =
      Module.finrank (ZMod 2) J₂.toSubmodule)
    (v : J₁.toSubmodule) (w : J₂.toSubmodule) :
    crossPairingEquiv ρ q hq J₁ J₂ hc hnd hsing hdim v w =
      q.polarBilin v.val w.val := rfl
end Representation.BinaryQuadraticConstituent
