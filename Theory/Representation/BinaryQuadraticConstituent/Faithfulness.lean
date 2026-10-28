module

public import Theory.Representation.BinaryQuadraticConstituent

/-!
# Faithfulness on a complement to a singular constituent

The nondegenerate polar form embeds a totally singular summand into the dual
of its complement. An element fixing the complement therefore fixes the
singular summand, hence the whole space; faithfulness kills that element.
No faithfulness of either summand is assumed.

This is the kernel-elimination step in the orthogonal constituent argument of
Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58, printed p.1149.
-/

public section

namespace Representation.BinaryQuadraticConstituent
open Representation Subgroup
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- In a faithful orthogonal action, a complement to a totally singular invariant
subspace is faithful. The cross pairing detects the action on the singular subspace. -/
theorem faithful_of_singular_complement
    (ρ : Representation (ZMod 2) A V) (hf : Function.Injective ρ)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ a v, q (ρ a v) = q v)
    (J L : Subrepresentation ρ) (hc : IsCompl J.toSubmodule L.toSubmodule)
    (hnd : q.polarBilin.Nondegenerate)
    (hsing : ∀ v ∈ J.toSubmodule, q v = 0) :
    Function.Injective L.toRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hL : L.toRepresentation a = 1 := ha
  have hLi : L.toRepresentation a⁻¹ = 1 := by
    have hh := L.toRepresentation.map_mul a⁻¹ a
    rw [inv_mul_cancel, map_one, hL, mul_one] at hh
    exact hh.symm
  have hJ : ∀ x : J.toSubmodule, J.toRepresentation a x = x := by
    intro x
    apply crossPairing_injective ρ q hq J L hc hnd hsing
    have he := LinearMap.congr_fun ((crossPairing ρ q hq J L).isIntertwining' a) x
    change crossPairing ρ q hq J L (J.toRepresentation a x) = _ at he
    rw [he]
    apply LinearMap.ext
    intro y
    change crossPairing ρ q hq J L x (L.toRepresentation a⁻¹ y) = _
    rw [hLi]
    rfl
  have hρ : ρ a = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, y, hxy, _⟩ := Submodule.existsUnique_add_of_isCompl hc v
    have hx : ρ a x.val = x.val := congrArg Subtype.val (hJ x)
    have hy : ρ a y.val = y.val := congrArg Subtype.val (LinearMap.congr_fun hL y)
    change ρ a v = v
    rw [← hxy, map_add, hx, hy]
  exact hf (hρ.trans ρ.map_one.symm)
end Representation.BinaryQuadraticConstituent
