module

public import Theory.Representation.BinaryPermutation
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Distinguishing the two four-dimensional binary A₅ modules

The three-cycle (0 1 2) fixes the nonzero even vector supported on the last
two letters of the five-point permutation module. In contrast, every
order-three matrix in SL₂ over a field of characteristic two fixes only zero
on its natural plane. Thus no faithful identification of the acting groups
can identify these modules, even as additive groups with an action.

In particular this distinguishes the natural binary A₅ module from the
natural SL₂(4) module viewed over F₂. This is the chief-factor obstruction
used twice in Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed p.1187. Constructing those chief factors in
the six-dimensional ambient action is a separate argument.
-/

public section

namespace BinaryPermutation.AlternatingFiveLinearTwo

open Matrix
open scoped MatrixGroups

private def cubic : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private def fixedVector : core (Fin 5) :=
  ⟨![0, 0, 0, 1, 1], by
    change (∑ i : Fin 5, (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2) i) = 0
    decide +kernel⟩

/-- A cubic element fixes a nonzero vector in the genuine permutation core. -/
theorem exists_cubic_fixed_ne_zero :
    ∃ a : alternatingGroup (Fin 5), orderOf a = 3 ∧
      ∃ v : core (Fin 5), v ≠ 0 ∧ coreRepresentation (Fin 5) a.val v = v := by
  refine ⟨cubic, orderOf_eq_prime (by decide +kernel) (by decide +kernel),
    fixedVector, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun v : core (Fin 5) => v.val 3) h
    exact one_ne_zero (show (1 : ZMod 2) = 0 from hh)
  · apply Subtype.ext
    ext i
    fin_cases i <;> rfl

variable {F : Type*} [Field F] [CharP F 2]

/-- The binary permutation core cannot embed equivariantly in a natural
SL₂ plane under any faithful identification of the acting A₅. -/
theorem no_equivariant_core_injection
    (f : alternatingGroup (Fin 5) →* SL(2,F)) (hf : Function.Injective f)
    (e : core (Fin 5) →+ (Fin 2 → F)) (he : Function.Injective e)
    (hact : ∀ a v, e (coreRepresentation (Fin 5) a.val v) = (f a).val *ᵥ e v) :
    False := by
  obtain ⟨a, ha, v, hv, hfix⟩ := exists_cubic_fixed_ne_zero
  have hord : orderOf (f a) = 3 := (orderOf_injective f hf a).trans ha
  have hz : e v = 0 := Matrix.SL2.cubic_fixed_eq_zero (f a) hord (e v)
    ((hact a v).symm.trans (congrArg e hfix))
  exact hv (he (hz.trans e.map_zero.symm))

/-- The same obstruction holds for the natural section (core modulo constants),
using the actual equivariant core-to-natural equivalence in odd degree. -/
theorem no_equivariant_natural_injection
    (f : alternatingGroup (Fin 5) →* SL(2,F)) (hf : Function.Injective f)
    (e : natural (Fin 5) →+ (Fin 2 → F)) (he : Function.Injective e)
    (hact : ∀ a v, e (naturalRepresentation (Fin 5) a.val v) = (f a).val *ᵥ e v) :
    False := by
  let c := coreEquivNatural (Fin 5) (by decide)
  apply no_equivariant_core_injection f hf (e.comp c.toAddMonoidHom) (he.comp c.injective)
  intro a v
  change e (c (coreRepresentation (Fin 5) a.val v)) = _
  rw [coreEquivNatural_equivariant]
  exact hact a (c v)

end BinaryPermutation.AlternatingFiveLinearTwo
