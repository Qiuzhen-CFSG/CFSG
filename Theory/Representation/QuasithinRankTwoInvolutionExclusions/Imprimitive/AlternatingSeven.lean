module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Extension
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements

/-!
# Involution ranks on the binary A₇ conjugate pair

The four-space is the natural SL₄(2) module restricted through the actual
A₇ → A₈ ≃ SL₄(2) embedding in `AlternatingSevenConjugatePair.Model.Natural`.
The second action is its conjugate by the transposition (0 1). The faithful
S₇ action on their product is the one constructed in `Model.Extension`:
even permutations act on the two blocks, and the transposition swaps them.
Its `firstEquiv` and `secondEquiv` identify the actual invariant summands
with these two marked A₇ representations.

Every involution of A₇ moves a plane in any faithful binary four-space:
it fixes a letter, and the six-letter transvection obstruction gives the
lower bound, while square-zero displacement gives the upper bound. Thus
an inner involution moves four dimensions on the product. An odd involution
exchanges the summands, so the graph calculation gives rank four as well.
No component rank hypothesis or cohomology calculation is assumed.

This is the concrete calculation for Aschbacher–Smith, *The Classification
of Quasithin Groups*, G.11.2(8), printed p.364 (PDF p.375), used in 6.2.19,
printed p.691 (PDF p.708). Transport from arbitrary source coordinates is
separate; a group-family identification alone does not identify its module.
-/

public section

namespace Representation.RankTwo.Imprimitive.AlternatingSeven

open Representation.AlternatingSevenConjugatePair
open Model

/-- The component calculation applies to every faithful binary A₇ four-space. -/
theorem finrank_faithful_involution
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 4)
    (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (movedSpace ρ t) = 2 := by
  exact (BinaryOffender.fixedCodim_zpowers_eq_displacement_rank ρ t).symm.trans
    (Model.involution_fixedCodim ρ hρ hdim t ht)

/-- Involutions move a plane in the actual restricted SL₄(2) module. -/
theorem finrank_natural_involution (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (movedSpace natural t) = 2 :=
  finrank_faithful_involution natural natural_faithful four_dimension t ht

/-- The actual odd conjugate has the same component rank. -/
theorem finrank_outer_involution (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (movedSpace outerNatural t) = 2 :=
  finrank_faithful_involution outerNatural outerNatural_faithful four_dimension t ht

/-- The even action is literally the block diagonal action of the marked modules. -/
theorem inner_operator (a : alternatingGroup (Fin 7)) :
    symmetricRepresentation a.val = (natural a).prodMap (outerNatural a) := by
  apply LinearMap.ext
  intro v
  exact symmetricRepresentation_inner a v

/-- The odd coset acts by the two marked block maps after interchanging coordinates. -/
theorem odd_action (a : alternatingGroup (Fin 7)) (v : Eight) :
    symmetricRepresentation (a.val * transposition) v =
      (natural a v.2, outerNatural a v.1) := by
  rw [map_mul, Module.End.mul_apply, symmetricRepresentation_transposition,
    symmetricRepresentation_inner]

/-- Inner involutions move two dimensions in each of the two summands. -/
theorem finrank_inner_involution (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (movedSpace symmetricRepresentation t.val) = 4 := by
  calc
    _ = Module.finrank (ZMod 2)
        (LinearMap.range ((natural t).prodMap (outerNatural t) - 1)) :=
      congrArg (fun f : Module.End (ZMod 2) Eight =>
        Module.finrank (ZMod 2) (LinearMap.range (f - 1))) (inner_operator t)
    _ = Module.finrank (ZMod 2) (movedSpace natural t) +
        Module.finrank (ZMod 2) (movedSpace outerNatural t) :=
      finrank_block (natural t) (outerNatural t)
    _ = 4 := by rw [finrank_natural_involution t ht, finrank_outer_involution t ht]

/-- A square-one element in the odd coset moves exactly four dimensions. -/
theorem finrank_swapping_involution (a : alternatingGroup (Fin 7))
    (h2 : (a.val * transposition) * (a.val * transposition) = 1) :
    Module.finrank (ZMod 2)
      (movedSpace symmetricRepresentation (a.val * transposition)) = 4 := by
  have hact2 : symmetricRepresentation (a.val * transposition) *
      symmetricRepresentation (a.val * transposition) = 1 := by
    rw [← map_mul, h2, map_one]
  exact (finrank_of_exchanges _ (outerNatural a) (natural a)
    (fun v w => odd_action a (v, w)) hact2).trans four_dimension

/-- Every odd permutation has the precise coset form used by `odd_action`. -/
theorem odd_normal_form (g : Equiv.Perm (Fin 7)) (hg : g ∉ alternatingGroup (Fin 7)) :
    ∃ a : alternatingGroup (Fin 7), g = a.val * transposition := by
  have hs : g.sign = -1 := (Int.units_eq_one_or g.sign).resolve_left hg
  refine ⟨⟨g * transposition, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs,
      show transposition.sign = -1 by decide]
    decide
  · change g = (g * transposition) * transposition
    rw [mul_assoc, ← pow_two, transposition_sq, mul_one]

/-- Every involution of the concrete eight-dimensional S₇ model has rank four. -/
theorem finrank_involution (t : Equiv.Perm (Fin 7)) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (movedSpace symmetricRepresentation t) = 4 := by
  by_cases heven : t ∈ alternatingGroup (Fin 7)
  · exact finrank_inner_involution ⟨t, heven⟩ ((Subgroup.orderOf_mk t heven).trans ht)
  · obtain ⟨a, rfl⟩ := odd_normal_form t heven
    apply finrank_swapping_involution
    simpa only [ht, pow_two] using pow_orderOf_eq_one (a.val * transposition)

/-- Including the identity, a square-one element has displacement rank zero or four. -/
theorem finrank_square_one (t : Equiv.Perm (Fin 7)) (ht : t * t = 1) :
    Module.finrank (ZMod 2) (movedSpace symmetricRepresentation t) = 0 ∨
    Module.finrank (ZMod 2) (movedSpace symmetricRepresentation t) = 4 := by
  by_cases h1 : t = 1
  · subst t
    left
    apply Submodule.finrank_eq_zero.mpr
    change LinearMap.range (symmetricRepresentation 1 - 1) = ⊥
    rw [map_one, sub_self, LinearMap.range_zero]
  · exact Or.inr (finrank_involution t (orderOf_eq_prime (by simpa [pow_two] using ht) h1))

/-- The rank-two exclusion for the concrete module in G.11.2(8).
It holds on all square-one elements, hence on the source subgroup X. -/
theorem not_rankTwo (t : Equiv.Perm (Fin 7)) (ht : t * t = 1) :
    Module.finrank (ZMod 2) (movedSpace symmetricRepresentation t) ≠ 2 := by
  rcases finrank_square_one t ht with h | h <;> omega

end Representation.RankTwo.Imprimitive.AlternatingSeven
