module

public import Theory.Representation.ReeF4.BinaryDegree.TitsAbsolute.Degree26Restriction.CliffordBound
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.SpecificGroups.ReeF4.DerivedTits
public import Theory.SpecificGroups.Tits.FiveFrobenius

/-!
# Degree-26 restriction from a Frobenius subgroup of Tits

A faithful characteristic-two representation of a group containing an abelian
subgroup of order 25, normalized fixed-point freely by a subgroup of order 24,
has dimension at least 24. This is the abelian weight-orbit bound.

For an arbitrary irreducible degree-26 representation of the full binary Ree
group, choose a constituent on its derived subgroup. Simplicity of that subgroup
and the abelianization argument make the constituent faithful. The certified
isomorphism with Parrott's Tits group transfers the lower bound, so the
constituent occupies more than half the ambient space. Clifford's conjugate-span
argument then proves that the restriction is irreducible.

The Frobenius subgroups are supplied by the independent concrete certificate
in `Tits.FiveFrobenius`, giving the unconditional restriction theorem. The
conditional reductions are retained. No small-degree catalogue or faithfulness
hypothesis on the original representation is used. The argument works over any
algebraically closed field of characteristic two; the final specialization has
the exact algebraic-closure signature used by the Tits minimum reduction.

Sources: Isaacs, *Character Theory of Finite Groups*, Theorem 6.5, and the
weight-orbit argument formalized in `AbelianFrobeniusDegree`. The certified
concrete subgroups come from the ATLAS Tits maximal-subgroup word program
`TF42G1-max8W1`, https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/TF42/.
-/

public section

namespace ReeF4.BinaryDegree.TitsAbsolute
open Representation
universe u v

/-- The concrete Frobenius pair bounds all faithful characteristic-two actions,
without requiring irreducibility or finite coefficient field. -/
theorem parrott_degree_ge_twentyFour_of_frobenius_subgroups
    {F : Type u} [Field F] [CharP F 2] [IsAlgClosed F]
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (K C : Subgroup Tits.ParrottGroup) [IsMulCommutative K]
    (hK : Nat.card K = 25) (hC : Nat.card C = 24)
    (hnorm : C ≤ Subgroup.normalizer (K : Set Tits.ParrottGroup))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : Tits.ParrottGroup) * k * (c : Tits.ParrottGroup)⁻¹ = k → k = 1)
    (σ : Representation F Tits.ParrottGroup V) (hσ : Function.Injective σ) :
    24 ≤ Module.finrank F V := by
  let : Nontrivial K := (Finite.one_lt_card_iff_nontrivial (α := K)).mp (by omega)
  have horder : (Nat.card K : F) ≠ 0 := by
    exact (CharP.cast_eq_zero_iff F 2 (Nat.card K)).not.mpr (by rw [hK]; decide)
  simpa only [hC] using
    card_le_finrank_of_fixedPointFree_normalizer σ K C hσ horder hnorm hfree

/-- A faithful-degree bound on the actual Parrott carrier rules out splitting
of any irreducible degree-26 representation on the derived binary Ree group. -/
theorem degree26_restrict_of_parrott_minimum
    {F : Type u} [Field F] [IsAlgClosed F]
    (hmin : ∀ (W : Type v) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (σ : Representation F Tits.ParrottGroup W),
      Function.Injective σ → 24 ≤ Module.finrank F W)
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F (Model 0) V) (hτ : τ.IsIrreducible)
    (hdim : Module.finrank F V = 26) :
    Representation.IsIrreducible (τ.comp (commutator (Model 0)).subtype) := by
  obtain ⟨e⟩ := DerivedTits.nonempty_derived_equiv
  let : IsSimpleGroup (commutator (Model 0)) := e.isSimpleGroup
  let : τ.IsIrreducible := hτ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (τ.comp (commutator (Model 0)).subtype)
  have hfaith : Function.Injective W.toRepresentation :=
    faithful_derived_constituent τ (by omega) W
      ((Subrepresentation.irreducible_iff_isAtom W).mp hW).ne_bot
  have hbound : 24 ≤ Module.finrank F W.toSubmodule :=
    hmin W.toSubmodule (W.toRepresentation.comp e.symm.toMonoidHom)
      (hfaith.comp e.symm.injective)
  apply irreducible_restrict_of_large_constituent τ (commutator (Model 0)) hτ W hW
  omega

/-- A concrete Frobenius pair in Parrott's Tits group suffices for the required
restriction statement, uniformly for every irreducible representation of degree 26. -/
theorem degree26_restrict_of_frobenius_subgroups
    {F : Type u} [Field F] [CharP F 2] [IsAlgClosed F]
    (K C : Subgroup Tits.ParrottGroup) [IsMulCommutative K]
    (hK : Nat.card K = 25) (hC : Nat.card C = 24)
    (hnorm : C ≤ Subgroup.normalizer (K : Set Tits.ParrottGroup))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : Tits.ParrottGroup) * k * (c : Tits.ParrottGroup)⁻¹ = k → k = 1)
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F (Model 0) V) (hτ : τ.IsIrreducible)
    (hdim : Module.finrank F V = 26) :
    Representation.IsIrreducible (τ.comp (commutator (Model 0)).subtype) := by
  apply degree26_restrict_of_parrott_minimum (fun W _ _ _ σ hσ => ?_) τ hτ hdim
  exact parrott_degree_ge_twentyFour_of_frobenius_subgroups K C hK hC hnorm hfree σ hσ

/-- Every irreducible degree-26 representation of the binary Ree group in
characteristic two restricts irreducibly to its derived subgroup. The concrete
Frobenius pair discharges all group inputs, independently of any small-degree
catalogue or faithfulness assumption on the original representation. -/
theorem degree26_restrict
    {F : Type u} [Field F] [CharP F 2] [IsAlgClosed F]
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F (Model 0) V) (hτ : τ.IsIrreducible)
    (hdim : Module.finrank F V = 26) :
    Representation.IsIrreducible (τ.comp (commutator (Model 0)).subtype) := by
  obtain ⟨K, C, hcomm, hK, hC, hnorm, hfree⟩ := Tits.exists_five_frobenius_subgroups
  let : IsMulCommutative K := hcomm
  exact degree26_restrict_of_frobenius_subgroups K C hK hC hnorm hfree τ hτ hdim

/-- The exact restriction input for the absolute Tits degree-minimum reduction,
uniformly over algebraic closures of finite fields of characteristic two. -/
theorem degree26_restrict_algebraicClosure
    (E : Type v) [Field E] [Finite E] [CharP E 2]
    (V : Type v) [AddCommGroup V] [Module (AlgebraicClosure E) V]
    [FiniteDimensional (AlgebraicClosure E) V]
    (τ : Representation (AlgebraicClosure E) (Model 0) V)
    (hτ : τ.IsIrreducible) (hdim : Module.finrank (AlgebraicClosure E) V = 26) :
    Representation.IsIrreducible (τ.comp (commutator (Model 0)).subtype) :=
  degree26_restrict τ hτ hdim

end ReeF4.BinaryDegree.TitsAbsolute
