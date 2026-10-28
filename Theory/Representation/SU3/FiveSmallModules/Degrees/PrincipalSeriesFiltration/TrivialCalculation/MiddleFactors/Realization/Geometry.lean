module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Actors
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Action

/-!
# The remaining coset enumeration contract

The finite table must enumerate distinct literal left cosets, and its two
permutations must agree with the inverses of the specified matrix actors.
The independent cardinality premise then proves that the enumeration is onto.
The constructor `ofTable` transports a computation over GF(25) using the actual
Borel-preserving comparison. No existence or generation is asserted here.

Source: `MiddleFactors/source/standard_flag_data.txt` and its right-coset
convention; Guralnick–Malle Proposition 4.3, Aschbacher–Smith K.2, p.453.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization

/-- An injective point table, with the exact inverse-actor convention. -/
structure CosetEnumeration where
  point : Fin 126 → CanonicalPoints
  injective : Function.Injective point
  base : point 0 = QuotientGroup.mk 1
  action : ∀ j i, point (image j i) = (actor j)⁻¹ • point i

/-- Transport a literal table-field coset computation to the canonical pair. -/
noncomputable def CosetEnumeration.ofTable
    (q : Fin 126 → TableGroup ⧸ tableBorel) (hq : Function.Injective q)
    (ha : ∀ j i, q (image j i) = (tableActor j)⁻¹ • q i)
    (hb : q 0 = QuotientGroup.mk 1) : CosetEnumeration where
  point i := cosetEquiv tableBorel canonicalBorel canonicalEquiv canonicalEquiv_borel (q i)
  injective := (cosetEquiv tableBorel canonicalBorel canonicalEquiv canonicalEquiv_borel).injective.comp hq
  base := by
    rw [hb]
    change QuotientGroup.mk (canonicalEquiv 1) = QuotientGroup.mk 1
    rw [map_one]
  action j i := by
    rw [ha, cosetEquiv_smul, map_inv]
    rfl

/-- The supplied count is used only to make the injective point table onto. -/
noncomputable def CosetEnumeration.equiv (c : CosetEnumeration)
    (hcard : Nat.card CanonicalPoints = 126) : Fin 126 ≃ CanonicalPoints :=
  Equiv.ofBijective c.point ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨c.injective, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]⟩)

@[simp] theorem CosetEnumeration.equiv_apply (c : CosetEnumeration)
    (hcard : Nat.card CanonicalPoints = 126) (i : Fin 126) :
    c.equiv hcard i = c.point i := rfl

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
