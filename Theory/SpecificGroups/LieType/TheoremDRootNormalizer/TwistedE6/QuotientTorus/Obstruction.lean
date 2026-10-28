module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.QuotientTorus
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6

/-!
# The twisted E6 torus obstruction from a specified lift

Apply the existing odd-prime rank contradiction to the faithful root curve
and three-coordinate torus in the literal projective root normalizer.
The sole geometric input is the specified lift of the published diagonal
torus into the defining-characteristic subgroup. Its independent producer
must supply that lift for the unconditional exclusion.

Source: the torus obstruction in Aschbacher–Smith A.2.18, printed p.40,
with the pinned carrier conventions of GLS3 §§2.2–2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6.TheoremDRootNormalizer

/-- The quotient and normalizer premises are discharged from the literal torus lift. -/
theorem not_quasithin_of_torus_lift (m : ℕ) (hm : 0 < m)
    (t : (Fin 4 → (FixedField m)ˣ) →* definingCharacteristicSubgroup 2 m)
    (ht : ∀ a, ambientInclusion m (t a) = foldedTorusMatrix m a) :
    ¬ IsQuasithin (Model 2 m) :=
  not_quasithin_of_normalizer_torus m hm
    (projectiveRootHom_injective_of_torus_lift m t ht hm)
    (liftedTorusNormalizer m t ht) (liftedTorusNormalizer_injective m t ht hm)

end TwistedE6.TheoremDRootNormalizer
