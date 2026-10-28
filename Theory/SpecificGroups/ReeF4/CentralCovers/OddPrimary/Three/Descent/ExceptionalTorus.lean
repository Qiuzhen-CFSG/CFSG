module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Data
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Roots

/-!
# The marked nonsplit torus in the concrete Ree group

The full norm-one parameter pair is inserted into the A₂×A₂ coroot torus
with signed exponent `(-2)^m`. This parity choice preserves the scalar
three-center. The explicit Weyl word makes it fixed by a conjugate of the
exceptional twist. The proved Lang theorem supplies the conjugator, and
rational descent puts the result in the actual finite root-generated carrier.

`exceptionalTorus_marking` records the exact field transports, root words,
and conjugator for the subsequent permutation and graph extension. No
projective quotient or unitary embedding is assumed.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A. The square of the source's
half-integer Ree parameter is `2^(2*m+1)` here.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent

/-- The complete marked norm-one product torus in the actual split Ree carrier. -/
def exceptionalTorus (m : ℕ) (hm : 1 ≤ m) : TorusMap m where
  map := (toSplitGroup m).comp (ExceptionalTorus.modelMap m hm)
  injective := (toSplitGroup_injective m).comp (ExceptionalTorus.modelMap_injective m hm)
  fixed _ := reeTwist_toSplitGroup m _

/-- Exact geometric marking retained by finite-field descent. -/
theorem exceptionalTorus_marking (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    ReeF4.BinaryDegree.ExceptionalTensor.Classification.splitEmbedding
      (ExceptionalTorus.coefficientEmbedding m) ((exceptionalTorus m hm).map a) =
      (ExceptionalTorus.conjugator m hm)⁻¹ *
        ExceptionalTorus.markedCorootWord m
          (ExceptionalTorus.normUnitHom m (ExceptionalTorus.quadraticEmbedding m) a.1)
          (ExceptionalTorus.normUnitHom m (ExceptionalTorus.quadraticEmbedding m) a.2) *
        ExceptionalTorus.conjugator m hm := by
  change ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.modelEmbedding
    (ExceptionalTorus.coefficientEmbedding m) (ExceptionalTorus.modelMap m hm a) = _
  rw [ExceptionalTorus.modelMap_marking, ExceptionalTorus.algebraicMap_corootWord]

end ReeF4.CentralCovers.OddPrimary.Three.Descent
