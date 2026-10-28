module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.FactorSpanning.Certificates

/-!
# Full matrix algebras for all nine central coset factors

For each of the six three-dimensional and three nine-dimensional published
pairs, a checked rank-one operator has spanning row and column orbits.
The resulting matrix units generate the entire algebra over the fixed field F.
This discharges the algebra certificate consumed by the literal quotient-action
irreducibility theorem. Coset coordinates and actual flag coordinates remain
independent inputs to the conditional application below.

Source: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464, citing GM02
Theorem 6.2 and Table 6.3. The fixed witnesses derive from the licensed ATLAS
hexacode carrier; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate

/-- Every published pair generates the full matrix algebra over the actual
hexacode field, in the published factor coordinates. -/
theorem factorSpanning : FactorSpanning := by
  intro t Q hQ
  fin_cases t
  · exact Spanning.Factor0.full Q hQ
  · exact Spanning.Factor1.full Q hQ
  · exact Spanning.Factor2.full Q hQ
  · exact Spanning.Factor3.full Q hQ
  · exact Spanning.Factor4.full Q hQ
  · exact Spanning.Factor5.full Q hQ
  · exact Spanning.Factor6.full Q hQ
  · exact Spanning.Factor7.full Q hQ
  · exact Spanning.Factor8.full Q hQ

/-- Apply the certified matrix algebras to the literal coset representation.
The parent assembly supplies the two independently constructed coordinate maps. -/
theorem cosetFiltration_of_certified_factorSpanning
    (C : CosetCoordinates) (D : FlagCoordinates) : CosetFiltration :=
  cosetFiltration_of_certificates C D factorSpanning

end Representation.Hexacode.TwelveDimensional.CosetCertificate
