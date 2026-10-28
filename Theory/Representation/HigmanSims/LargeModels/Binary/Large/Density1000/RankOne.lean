module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Setup
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Recurrences
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Values

/-!
# Numerical assembly for the degree-1000 HS rank-one polynomial

The column kernel, row kernel, and polynomial's value on the first cyclic row
are certified in `RankOne.Values`. `Algebra`, `Recurrences`, and `Spanning`
certify the literal-generator identification of D, all 999 cyclic transitions,
and spanning. Since the polynomial and the outer product commute with D and
agree on the first row of this spanning chain, they are equal. The final
`polynomial_identity` discharges every numerical premise and identifies the
exact source polynomial with the supplied outer product unconditionally.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and the preserved witness
`Binary/source/density1000.json`. See `RankOne/source/README.md` for provenance,
checked scope and reproducible measurements.
-/

public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

/-- The three remaining independently certifiable numerical inputs. The two
kernel identities and polynomial-row value have already been proved. -/
theorem polynomial_identity_of_packed_certificates
    (halgebra : decode 1000 Data.dRows = algebraMatrix)
    (hspan : Submodule.span (ZMod 2) (Set.range RankOne.chain) = ⊤)
    (hstep : ∀ i : Fin 999,
      vecMul (RankOne.chain i.castSucc) (decode 1000 Data.dRows) = RankOne.chain i.succ) :
    polynomialMatrix = vecMulVec imageVector functionalVector := by
  apply polynomial_identity_of_cyclic_rows RankOne.chain hspan
  · intro i
    rw [← halgebra]
    exact hstep i
  · rw [← halgebra]
    exact RankOne.d_mul_image
  · rw [← halgebra]
    exact RankOne.functional_mul_d
  · exact RankOne.polynomial_row_outer

/-- The published polynomial in the four literal generator words is exactly
the supplied outer product, with no remaining certificate hypotheses. -/
theorem polynomial_identity :
    polynomialMatrix = vecMulVec imageVector functionalVector :=
  polynomial_identity_of_packed_certificates RankOne.decoded_algebra_eq
    RankOne.chain_span RankOne.chain_step

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
