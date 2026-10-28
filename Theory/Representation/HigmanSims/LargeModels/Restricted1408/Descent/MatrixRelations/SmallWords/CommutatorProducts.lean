module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Soundness
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.CommutatorProducts.Certificates

/-!
# The fourteen products for the small commutator relations

The simultaneous packed certificates establish the ordinary matrix equalities
between the unchanged decoded literal tables. The three identity endpoints
use the proved decoding of the coordinate rows. Every numerical premise of
`CommutatorProducts` is discharged here, without hypotheses about the other
product families, invertibility, density or the presentation.

The actual consumer `smallWords_of_products` combines these products with the
independent generator and alternating families to establish source indices
4–6, in the original commutator convention a⁻¹b⁻¹ab. Those families remain
with the small-word assembly owner. Source: ATLAS HSG1-P1.M, retained in
`Descent/source/`; see `CommutatorProducts/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
open LongPacked CommutatorCertificate

/-- All fourteen literal commutator-family products, with no extra premises. -/
theorem commutatorProducts : CommutatorProducts where
  a_inverse := productCertificate_sound aRows inverseRows aiRows
      a_bounded inverse_bounded ai_bounded inverse_size CommutatorCertificate.a_inverse
  ai_ab := productCertificate_sound aiRows abRows commRows
      ai_bounded ab_bounded comm_bounded ab_size CommutatorCertificate.ai_ab
  comm_comm := productCertificate_sound commRows commRows comm2Rows
      comm_bounded comm_bounded comm2_bounded comm_size CommutatorCertificate.comm_comm
  comm2_comm2 := productCertificate_sound comm2Rows comm2Rows comm4Rows
      comm2_bounded comm2_bounded comm4_bounded comm2_size CommutatorCertificate.comm2_comm2
  comm4_comm := (productCertificate_sound comm4Rows commRows identityRows
      comm4_bounded comm_bounded identity_bounded comm_size CommutatorCertificate.comm4_comm).trans identity_decode
  ai_ai := productCertificate_sound aiRows aiRows ai2Rows
      ai_bounded ai_bounded ai2_bounded ai_size CommutatorCertificate.ai_ai
  ai2_ab2 := productCertificate_sound ai2Rows ab2Rows mixedRows
      ai2_bounded ab2_bounded mixed_bounded ab2_size CommutatorCertificate.ai2_ab2
  mixed_mixed := productCertificate_sound mixedRows mixedRows mixed2Rows
      mixed_bounded mixed_bounded mixed2_bounded mixed_size CommutatorCertificate.mixed_mixed
  mixed2_mixed := (productCertificate_sound mixed2Rows mixedRows identityRows
      mixed2_bounded mixed_bounded identity_bounded mixed_size CommutatorCertificate.mixed2_mixed).trans identity_decode
  ai_inverse := productCertificate_sound aiRows inverseRows aiiRows
      ai_bounded inverse_bounded aii_bounded inverse_size CommutatorCertificate.ai_inverse
  aii_abb := productCertificate_sound aiiRows abbRows squareCommRows
      aii_bounded abb_bounded squareComm_bounded abb_size CommutatorCertificate.aii_abb
  squareComm_squareComm := productCertificate_sound squareCommRows squareCommRows squareComm2Rows
      squareComm_bounded squareComm_bounded squareComm2_bounded squareComm_size CommutatorCertificate.squareComm_squareComm
  squareComm2_squareComm := productCertificate_sound squareComm2Rows squareCommRows squareComm3Rows
      squareComm2_bounded squareComm_bounded squareComm3_bounded squareComm_size CommutatorCertificate.squareComm2_squareComm
  squareComm3_squareComm3 := (productCertificate_sound squareComm3Rows squareComm3Rows identityRows
      squareComm3_bounded squareComm3_bounded identity_bounded squareComm3_size CommutatorCertificate.squareComm3_squareComm3).trans identity_decode

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
