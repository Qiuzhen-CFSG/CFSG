module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Words
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables00
import Mathlib.Tactic.FinCases

/-!
# Orbit-color witnesses for Held pair (false,0)

The four two-generators preserve the displayed coloring of the 2058 letters.
Each marked odd generator takes its witness between two colors. Among all
nine elements of the plane, only that generator and its inverse can connect
those colors. Thus a color-preserving conjugator preserving the odd subgroup
must preserve each marked axis. These are kernel-checked finite certificates,
using the previously certified two- and odd-generator permutation tables.
Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. See source/README.md.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors00

/-- An invariant point coloring; exact orbit equality is not needed. -/
def color (x : Fin 2058) : ℕ :=
  (0x18f50d2b68c717282a1248a30d0725d255086a2290a5114428ca320c0422a4d2180a7888a311445006410c4a18c803a14c129494914d1c54333e0a19d431b530421241284020d437908910eec31d4228d4a2306160d4a51084028e16b92a1914c028ac1a94a624a31a941709475198e532e34888f628821a409291c318c6320c0e5398e100691900a3286a5242c6288752463609cd524635358a1a842190034804a19060229435106a10d40290515294c728035154a22d894a4e320140638842040a330851a88620943229445009448d2a125435314d029aa1a88a1c06d219456904a50c5018d44330ca23dca6286a5289750d4010e893a12c1a5802006a485440282a229801a48d52942028011192a510c50286a52a8a628084a88c2292aa11491107083144210655294d629a25114a1ad4a698930120220d441912e225432254c210672288a5280a50c4d9164a0294b4888d201e30091078863531801906228c825512a51557238b402942129832a55162849528c318d4a00d26300aa3a575519cc198621b14262d8a2246a540a4039c223c4d531aa4b14e6190a4948a011e462920384427396a521472308221cca00982139275094a2286aa0d8d5b04a63544528e6550e35280a1c943500e350c8c191a41914a498ed88cc4190ca5294c5286d510f250543730ca215424bcc0521421a9a32114a6a54a30d40529665366a5a1047b1401a94f789a7529426114348e232114c490641912719c0363c6321c0c535245286e525455019452844529c0200a71040a5286a501433414f6b18a510802248a1b12a529435c0873c88d501e01a86422886239e419a0c50c060844c72954689a95240951d831a54a7a8c452442181846028f1286e2294050c4260d4310d42684a22288310a8452556529ca204851a86d7086d21142529c38918a0c487502284a14a52ae439c802204c5116a511645394a28ca00381752403531c91986651142190035106a0154a08da64b98a611230b143288c94b91500c8a7b9435288a51142035ca18c4450c640992450d4a23dcd20400508632314b5192651a09210033a46120c512014a5514a2002a1c58250d4321da43bc8d6148c4a8e338d4a6514e50d4c29c841b003120a53a8842b0c411143228622a12319cae220000a54c5288f19147aa885529ca51ccc5a845108833894210d4819d4a38cac631492294a2b16a529cd70d4c4a8f1829435286a68d443a88c2294a1a04a52c4a48c8a1b0636294901c0d52d49011436098a23464630626b2ec3a8837a5855a80418d4a50c0222a480a8ca4914a5aeca508a222949108425394a3a9ad28c0a50c8048d47508841a94450c41530ca22d6f350e0228626286a3312572ca3532351a8a74a94a528ca2a8ea4198920c49501aa501432348062949510874bde253de35294a7246c390026a5ce5b4604a926831245114a1914a7182a508006a9440b14a00084028938b1245244752974030f348c4070c864b94a1a940301442284a201445152321089100824106c48cca5118a509c4229472a88910d444c86a4a08070c6052846688452a481221ca4900a3a5a668d44229a35046320d2d5254462a2a0084c0246a8a4685386a1b06c13463115892a9a5625aa2a443311501006a62dc423460480ca52d0a525ee1a80c210a651c64218644a92a5254950d4a1880228c0b6114c02884611c37386a6806340949491ca6108a1b0e61954b501497286a5100a501c700ca51a84c03c605a40461061291c850d426354c2914a528ea531645014a5106448c08398a418820 >>> (5 * x.val)) % 32

def witness (k : Fin 2) : Fin 2058 := if k = 0 then 1 else 21

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem generator_preserves (k : Fin 4) :
    ∀ x, color (representation (twoGenerator false 0 k) x) = color x := by
  have he := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.TwoTables00.representation_generator k
  change representation (twoGenerator false 0 k) = _ at he
  rw [he]
  fin_cases k <;> apply allLetters <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem coordinate_test (k : Fin 2) : ∀ (x : Fin 2058) (v : Plane),
    color x = color (witness k) →
    color (representation (markedEmbedding false 0 v) x) =
      color (representation (basisGenerator false 0 k) (witness k)) →
    v = coordinateVector k ∨ v = (coordinateVector k)⁻¹ := by
  simp only [markedEmbedding, MonoidHom.comp_apply, oddEmbedding_apply,
    basisGenerator, map_mul, map_pow,
    ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair00.odd0_eq, ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair00.odd1_eq]
  fin_cases k <;> apply allLetters <;> decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors00
