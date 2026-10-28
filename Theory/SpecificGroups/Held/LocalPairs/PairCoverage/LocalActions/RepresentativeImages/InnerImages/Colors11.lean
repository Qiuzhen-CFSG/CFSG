module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Words
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables11
import Mathlib.Tactic.FinCases

/-!
# Orbit-color witnesses for Held pair (true,1)

The four two-generators preserve the displayed coloring of the 2058 letters.
Each marked odd generator takes its witness between two colors. Among all
nine elements of the plane, only that generator and its inverse can connect
those colors. Thus a color-preserving conjugator preserving the odd subgroup
must preserve each marked axis. These are kernel-checked finite certificates,
using the previously certified two- and odd-generator permutation tables.
Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. See source/README.md.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors11

/-- An invariant point coloring; exact orbit equality is not needed. -/
def color (x : Fin 2058) : ℕ :=
  (0xa58adc2910a0714ad808a508ca2294ae0004e8084e108a62881028cab194a52288221885389c62ac858b9a328c452104e300a4715cc1cca421c05438a42148d214e9284a580cb121087295ae22caf70ce3494a0728c519ec52b0e728ca570c652a8ee688455c160194a228ce22820513965214a528584294d0294a5200a579c65114ab7144e6b0ce81cae514a3208a2190445d0e43c08d1880521ce48958d6c0a188c92295c411485214f2615853940d211702952214ca5215c534c4b288a4814c0835c4314a2ac0a41087312e052946528ca5589d382ca2114aa209a02bdc3194ae88ca2290a57104d31224194ac010a5b904c188a511485215c52c08581c6b128ab59d656096521c82715c27a88229553214ad2886520ce52009081dce801a2294872b9c41084b1c140015a3694e2294e5388cf114a32b507111a53c603715224b14529ca520ca52ce672988f69c82910a72b8a049094694892a5253b4a5000052d8a92baee81dc231607210e41412b808a9810852a8a428887380e2228e518880594a03944e288a58120c83986910856144529c841148570cc42948c2946c29445288a5288b2294b72c9c43ad67314a4b10a48146718e0a28cae214b1288a4001c8210b3314a729265394a3294a58144410847299c22988c208ab291c551062240481446383862308843408a29052288b222e0e394a2214a52b8e22b085230ad5b08c288438428561c472998f2ac64295ee8416c2adce208a4834a310892188e4188a329c451412423a06128a52b16a3920521407811a329043100a2638ae2c0a529e0272c87708ae11a0b714a011493308e271050208442a49402c4213a86291c328ca42c4852ba04230422005029e05294ad8394514ca58c06d9c4a2694a3834422c1862c1eb2c5c280845808a268c9778c8e2161023490145c2298855948501a222b4a311d872a602794a590dc57018539484494b2695a272e0431c4229ce4318a2709d0290d338d27345822348c01a1028cf02346c340652c1c92ba00814a2214a225065210447146e2a0a32920a19ca22c08b29c822c08210804315a6214877088c8920d7c04924c4b8244504c85694ac708452ac006352d2288763604108a429d2589ce58144e71006251cc59587288a5710eb3d0a571c430284b11565249542a8a0388a43ac4208a257c0a42c262244a3814e03908c298b1495ac310eea1da298a2524dcb808e429ca5290453019011084b35cc114c5816452b16669062a88a2108822d1d028d2d288851010528cc210cab14045708ab69082234879908561445394a5100f3590a4588a468cee189cd1158e1c1a270a631b5d02888e2960b1920424ce39944411085715c2488905146c1526e3ba6b188a4280853b8051a8502b844208c529a05134a228040194a4214422146e1106d38dc5108ae00c90110c570882838e2638a5388a38ace21c1c5734a428c5301885139c611c42319ec815cc294b059e90394a572934188a2240ac70c450146431c844ad4f29670119502cca580c4e118a31c2221822282d82299a38906721525214e384204708a5114857104c28c45389c72c18b29044110842922a290a32d20383082015c52c08c1407011c4e3949114dc08344019c12208b018845188652c0851888b2b5a328d65615340160919ca420c8c988852cdb03980559c45434a528ca7644d23088528a05515d039dc718ca528c8411cc53944728cac8948280e0203a2582d8e29c4c211a5291e4285c53b8ea0b48610ca32b0e9590872948c2148b5250729ca5294a6298a418820 >>> (5 * x.val)) % 32

def witness (k : Fin 2) : Fin 2058 := if k = 0 then 0 else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem generator_preserves (k : Fin 4) :
    ∀ x, color (representation (twoGenerator true 1 k) x) = color x := by
  have he := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.TwoTables11.representation_generator k
  change representation (twoGenerator true 1 k) = _ at he
  rw [he]
  fin_cases k <;> apply allLetters <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem coordinate_test (k : Fin 2) : ∀ (x : Fin 2058) (v : Plane),
    color x = color (witness k) →
    color (representation (markedEmbedding true 1 v) x) =
      color (representation (basisGenerator true 1 k) (witness k)) →
    v = coordinateVector k ∨ v = (coordinateVector k)⁻¹ := by
  simp only [markedEmbedding, MonoidHom.comp_apply, oddEmbedding_apply,
    basisGenerator, map_mul, map_pow,
    ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair11.odd0_eq, ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair11.odd1_eq]
  fin_cases k <;> apply allLetters <;> decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors11
