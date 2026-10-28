module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Words
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.TwoTables01
import Mathlib.Tactic.FinCases

/-!
# Orbit-color witnesses for Held pair (false,1)

The four two-generators preserve the displayed coloring of the 2058 letters.
Each marked odd generator takes its witness between two colors. Among all
nine elements of the plane, only that generator and its inverse can connect
those colors. Thus a color-preserving conjugator preserving the odd subgroup
must preserve each marked axis. These are kernel-checked finite certificates,
using the previously certified two- and odd-generator permutation tables.
Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. See source/README.md.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors01

/-- An invariant point coloring; exact orbit equality is not needed. -/
def color (x : Fin 2058) : ℕ :=
  (0x16e48db060c71424291348930ce12490548869024e94912428ca300c040266c2180970889311204806010c4918c0079d2b125284112c1c92333949185231b10a39d041244020d237108d10e4b3052228d290146128d2949000024216210919125024a51a5295b4a31a52140921498a8496436880e5a4821b40d2910318c6300c084a0a81006d18009324694a02b5a48f4b4632890c4a0634b0a91a442190036804918060025234806910d20280514a5254240349529029686a023201205a08000409314851a40620923025204801540d09121234952c025891a4091a86c219256104948c4a18d2032cc9239095a4694a49248d2010ead09d0b1a0a0000694052402429024a01b40c4a5220240111909490c5024694a6a95a40742405025a9a91281106a51524000654a52c5a582491291a929618940014200d241910803523221250006f224894a40948c4c996690252a6880c001c3008ea70863494a01806228c824d50949532220b502522125632a1322a44d4a4c318d2900da6300a97a2164990b19862195225c0a9234694a8a0021020384c4ad8941528298e969489011c02a500084424214949d2122c82004c9008a2121014892922469a8d6c514495b1204a5e64d5e34a4091cd23481e348c0b1818419129419ec88cc0190c94a5254a46c4903348523414c901522438c049d221a583011296352930d204a6064b28981ce472d201a52e7098f4a5222912368e2301125680601810f1bc035b86303c0b4b1a04a4684b525481754a4404a500000af104094a469481233292e62ca94900002009195a94a523528017cc8c481c01a46002486021c41994b48c060844b425356098d4a0084bd631a129724c44a04218164282ae124682252048c4228d2310d22604a20248310aa04a1374a509004851a46c4086c211224a503900a90c4814824741d294a6440848001c4b48209492044a12928ca0020124a00349508198664912219003490690152908d86420a9291030ad23288cd420f600c89721234a489481220310918c4448c60099a048d290390c004004886302d2a4990649948010030b46120c52001294d529000291c4a248d2303d847b80c594056a42308d295d52848d2b2bc841940311ca57a4842acc0111232246229da3184a821c000b5254a40e1912fb24854a5094bcc582445108030892210d271bd2978cab2ad2d22529296094a50c40d2b6a5f2525234a46960d240a4050252919c494c04940c091ac635a52d0040c4a92d0012358969030605ac626164b0a403720a58240018d2948c02226670a4c94112952ae9488a202528108424a1290a58c28c0948c0040d21488001a52048c414acc90414e355e0024625a46931505428a3496361a4a16a5294a4c92a4293996d00c4d4818948123230002a52d4908f6b9c24b9c34a5294206b0900263508830606a5a652da44812919129418294880062524095290008002414915a44b44f4a5550143440c4040c866a1291a5203012402449001204950301088100823906540cc9490a9489002252f2a40810d2444c6969c8040c604a446608452a00121d09690097b58660d24225834846320dac4b5205a64900845034698b4674a0691ac6b13063115682a5855b5892a0433012a100692c10003060680c94c0e94b5c81a40b010a64bc6001864425a94b52848d291880228c0a29125024845910342069600633892d6810929089195e6195304812842469480094810f00ca51a44b0386053404580612810748d225b12b281294a42949540481294806040c07098a418820 >>> (5 * x.val)) % 32

def witness (k : Fin 2) : Fin 2058 := if k = 0 then 5 else 21

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem generator_preserves (k : Fin 4) :
    ∀ x, color (representation (twoGenerator false 1 k) x) = color x := by
  have he := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.TwoTables01.representation_generator k
  change representation (twoGenerator false 1 k) = _ at he
  rw [he]
  fin_cases k <;> apply allLetters <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem coordinate_test (k : Fin 2) : ∀ (x : Fin 2058) (v : Plane),
    color x = color (witness k) →
    color (representation (markedEmbedding false 1 v) x) =
      color (representation (basisGenerator false 1 k) (witness k)) →
    v = coordinateVector k ∨ v = (coordinateVector k)⁻¹ := by
  simp only [markedEmbedding, MonoidHom.comp_apply, oddEmbedding_apply,
    basisGenerator, map_mul, map_pow,
    ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair01.odd0_eq, ← Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Pair01.odd1_eq]
  fin_cases k <;> apply allLetters <;> decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors01
