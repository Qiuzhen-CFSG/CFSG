module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.MixedRank
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates

/-!
# The distinguished orbit is the rank-sixteen fibre

The explicit inverse coordinate change represents every actual homology class
by one of 4096 binary columns. A complete decreasing-height forest reduces them
to roots 0, 1, 4 and 14 under the two actual local generators. At the nonzero
roots, Gaussian witnesses identify both row spans, and invertible triangular
pivot minors give ranks 20, 20 and 16. Full-centralizer rank invariance and local
orbit closure then prove the exact rank-sixteen characterization.

The witnesses come from `source/contraction_witnesses.py`, run with
`--output Scratch/ContractionRank/contraction.json`. The packed forest uses
4, 12, 5 and 1 bits for root, parent, height and generator choice. The echelon
rows have expansions in the forty input rows and conversely; both directions
are checked. Every numerical identity below is proved by ordinary kernel
reduction. Neither Python evaluation nor a Gaussian algorithm is a premise.

The original ATLAS matrices are credited to R. A. Wilson, S. J. Nickerson and
J. N. Bray; see Model.Data and the source README in this directory. GLS3,
Table 5.3i, printed p.270, motivates the local problem but does not identify
this homology quotient with the Frattini quotient of a two-core.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank.Census
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
open KernelBound.OrbitCoverCoordinates
open KernelBound.OrbitCoverCoordinates.LinearMembership
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000

def mixedToOrbitCols : Fin 12 → ℕ := ![1933,2654,3469,1828,3064,42,2271,2391,1808,979,437,628]
def orbitToMixedCols : Fin 12 → ℕ := ![2578,2124,242,4058,1612,1974,303,631,3437,2087,518,2082]

theorem quotient_mixed_columns :
    OrbitGeometry.Coordinates.Q * mixedEmbedding =
      (OrbitGeometry.Coordinates.columns mixedToOrbitCols : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
  let : ∀ i j : Fin 12, Decidable ((OrbitGeometry.Coordinates.Q * mixedEmbedding) i j =
      (OrbitGeometry.Coordinates.columns mixedToOrbitCols : Matrix (Fin 12) (Fin 12) (ZMod 2)) i j) :=
    fun _ _ => inferInstance
  exact funext (fun i => funext (OrbitGeometry.allFin₂
    (fun i j => (OrbitGeometry.Coordinates.Q * mixedEmbedding) i j =
      (OrbitGeometry.Coordinates.columns mixedToOrbitCols : Matrix (Fin 12) (Fin 12) (ZMod 2)) i j)
    (by decide +kernel) i))

theorem mixed_orbit_columns_inverse :
    (OrbitGeometry.Coordinates.columns mixedToOrbitCols : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
      OrbitGeometry.Coordinates.columns orbitToMixedCols = 1 := by
  rw [OrbitGeometry.Coordinates.columns_mul, ← OrbitGeometry.Coordinates.columns_one 12]
  congr 1
  exact funext (OrbitGeometry.allFin _ (by decide +kernel))

theorem orbit_mixed_columns_inverse :
    (OrbitGeometry.Coordinates.columns orbitToMixedCols : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
      OrbitGeometry.Coordinates.columns mixedToOrbitCols = 1 := by
  rw [OrbitGeometry.Coordinates.columns_mul, ← OrbitGeometry.Coordinates.columns_one 12]
  congr 1
  exact funext (OrbitGeometry.allFin _ (by decide +kernel))

theorem orbitCoordinates_mixedClass (x : Fin 12 → ZMod 2) :
    OrbitGeometry.orbitCoordinates (mixedClass x) =
      OrbitGeometry.Coordinates.columns mixedToOrbitCols *ᵥ x := by
  change OrbitGeometry.Coordinates.quotientMap (Submodule.Quotient.mk _) = _
  rw [OrbitGeometry.Coordinates.quotientMap_mk]
  change OrbitGeometry.Coordinates.Q *ᵥ (mixedEmbedding *ᵥ x) = _
  rw [Matrix.mulVec_mulVec, quotient_mixed_columns]

def mixedOfOrbit (y : OrbitGeometry.CoordinateSpace) : NaturalHomology :=
  mixedClass (OrbitGeometry.Coordinates.columns orbitToMixedCols *ᵥ y)

def mixedOfCode (n : ℕ) : NaturalHomology := mixedOfOrbit (OrbitGeometry.vectorOfCode n)

theorem orbitCoordinates_mixedOfOrbit (y : OrbitGeometry.CoordinateSpace) :
    OrbitGeometry.orbitCoordinates (mixedOfOrbit y) = y := by
  rw [mixedOfOrbit, orbitCoordinates_mixedClass, Matrix.mulVec_mulVec,
    mixed_orbit_columns_inverse, Matrix.one_mulVec]

theorem orbitCoordinates_mixedOfCode (n : ℕ) :
    OrbitGeometry.orbitCoordinates (mixedOfCode n) = OrbitGeometry.vectorOfCode n := by
  exact orbitCoordinates_mixedOfOrbit _

theorem mixedOfCode_eq_mixedClass (n : ℕ) :
    mixedOfCode n = mixedClass (OrbitGeometry.vectorOfCode
      (OrbitGeometry.Coordinates.combine orbitToMixedCols n)) := by
  unfold mixedOfCode mixedOfOrbit
  congr 1
  change (OrbitGeometry.Coordinates.columns orbitToMixedCols *ᵥ OrbitGeometry.Coordinates.decode n) =
    OrbitGeometry.Coordinates.decode (OrbitGeometry.Coordinates.combine orbitToMixedCols n)
  exact (OrbitGeometry.Coordinates.decode_combine _ _).symm

theorem mixedOfOrbit_action (b : Bool) (y : OrbitGeometry.CoordinateSpace) :
    (homologyAction (OrbitGeometry.Coordinates.generator b).val :
      Module.End (ZMod 2) NaturalHomology) (mixedOfOrbit y) =
      mixedOfOrbit (OrbitGeometry.Coordinates.actionMatrix b *ᵥ y) := by
  apply OrbitGeometry.orbitCoordinates.injective
  change OrbitGeometry.orbitCoordinates
      ((localHomologyAction (OrbitGeometry.Coordinates.generator b) :
        Module.End (ZMod 2) NaturalHomology) (mixedOfOrbit y)) = _
  change OrbitGeometry.Coordinates.equiv
      ((localHomologyAction (OrbitGeometry.Coordinates.generator b) :
        Module.End (ZMod 2) NaturalHomology) (mixedOfOrbit y)) = _
  rw [OrbitGeometry.Coordinates.equiv_generator]
  change OrbitGeometry.Coordinates.actionMatrix b *ᵥ
      OrbitGeometry.orbitCoordinates (mixedOfOrbit y) = _
  simp only [orbitCoordinates_mixedOfOrbit]

theorem mixedOfCode_action (b : Bool) (n : ℕ) :
    (homologyAction (OrbitGeometry.Coordinates.generator b).val :
      Module.End (ZMod 2) NaturalHomology) (mixedOfCode n) =
      mixedOfCode (OrbitGeometry.Coordinates.combine
        (OrbitGeometry.Coordinates.actionCols b) n) := by
  rw [mixedOfCode, mixedOfOrbit_action]
  congr 1
  change OrbitGeometry.Coordinates.actionMatrix b *ᵥ OrbitGeometry.Coordinates.decode n =
    OrbitGeometry.Coordinates.decode
      (OrbitGeometry.Coordinates.combine (OrbitGeometry.Coordinates.actionCols b) n)
  exact (OrbitGeometry.Coordinates.decode_combine _ _).symm

def sumMask {n : ℕ} {α : Type} [AddCommMonoid α] (rows : Fin n → α) (mask : ℕ) : α :=
  ∑ i : Fin n, if mask.testBit i.val then rows i else 0

theorem sumMask_mem {n : ℕ} {α : Type} [AddCommMonoid α] [Module (ZMod 2) α]
    (M : Submodule (ZMod 2) α) (rows : Fin n → α) (mask : ℕ)
    (hm : ∀ i, rows i ∈ M) : sumMask rows mask ∈ M := by
  apply Submodule.sum_mem
  intro i hi
  split_ifs
  · exact hm i
  · exact M.zero_mem

def forestRootPack : ℕ := 0x41e41e44441e1114e1111411ee41114111411114e1444111111e11e1e111414e411141e44441441441444111e41e4441e44111411444414e44141114141141111141111e1e11144e4ee14e14411141eee1e414441141e441144ee1eee4e11141e4e111e14111141111414e411411e111411141e4111e11411e11144e441ee441e1441ee44e1e11141e4e4144111eee1ee4144e41141114ee111411e1e11141eee11141e444414e141411144411e111141114e41441111411ee1e111e14114111e41eee41414ee111ee414e144111e14e414e144e11e1444141111411111eee14111444141e4441e41141ee4114114111411141e4111e1141e14441111141111411e1e44141ee14e444e111411e44e14e1e11144e1141111ee111414eeee14414e4e1ee1414e4141111e1111441444111144441441114ee14e1441444e41e111414111e44e414444114441e1144414414114144411e11e11111144e1e1444414414eee1444ee111e11e114111e41411144e41e41e411141ee4e1ee4e1414441114e1e111414114111e44111411444e14414111e4e1141111e144e1411111411e1111411414111414411411114414e41111e4e414411144e1e1411e1111141e4411e1114e4e41e4441e111e1e4111411e1441e1114e1441e4411144e1414ee414e1444414444e111e141e41e4411414e41111e11e114e41e11441eeee1414441114441e41414441411e41444e1141114ee41111e114441114141441444e4141114441e11141e114111444111e1144441e4141114441141111e1eee1411111411e114e4e14e444111e1e14414e4114144e1111411411ee414114e1e4ee1414441114144411111e11114144414114441441e11414e411411e1114e411141e1111e114e414e141e44141111e1111441444111144e41441114e414e1e4144eee1411144e14111e141141111114441e41111411e14e4111e414e4411e441411111411e14111141111144e1441441ee411e144411114114114e41e1111e1111e1e1114441411144ee41e44e114e414114441ee1411e14ee11e1141111114ee141e4e4144e111e1e44441ee14141114e411e1111e111e4e14e1111411e41e1114141141111411e111114144e1411114114e41114111e11114e144e11144414e1414441411e44111e141111e11e414111e41e414441444141144e14e1e1e1114444e144441e41e44414144411144e14414e111414e41e41eee1141e44141111e1111144e1e1ee41411111411411e111e441141111e111e44144111141111e144e1e1441444414e1e44441e1114411114114e41114111411114414e4111111e11e141114144e44111e141111e11114144e11411e1114111414411141141141114e4441e4441441e4e41e1eee111111411e1144e14111e11e1114414111441111411111eee1414e441e41114e41e41e414444e1e11144441441e14441411114111144144e111141114441141111e411141444ee1e414114144e1414e144ee4e1114114ee414444e1e4144111e1ee4e1444414144e111144e41e44441114114114111441e111e11e14ee11411e111111e4e1e144441e4141114444e14e44114e41e1144e1441441111e11ee41114141441444e414111444414e141e4e14114414e4411e111444e1e441114414ee414111414e444144141141444141e4144411144e14411114114441441e411141ee11e111141e11144ee1111e11111e441414114111ee1411141141e4411411e1114e41114141111411e1ee411111411114144414114e41ee144e4111411eee41ee441e11141411e111411141444e414414414441114414ee4111e1111441444111111411414111414441441444441e1114e1111e11444111e14111414e111e1141141114e4441444e1e441114141111411114144411411411141441eee11e1e44114e441e444e111e11141111414111e44ee414e144111e1e444e111e11444414411e1e441e1441e4e144e1411111e114141444111e4144e411141111ee144e111e4414e1e1ee4141114114111114144414111141144e111411e441411eee1441e14111ee44414e4e14e411141411114114e14111e41441e4414114111ee1411141e4e414e4e41114111e1111414111ee4111411e11e4414111141111e414ee111eee14414144414111e11e11111e144e141111e11e4e111411114441441111e114414111414114111411141444e41ee141e1114e411e11114e1e4144411414e4141111e11111ee414441ee44141ee411144e1e41ee111e144144e1e114ee14e1414111e44e41e44e1e44111e1e1111411e414111e414e14ee441e4e4114111ee44441441414e414111e11e11111414441144e41e4111444144e4111e114e4414e4e1e111e1e1141114111e14444e1441e41e44111e41ee441414e144411e1eee1144441e4444111e1114111141e111e4e4e41441441114144144414114441e414e1444111114111141114ee1e1444414e44141114e14e144e14111e441141111414e41411111e11414e1411141411e11144411141144ee144e11114114e4111e1414414e4ee14111444414e1e14ee1e11e41ee4e11e111e441141e4411411e11144411141e1111411e144e1111141111e144e14114e41e414111e11411e441411e41444e1e14e41111e44e144e44111e1414414441141e44114111e4411e1111e4111e14444414414114144e141ee14444ee111e114e441444111141144e111411e1141111141e441111e1141e11141444e144ee11411144e4414111441e414444441114141111e11414e4111114111144111e14e11141141eee14414e111e1444414e4e1e1e4411114eee14eee4111411e11411144141110
def forestParentPack : ℕ := 0x20844d0d46917b7f533e4099bd1d9490d9502e3ea4d295cd7a61e30f733f4962d364a00fa6983a5a3ae6d4fe10f939d606c25bfa608772e41533b3b7538b82f1b95eef714166fa6e1b0c9f36c3558e64c572c61912fe2cab5601db2d1c985a9c67ae9e9b0246ae73aa52ddc932ebcace4b9fc36a730798af371a891ad54304161413a9deaa8ced874e31998fdd46ec8a0c968c2f64501a1945e6b760910f55bccf464f5c65b3feb992b1cf7bb1fe657012a7c2cec7fafb3b5827f8e806d52b1778259155e31b4b290c66e02be5b81ec87ac2d6bc58fb739222c1860f0e4c11cd1b3c02d1c364d2929f6c8c5e80a19c5c1947d19f911d2a44e156463d367b83a91449b7d71e9a1fe443a27fdee50a70a14f173997770ba68ba05ebed309c0fa4a355510fef7cc065620372b96a8ccc9abb25f9ecff9b60ec24320be42731c5cb38e765f81f22982dfebbbc12a57ece88bb6338779f1da6730364af0d0e37adfe46919faaa4ed76584f747900be85a3ddb0dc234c7934f71be8d0ea04c4197719314c9a8e8666272216721b3bb418cfcbd2336885061c27fab1bc7f93602759c64c960c615865e20fc5721c92476358fcc2042ee0d869d13477195d1b9f5e7ba094f443c3ea8a31c747aa6f957693349aa64646003e73836cafc677d4b06f9f9dac1c68021945c0815b0f4b7af948f59bc0d85a2cc69a1feb580b0ef7c1f25496c724873b8d5faf7e6ea71f829c7d5eb1b6d309689024abc73a640dce9f0a94fdc4520c3a677ee68a334dba9c87463fd06082914d4aa4ce1878e3da84260b48d0d198ff78d903d2a84ed444631841aa3a9d569edad349adfe8436273cce0af7061430538b7defeb499a17eacd89ac03a4678e1cb39fb7b4be82cf027e69018126cbe2fd67b22fbb2b28424657886b91107553cc589bf9dbc2dca388c9e8ca156a5a4330a793d6d6de03a9142e6c96ad30dd80f38a9e3d7a4a40e16b023d4783d1a2d10d748b00f7dbe4c2ea08f798d40b33599e1ecf62bd9862c2b54f0451cb585c37f8ccff5706d295120b2ad826e5c716b645ea104696bf8c768c1ea5bec2bf53beb5ac74bc2f237c7eb780d682e0e9201c45b23f776e12baf5cb08290879c5f80b19d5c2fda19d375d3e606841aa48594df08732fd6465c38bafee40946d124840d3a45e1efb61fce3aa6e3f87afd3896d0f75c53a15f6711a360a04faec208eeedc99509c08bcef9a60c2525535e470c947277203b95fcaf9867cfeabb664e80fce98bfad1be06736233028e6170525a8d4cf46286eaa8efc76a3344381869f0dac614853abb4f1bf95be75cadd22d419d8f9d1edc0fb21574876498001f58ad1d0580de4897c1986b6e5230854df7f79b0384cc3e24a1f7f912da36d8c4fa0ae93a456a6c46b6838c5963d37f5f11cc7a8216d989ff7adedf051451e35b439cdd76e06b4f2040969f2cbb5df0a59ec9885103fe470002e4293805c5cb37198b1843cdaf9fd36b73be69af7df50122f3464ef2aa633656ca6442974b888988dfa44c01271116638edc141704aa5241810e55c3dc89b20d650a0fb91c978c31518d2f94bc0256607e0bfb82a927e8e8cbc52c532b4a506bb0fe7571121e3907941f04b9ddd8545da1a8fee8098468244ba20115edfdb731dcfaaae33ae1fdf9b6d0367c5363737511af606043bcc328f57912d8bbcee036e7ebb92d7caf2e452217b573b3762127689cbc9431a7a142f05ded3a3205651fc7b9f4065508a86ed96c6cb4290fea68e37dfa3f44f9386936f277f13a5a33e609f87bf557b1b08d4d9d4f915cb7a4a012e52d11b200de78b80dc50048e08b0ef5a6c47d25927e5506c016972c3b55f0bd933d413cf7d1eb5b88e9877f766952b36e210af4dda53eccba8ee178a9ffbbfecd0434ad335751918b6220674fe2bbb9037445adfca55fe9889ecc0bc6f910e42538cabd150715addc25801e449edfa8796d74304971e5f79d0345ec2c2a260d6936f1c7f8c43a063818da6aa0efa4823359a3df6d5e312d7e59ac0c85e4a6ae180fb51c578084955c2f53fa4d466c6c0bf7f6e1eee822b9c5ed7346b22e6b70f275b7ed0c33c2e0a84fcd6a93d3ade8fe69a37d319630fbeb0582a6f9207aba4de124caa811bed1ed16358d2036718ffc14dcab39136137853d1a43b080360d7c9f2d1ca92e87d6e4d57fd429dd0808986d40a24f5e63a373a17ff0f94add32f3c3fa7aee3e6e56e32b7b21f7345ba14822c7cb7af2546da26119c29dbb1e0c068521c4593f05b512c07c919f5c151d80206ae2dcc5287af1ea573ee0553db7a9927dc9a47e350aefd46b03fcd72920153d0dd6981317743ed5a888d069904fa38e8eada34c712887fcd42520e154cc055610860e25abccf9b50d1548bfc9417e7b6cb1b1a021625fb3bedceb8bc014e5efe7b2c228786f20b7d0b26b5c238771e972795f71df7bb2b08a5eec7c266d6e3291c1f806c6295814f5382cc0859e1c9b5ff0b69d2c0e46a164dea93d459110823493df78319bfda0dc48f84e9454a30f796abe67a03fec76238c4ad6e4f80afa39e6b933772254600f96bc115750cc658cac522150fdeb658ebca10c55b861ce55731271b2fe8d1022ed2817118acb24faabfbe9fb433c336ef0aa84a1465dff64183967e49973d1e5fa2d4a430c07d83417eec5d4e8397634594d70a5e2ba9091ed6c3fedef861c7be1fb652a8148e54bbacafe466822731fd58fb01f0cc20b2104553fc5b99b876591575f071d8c326c608f94085be5311a87ed0441c72984dd0eace88717c499d493b41d046da09f406243d345d02fea1a4fdc19ddf3d3860a767aa8aa1b57f036952c2854c005961c86ce18ab01d2b5cd19980d4f41bf5b6c708272b3c64e83b2dc2a0ff1e5c5ef28b71bca6b8ee00a72433a473c9764f00adba83fca6ae3d4ab0feed9d320d41d333bd713d8803e174abd4149667f4d8e4dd4a38c7d0e86ad23447143acde104741df3517239add16ec448dd640cb045437a1df02d0334aa703c9fadae43806579d9dab3b366fe0bbc2b267f7c7980b68526b5e51dfb19ba282ccecb88e35051583c0d8b6b6254a14f9a89ccc85558c9b9ffcb65d205f727a6e30a670f14a6a0396de6ba3f6997fc3e8933f4b101e090434d6ced7d5992b7638848e0db7e39ab78d3d9a4f0722965517b99f11975c3c5580be5db542ff698c0f9ca1cc5978724256cd884b7edf9f1115ff2716c828dc36fb2bfb2441c0a86ecf7ab2097873fc79827f21b7694e704c2d2761e05bb85dc07d7f1c480ef0b4ac2cd49419080a6716c9303b05f583de78ae1062b0d33541bcff1e4afcdd257de856610089abd93bbfc91475ea372200ca3a60f20f6960d3a9213f5a63e3afccb9e90e659ccf8920dd55325560bc47bc8930772c948cf52da9a87263c62a2761a8fb68b0ce457737c84460767baacea2f85d6d32fda99fd061af5333767ef1aa603b31c1f4fb944f01b98ddda74a728a8eedb5f6d84954047c25e8171734a552b159ff386c8ed4a4dc0827843d0a46e114870d3945d1e4284acd3a96d3fa3bd155f17d61934dcc3878bf6f63a07f1139f7f6b92ee8756ac5baa046eca3b8d0f775e11b5823c7504e5cacec80999d6c9f5fb005078531c77e2f04b5307be3f76fe1daabefb98a03e9a8df251ab5d9b23659f3da743106ad8c9d80443c9e876bb34d71301ea298c798adb6745114a8c43f25bbcdf90dec1588cec90b96fc2654203895cca407108540b079e857ffec2dd223e75175e42ca18e6279794fb2be831e889a6ca8b01d4453bddf1e8bdccf2571fa549d00488bd9fbdadb1906eaf602c739c872f20369a001bb21335aa3efe27862cfbabe1b7953fcb98e7fe09a522f504e328b61205793ddcc955f105a0efca6a28ec6948d3a36c90f4725f3e5f9b3caa34f6c12fd6993d0ab4f53f37a7e31a62f5a114d3296f2bf0db94dd1a78b528a4ee1a7f6d424dd516e2e0692873807acb5fb0754ce740332dd5932956cae47b001965c2c5480f5e91bd82343c6ea2b73a8f76870c245b6175b754026e12edbb8d7ff971de8b44ac57a125672276be0fb75211e630ed4815e50ac9c8c8b9d609f9f971cc994eba65eded4b9020665b75de8971c5b89ded8822c04e214310a86ed2bc701d765ddf62786cdfa9a3ffb76fef4d17da19f5fcd186ab2af961185d63f29bb0df51fe91ae346d00b50d326942c385c4eb60384974a87e1e85b5e99b7d2e2c751b4c47c7b0e62b06e4f72b2f7aec19efbe3ab825c5728d36a3b95cbb23afec70874f8c2ad4ad6808e4d9e4fa116598130d5488ac04803d6782e14a46ac0e9835235b623d97401052aba4fda9585c45a00e999183025471de4c6f756770bf4ab6bcc9e976e429ebfaeb37d720ba6ff266b9738a5cf156713963f26627dfa570d94aba25e8ae04a764f806240614f82bdccda88230854ffd9b8d21b64aaf24b0a7d8163270e9f85d2ba2de797ef3b892ed7a4ec0b7d51905099964e52a0def50bbec308cd0cc2d3cf958bb05f46d228e236c775d1185813c4db4bf1f6892d8208c1c58a1d5fed1aa342d02f318702f66a81ae5fac6c83c374d33fdb191a0563e6a7bfd3d6532f748faffc10b3ee669cff8a7a3d565b70cd4542115b83fd7641210e3807d8dbc8c61a24ebdb505302027ec1a967b0454dc299fb2aace35870fd9bcbd05401ef16db2429df3ae5ebda6542947f02b9bc8ba77fdc8f2016cf01b452dbde4c1284fa7743e2886dcf4e8ad18b5dfc421725f41a0836c647ac9e3b35f6b8655795af1f12eef3a6ac2f1e77a233b57e2d74924e164e83ee7bd28ca7e7f69b1b59513a1b45c6b0d07797d85a53e0d90bd593f1dbea08e5c7ca39d996f3253ab71049e015a62a8cd029707df6450c1ab9aec698e35d64418162806d4f42b1cc1a84e1d858ff19b4f8d7696a00e59151f1a423d5588109f7993cda5be0f16a0ce958d030e54b1d279703e6b12e24a7ad7f788560b29e73e54cbd7e46182df030f8c5411439eb7a59dbfdf649219008cdc54a111cf78ab143f02ff4ba78966681696eacac8fd17d639fafbfb8f4320abca1147ff639b03cedb63f972f37246edbd8cc07f9877c5058b6305be1635070e00845506a99d30eb599b9a953c3227e01a560c049891295ce5aa015887c20faebd0952109273501b8ff3a25e717e73b94bf0e54fdd2618c3e8a7ee208056f1f67aec1d65f2c6483af3cb682f2fa9491ad683d5a497c7345821d5b40ee768f24f5d927d81bc4c6d5ba2948f41ebe7295c5722db49e0076423c2b26aee4ecb02d47095f9b445a65d4b0dc7751301d63ecd9cf3181f905eac3ac482a357fd5345213644cd288e87054e2406074eabdd14cfdfc833725312308f6ca163dbea90274c93477956bbd00eeffa66720f6bdba0a1f668cfe8ac3cc562262db0fad116a2e463ca58fe513984b6ac8d61f05fbd0cfe286cc5543114b8a51d7f59b42dbacbe73038b0054c05f9e179275eb30a970014522e39903a8dea9b714b77d329abb8956ed8a3425079f3117072eddf2896ddf4bb1ea6a5dec49886f1f8b8a5041bf2316438cdc62cec89e6e1fab1ff3b6ad2f378b9ccb27c606f70102f4f693e199be2da7a0ed048d2e97c294cd3e347e0b485010b79ad6aad5e4c809fa0913e3db3983e30c7951d04a3c474a52e0e758306feaec5a9d4df99287c601e93aab4e49c2d9f37005d23d9e2e9f428ebeaea376902020937bd69b4eac0eb205ab863a96db8cfaeefd161259c11ba7ff8ec00828a35f056613dcde819af14befd21cc21dd64142516c808d7241615f83bd464ce787ee3b992fd7733d0b37b9d4efa7e2dad60e267a83073897dd075dcee40aee08a56d50904092099ba15e73917ccb4af10e882d3bf9c1d5849156d3285bc1f46eb0184811c591a3d1bc6c1ba2ac6f862eb3e6168621f45a2fc5b612f5d2de5de9f3997ced5174c09a4c0592796e0777cc442030ebea84b9feed0cd2b7bd3e9a7fe2192caa34e50b2a203707effdbf36af181f6a8c3e86d1c5f822a3fb0f66b311a75f3c6583a5c818c81ac4d6de2590b9f47841c155831d4b4b71c5f4bb9320b9797f73a02c24b0ae9bd096ae237a2719459e1076bac4aad9380805fac833f1d7f991e3006d41dc6750304a92adf24bffdf8435f86762ec88a86fd0b84211615cd388711154a8afe88560229ba375b66cbf258abc18f576ec56262bf4fa86fe2aab3cf6b5fd1a0058e11b67f336a52f2864c355161f745b8488f958bd88b4c2da6841825d6c40817286685f43b1e7983c7def3a489b0cb439d07a05a428a33949093964c009c03d923c9b2d8e7ea2a3b7b020e44b69d6975ca77b3e25a7e026e6e6482129f9cdd54b11b563247bd1f87cb0148012c8916f53bcad3b688e6c942ebff417a508b86f3ffb38c16766aaeda087226a99e13d613d070105321ab73e04746929bba3f009b7ddc67ddcea75eec8a96d909cbcd2405e93ac7351707dc199500f654ec2a9b1c075d1f5fbcd9a9cd35b70e489ac2724b80aeb720c1825f0b5dbbab1ec977e2689bedea5fc0230dbe9cc74232fa77405a8be659ebd993177b23d669ffdea71affe6b80fd7543635883cd24ebf8d84560e8d8c81199fd30b54ead179298667e2e74a2ad28ab80ee4b9e2436318d7b6a59e847923c5953d0749abf458cbcb92376c4ca09e90feb51d3587c19732c00684f12b4cc43ede18c277949b185eb6da4a6f658042a6d75c691d1f996a7fabb6df3a5ac1f886ec325641308a93a1667233ba5ffb8fdca953f168bfefa8170f37f81bd524d2d4c828d954051e217b309d879d11b2efcd4e4440205a980d99cf1356053e90068e2f45728c9b47fc75a301ee9a1332577dd849b212af6837cf5aebcaeb07068746f9e6810c445d46a5b173d013128f5891dd84bc1c682695478f175356a1f37b6bce65a2c3486af6cb3dcd529e9af83b1a9b40970e67c840e3a7c7b17b73e94ef0b29ca78a7e92fe01ee753937c7e5b3b60904c4d5290ce0aa5e3ce6ffd0d38a162f222d78331a55feb04b317a66f81fe5aac3c86b2fd6a42efb663a22d6b40f175811d584d8936ebf4f6d440e817170398dd96b1956a13494e02a5a3c079e094dbcd5a90d39846fe59a0d7c5980a26e71e170be2b5d7ba7de297bf064b5ed2b7fc0ef7d7997cd1883e00644fd4cecc8a8d5e38516b49bdd24b61b6a6fa263c4438ff1383d0d9e3e6dabba910a56a4788a58d307cdf1db79e8a667276cf88ade98bea5e47df2516238adc02c0ecfe6702cb13dc37b100f70935ab22569e5a0562fecb47220969035c8ef00b725fc1d95bd0f4990cdbb55fc79a951e27a733e57b2d249700ebd683be7eafbca2b0bd4e666f9225a41f0866c33a9b4d3b65f3a60dc695fd4e8b3ef6a6f1d37f41b14e936d4c4f5a87405de77868cf19592eab58fc15c409b1c66e8e0c3ab5ee177732c764923bcddb0eb80ff21eeb5353707e91ac60594c4d9686cecaa9e308754fcc18d003d22640c8dae2145bd3f81339d7f54911d8801ebada21eb88fd323e971ff7ba0136562cf48aafacbf826e63fbaf8fb16d530dfccaf157f1c42ffab63d2658bd6fa412a59166232ba4ff4c8964dfdbb8855a5479ff7b19c9784246b25c838d714151b9937de45cb7fa9fe0d75b30ecd3051071d9670035d9a57e93776abeb8a0313c428db43d0ee6ab2324773de59b98d747e5881d245ac1d689f6fb49f178103f55dff54462f466d028bf6db392aeb6505e83acf22b22f428306be211f8b53c35866c9e0b903cd7b7e2b09a2fe739db79c5750e2a74e20ca82e2dea3af3c979e436a7c0c96d43927c6e50a07093f35d539068094094a1aec35a70ee9d336dc099c1e2455ec3a9730867aabcee8775b999b6ee1c0d027c3f271ae7ebb5e3ba29ec70913f5620cd8aa239bfe91eba0ca68f216fbc3faceb1263219d1af861b824f8dda8d51262c8546134f1fd0188fc488736bd0d9790ef4b74dea7887063e8444e14e9aa13bafddd3537e7c839ca08e935ab09f90474a9327757933c4952d09c400c096b81f187b8ef44efc28a6d41d2586c12ec72d1bb5f1e71481e2fb4b3af81cd1f7d6fc31b37f6e1f52a2834c6282a66c9525d57380c624ec0d7910a54c7097901d567cb94cba45e93bf7e164980a0bc4edf9e920e26a723ecd43d2f838ad74ba83cc685f6d19b3586b6fd2a4ab51fb6138506a62f7fc4f3f2dd0ca222c6975a586bfe5b6f40b1f767925c44c571815d842e07a9e0c7b743909aec5a2bd7ded775022ab4ee1ea632decb1af304d0f63787c0084d6aae4e6e90ac7051405d939ce5444bc88b81032b21fb871c78d1c85513144bdd82aac0248b8dbf772f968cae8fa1630b2235080ffac21719953cf58a91f402bc3d86a2fc6a8f37550c6156678e9c3f6dcb12a76f8f1015e6d82846cc88d5db1856832d26fa8b65801d4842c1f0994c86ab90c39a7cee58a02f4a1040c2495e03a51a31793b7b5387b499997fd20e0d0e6e353b9297e704e60b2924d7dc8952f14951ef88bdc24a05411254b2808887f1647b5f51866e23abacff93c1d898ae121bf811f3f7dbc684ca3a2b46bded9b53adde8eee899a7c77fa44420db88a137bdd3eb5aeee700ecacae9d40b05db09d9bb31ec57500472efca001000
def forestHeightPack : ℕ := 0xa55529d275a35b5956536d9d7d61b363c868ce339eab474ed69c277b66128c1e6ad1f685e709da6a8ba55bc8f3738d29cb2cbc24dac9366d2d035ab56d64bbbe9293d5683ab46c952a4696bd2b69d64eaaa17bb2acb4295b45f4cc6ad7c66699aee83e33932569d2a55e1cb9b627c55f395d96ad495b3d30345d0cd9ef95731bd2d6bd96e55e1393d953c6da5321594a94a5acc9d230b4ed63ca527c2d18bad6a599293615ac2ab8529693d8e961f78d28d84d47842939c6346c336b599085655ad96f9d5f4ad5d17d31883e74759d184f2f9ae0dd32353d174b4ed3c36b66ba769de0fac6a6242909bb54a2dcc8c20e756ee7cad4bd9b495af45a9d69d313bcb09759d3a62b1ac1f1e6a0cadf09642accda8dc57116c71744d65ace589c68e961f25eb1681671845b34d933552369d231ade5093a72a3aaec5877a5e77966d69ae1744df283e2d54db3b39d4a3e2ebc6d6a5a7284f11822aeccad3ada6576136bca48ab5cfadeb484eb444714a54d15caa8b4679c3e2e9d9731ceb2a56d06d9f2c56ac84ab39d9d06bef39260ec3426a3a4e8ba98642cfa3e53b3893acad1a3239636723564dada99bce2f6c65783d94a32113d573bcdd5ac92e95acfac61595695931b4b4a32946d4cb1d58c6f584aa89e1d2ce1158c1aa8cd969d5b5a52d4acaaf8d8f885e72c59f27be75a56b1861e56d552639cd9a234ade2d9468f9b631ac2972c2d18bccbb66ecac6b97ced16a48d755f5ab5f654697336f57bc3485af5d4ab0b3eb5d52d1952919aa337c532b3ed5a5a148bb6f92e798e2b853a569d5b6cc5f4651d285dd06daabaaf17a52cdc4af26ae11bbdb02c2d2bd287849f87da9984a4a8cab59d26a8a655bc70ebbe15b3d96819f04528d6b5b23cab36da31956537daec88eb6c61974d6ababe35bd6cc3422bbb9f8db73185634c52719b2299b6ab65f27c5aeda5248a56aab9d7ab3e12a5692bd1f47d2679c5948de8f9be886ba088bef09c21246273ca653bbd4e8c259831ad44230ace95666339a5f0cb2374d2157e2d29aab28b65394ef0931cf8aa8fb4db73da55a4ed545a30959f5966165469734f10bdab75d9efb43379320f6cab3942489c6337d6744526f74a6fb46919caae9cab0952b0cc1f4cda70b16d17d696ad569bb714b4b4c852762b9b8b56698c62d6d215bba0fc2ad19ca539da319d314abaacc5db3ace4d7d5898ee9593a506d1b033b11649f6ad330152379d653c3ef65ce6c8ca767467662d75839d5b5e976ca54c5a7886532ba6d45ce74a3e6f84a103ce56c62924c2709528b8ad69d4c8f9a33685a3272a90c3e37ba215b9ef4ab30fb5234746a8b465071e7372e3775a2fac695b4e969d5f6a5d6b8d5d1bbe74a56b794276acaee7dab38d6d3bcab194674ace33958f9a54d25d1035de5174ad194655432d3a4e15b45f6a5ec5ad2531471bbdd396cd8d84e53a39f055a9085e93aaeec932b594a6fb29ec8da686eaba95a03ab62ea9e2e835f4b49f3bd2ad94dd6846878ca0a4bdf284dcea55aea8a79642d34d356c6690c35309356ca56b15b6f15a98bb4db99e65295771bd5b7a5271ce6f4bd03aabadaa5a72951e185e938e24f8c6d89476899aed8de5194d939c5f5cbe54b5a2788e9394ed27e68f5dd34bd28ba35732e28e85db98d7159c64f56a546cdcacd23ac55f5959d14ce97a55cd85ef5ab337baa92ace538521c7deac93ed17561453deab5e39859bc845cfad9098aed46c672939ef750544d6cc6daafa31b1aca72b3ee96be87952b4ac6d6c66d06ce36959d0752b2739b2a4476ad9cc932498d28d8c90cac5afac192ac670a46ee952b074254ab577c6dafa52cf95e8b5cdf8a4dc24be0d962fadba8e9e3359beea632107ae547ad58755f5934f454e329cd9764ad4ad6508d1f1656b555df4bc69394a14932367bdb67bdec84f3123da7862789d6b8bd1d5ad6956d6f09be93656ad9bcef741cd9566f4de2d8b60ea422e551cb8c591c32ce2b6949426b7d2f04397484578a4a4ba42d483234bd6989d6b05c216c5d33b43363c6559916e9d2d0a1272b2d8cbd62e93a737b68fbb60e95ccf5da546556d94df594d9994e93832f594edba36f2a5e589baf1a49b3ad2289da343ca54ba575b3eb3bd6307c26d83a388e9b07d218bcd2fc5177cc6b476f19cbf119d1d4b4af79ceb3b32f69a848b53558dc956d315ade339a278a3eb3add158ddd37473524e105c6b8a52d19dae78ceaed522dbb1130d5f284b0793e77bb66975974cd2aaa5e6d952d87deb67cf14862d68ba33ab2949e64c4da74bc250bbf35a51d1aceae8d595ca68ea42cb94d53941581ded19d634ad8f4b2e67c69369edafb31929290f9b9d4735b55b6b6ac64d8d274d5a30ab2697d5f4a561383eb79e6f29d7759d634545ec6c6738c21463f158c69695152abdd2a5283ad0ce8550c6d611b69ee95a76a4b5994a58bce70743184cb117aa1595a0dbca11d49d5b41f8946508b2328cd349ba4a9466bcce72d32d8ad1b3995d4ad54e2baf68ae71955a9b527742ece6d21195af69e6f672a2f755b194e52b4e70ad20c9662f9b3179d210b49b78423286253c1a9884e955ca5684e45ad1cf94e76ad1f07c152bce5775114ae670c428a74e959d14fad275bae53d4958ade13729f3ad9d3b51d3ade50546b884610acdb49329495650ad1f4bb252cd1f5a3252a46927d5d89d70f94e4a8d9d293dd4b5111c32d2945d7748d1a52b7ce472635f0759d3caa6f9b5f4ad2f29ca94a5a94ae29a82e32bb2b0a4718ab614758fba2a13b467393e54ace1285ab8bc54b5dd0bbe2d67d8d0a4af1a4e37bbad26ca4ebc5f05726f4ca0ba52ce945296e0af8e78a544767dad37d3564c616b5674aa1f8329f8b8a42c36f96c2519b9497d1a47520db56309a1b7b5af25c5a9949cb9b8cc9c1147cad184f10745cb5ceafabed3cda189ded48cd93bbf1765e7926e51bdcb67d7086c63285e318de558c1d5c3a36c6612b22b155a328d28ea16d2d46aea356c76ef7b3999a4f2abca112cab0abeef7ceb6a452fb5df4b49ac4c633bb6ccc4c369da8e842af85a73cbf2fc3a70845f254953956d5c5212bce91ccaefad6587b6b183af37cdd84d2eab5a7895aae7de507c2f66628fad6ae850b07d6139de6f9ba6e246f585552bde77b3df8ba62b84e18bd334ad999a9f30552f799ef88caee8c2cfbc24b645ec9d9549563194a7582aceab230232378c8ca845f175ecbae6768ca8d8b9d1acb578463574dd48c27564a53a22ad85e138d6515e5d1b4236ae2b564db6cddda666307ced0d5336b570eb3d935be7192d789e31696573aa3336d212b56d67c2d4952b775ed595eb56aeae64ad4740f48cd989b25844a34b35768328fb5257a4ab36b2788a65452ef17d612ace6e7514e1c67262db37ce299d6f362d78c65968d6348d2b2656d28ce787c9b793689ab6f58da4e6c7569def46d24bc428f6b258a3ab4a4670a15139caf57cdedccb2adbf16b55d7a62b3139f284a705630d95a739d291ad2af64277bc5f1b4eb1b69f1a4ef6a6e964b9b0b49738463455f12aa9765e28f9dcf3bbef47bab47ed328b1b5742f1902d4b5134bb26075400
def forestChoicePack : ℕ := 0xf2e4df5b5979a566141da8fcd1e53d5bbbfaaa3fcd2bcc43dcc66cbf3e6a08ec0d02e5c1bc17abe7747d026fd4cb07f38da7dc87c84e5fce65d6bb6a8725584e128fef01c5fcfa9c6f8773572fb01796b0c9ae8cc8c6fa1d6d9e2b8cddef5e3cf1a56adcf23340f49daf0f4ace9f0db0e85f1bdbbd984ddc71d96af9fbc5c40ae4253feef3c5fed0e01cbf2f57fda7cade360d7fcecdec7cfd037553b61165013a50bd967b6bf025ffaeb9ad137d8a9bf30616f1d023c5ef7dd421ce8f5b882673cbd56be8928977ddd38de28ef8fb5717ff78c33a9f576cb71feb9577fd1a9b9c96da67f3a774154ff37b6141dfede98b78f6876d7536c470b876af9192bccfd72ee55fefd00fdf25ffec28cff70bf0559d7f3eb77a6ce86ceef3b7fdd01bcf42155ffcc5f7fb899477cdb76a3523d9bdd28fd767e13ab99f2d9d99bd9ab8265da39a38425d2e32f6801719bb127973d24d5e9194cb8aff7d9423e3d6d6ad76bb609fba9cbf79f88966585ea2efaa27fcfd57fbc59b4ed73775e109a96aa7dfed3da1ad080e3b4cd7b9be0ee7a554bfeffced8ad523b4b9e9f977c69bc9efe875fd7e685dbb35e536d7682ab49045c460f2feddf36ed9668f11faf25ce7bff74707742f2b5ca6fddba7e48b5b1c32fb4edee932d9ea5a127448e63d6bea45dc92b8cde9eb4d84cbe25da23fa6f94ea3be8b33cfdf3d2d5fbed4f284c96b3d60
def forestRootCode (i : Fin 4096) : ℕ := (forestRootPack >>> (4 * i.val)) % 16
def forestParent (i : Fin 4096) : Fin 4096 :=
  ⟨(forestParentPack >>> (12 * i.val)) % 4096, Nat.mod_lt _ (by decide)⟩
def forestHeight (i : Fin 4096) : ℕ := (forestHeightPack >>> (5 * i.val)) % 32
def forestChoice (i : Fin 4096) : Bool :=
  if (forestChoicePack >>> i.val) % 2 = 1 then true else false

set_option maxHeartbeats 30000000 in
theorem forest_certificate : ∀ i : Fin 4096,
    (forestRootCode i = 0 ∨ forestRootCode i = 1 ∨ forestRootCode i = 4 ∨ forestRootCode i = 14) ∧
      ((forestHeight i = 0 ∧ i.val = forestRootCode i) ∨
        (forestHeight (forestParent i) < forestHeight i ∧
          OrbitGeometry.Coordinates.combine
              (OrbitGeometry.Coordinates.actionCols (forestChoice i)) (forestParent i).val = i.val)) := by
  apply OrbitGeometry.allFin
  decide +kernel

theorem forest_root_cases (i : Fin 4096) :
    forestRootCode i = 0 ∨ forestRootCode i = 1 ∨ forestRootCode i = 4 ∨ forestRootCode i = 14 :=
  (forest_certificate i).1

theorem mixed_code0 : mixedOfCode 0 = mixedClass (OrbitGeometry.vectorOfCode 0) := by
  rw [mixedOfCode_eq_mixedClass]
  congr 1

theorem mixed_code1 : mixedOfCode 1 = mixedClass (OrbitGeometry.vectorOfCode 2578) := by
  rw [mixedOfCode_eq_mixedClass]
  congr 1

theorem mixed_code4 : mixedOfCode 4 = mixedClass (OrbitGeometry.vectorOfCode 242) := by
  rw [mixedOfCode_eq_mixedClass]
  congr 1

theorem mixed_code14 : mixedOfCode 14 = mixedClass (OrbitGeometry.vectorOfCode 1892) := by
  rw [mixedOfCode_eq_mixedClass]
  congr 1


def eCodes1 : Fin 20 → ℕ := ![429726646493539,1122795443611075,264005409139494,60678443832706,33413557846120,114045354055911,15518029900419,782486777239,100106072352,4517161375201,4312699499397,1630580562183,456125382466,20401374912,141583996760,4119702508,56781338421,13124738165,395243285,180290510]
def eMat1 : Matrix (Fin 20) (Fin 50) (ZMod 2) := fun i => OrbitGeometry.Coordinates.decode (eCodes1 i)
def eFrom1 : Fin 20 → ℕ := ![1,2,5,11,20,35,110,155,281,516,1643,2158,6680,12923,19002,47252,70825,277404,527752,2703142]
def inFrom1 : Fin 40 → ℕ := ![1,2,5,11,21,35,111,157,287,517,1601,2112,6747,14351,19066,43673,72878,44327,141704,266120,79741,867405,2668,99045,449653,683721,599190,724529,970911,583823,778296,340135,881865,59505,1028199,583823,60937,705064,833744,864345]
def rowMat1 : Matrix (Fin 40) (Fin 50) (ZMod 2) :=
  mixedRowMatrix (OrbitGeometry.vectorOfCode 2578)
def sortedRows1 : Fin 20 → Fin 20 := ![1,0,2,5,3,4,6,9,10,11,7,12,14,8,16,13,17,15,18,19]
def sortedPivots1 : Fin 20 → Fin 50 := ![49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,31,28,27]
def sortedMat1 : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  eMat1.submatrix (sortedRows1) (sortedPivots1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem e1_from_rows : ∀ i : Fin 20, eMat1.row i = sumMask rowMat1.row (eFrom1 i) := by
  let : DecidablePred (fun i : Fin 20 => eMat1.row i = sumMask rowMat1.row (eFrom1 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem rows1_from_e : ∀ i : Fin 40, rowMat1.row i = sumMask eMat1.row (inFrom1 i) := by
  let : DecidablePred (fun i : Fin 40 => rowMat1.row i = sumMask eMat1.row (inFrom1 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

theorem span1 : Submodule.span (ZMod 2) (Set.range rowMat1.row) =
    Submodule.span (ZMod 2) (Set.range eMat1.row) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [rows1_from_e i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [e1_from_rows i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem tri1 : (sortedMat1).IsUpperTriangular := by
  let : ∀ i j : Fin 20, Decidable (j < i → sortedMat1 i j = 0) := fun _ _ => inferInstance
  have h : ∀ i j : Fin 20, j < i → sortedMat1 i j = 0 :=
    OrbitGeometry.allFin₂ _ (by decide +kernel)
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem det1 : (sortedMat1).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular tri1]
  decide +kernel

theorem rankE1 : eMat1.rank = 20 := by
  apply le_antisymm (Matrix.rank_le_card_height _)
  calc
    Fintype.card (Fin 20) = sortedMat1.rank := (Matrix.rank_of_det_ne_zero det1).symm
    _ ≤ eMat1.rank := Matrix.rank_submatrix_le _ _ _

theorem rankRows1 : rowMat1.rank = 20 := by
  calc
    rowMat1.rank = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range rowMat1.row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range eMat1.row)) := by rw [span1]
    _ = eMat1.rank := (Matrix.rank_eq_finrank_span_row _).symm
    _ = 20 := rankE1

theorem rankCode1 : ContractionRank.rank (mixedOfCode 1) = 20 := by
  rw [mixed_code1]
  calc
    ContractionRank.rank (mixedClass (OrbitGeometry.vectorOfCode 2578)) =
        (mixedRowMatrix (OrbitGeometry.vectorOfCode 2578)).rank :=
      ContractionRank.rank_mixedClass_matrix _
    _ = rowMat1.rank := rfl
    _ = 20 := rankRows1

def eCodes4 : Fin 20 → ℕ := ![9944450592918,6125253838174,727044675171420,306864867108115,23775374538365,138137976597718,67338358223283,2829565632023,1284613263174,972274336551,379045761806,239248129501,183448147471098,12287922187,64235790726,32796591177,130239381677,1011817320,2927612124,120282253]
def eMat4 : Matrix (Fin 20) (Fin 50) (ZMod 2) := fun i => OrbitGeometry.Coordinates.decode (eCodes4 i)
def eFrom4 : Fin 20 → ℕ := ![1,2,4,8,20,40,108,245,406,611,1412,3198,4108,8571,22100,38518,69065,218473,322020,1140037]
def inFrom4 : Fin 40 → ℕ := ![1,2,4,8,20,40,100,221,463,591,1302,3392,4108,8604,22305,38667,67881,215704,322988,475483,621356,763092,572177,438395,330241,256853,461757,942840,1017663,400920,65356,771005,203490,856157,856157,323091,134983,584683,534035,713900]
def rowMat4 : Matrix (Fin 40) (Fin 50) (ZMod 2) :=
  mixedRowMatrix (OrbitGeometry.vectorOfCode 242)
def sortedRows4 : Fin 20 → Fin 20 := ![2,3,12,5,6,4,0,1,7,8,9,10,11,16,14,15,13,18,17,19]
def sortedPivots4 : Fin 20 → Fin 50 := ![49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,31,29,26]
def sortedMat4 : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  eMat4.submatrix (sortedRows4) (sortedPivots4)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem e4_from_rows : ∀ i : Fin 20, eMat4.row i = sumMask rowMat4.row (eFrom4 i) := by
  let : DecidablePred (fun i : Fin 20 => eMat4.row i = sumMask rowMat4.row (eFrom4 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem rows4_from_e : ∀ i : Fin 40, rowMat4.row i = sumMask eMat4.row (inFrom4 i) := by
  let : DecidablePred (fun i : Fin 40 => rowMat4.row i = sumMask eMat4.row (inFrom4 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

theorem span4 : Submodule.span (ZMod 2) (Set.range rowMat4.row) =
    Submodule.span (ZMod 2) (Set.range eMat4.row) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [rows4_from_e i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [e4_from_rows i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem tri4 : (sortedMat4).IsUpperTriangular := by
  let : ∀ i j : Fin 20, Decidable (j < i → sortedMat4 i j = 0) := fun _ _ => inferInstance
  have h : ∀ i j : Fin 20, j < i → sortedMat4 i j = 0 :=
    OrbitGeometry.allFin₂ _ (by decide +kernel)
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem det4 : (sortedMat4).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular tri4]
  decide +kernel

theorem rankE4 : eMat4.rank = 20 := by
  apply le_antisymm (Matrix.rank_le_card_height _)
  calc
    Fintype.card (Fin 20) = sortedMat4.rank := (Matrix.rank_of_det_ne_zero det4).symm
    _ ≤ eMat4.rank := Matrix.rank_submatrix_le _ _ _

theorem rankRows4 : rowMat4.rank = 20 := by
  calc
    rowMat4.rank = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range rowMat4.row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range eMat4.row)) := by rw [span4]
    _ = eMat4.rank := (Matrix.rank_eq_finrank_span_row _).symm
    _ = 20 := rankE4

theorem rankCode4 : ContractionRank.rank (mixedOfCode 4) = 20 := by
  rw [mixed_code4]
  calc
    ContractionRank.rank (mixedClass (OrbitGeometry.vectorOfCode 242)) =
        (mixedRowMatrix (OrbitGeometry.vectorOfCode 242)).rank :=
      ContractionRank.rank_mixedClass_matrix _
    _ = rowMat4.rank := rfl
    _ = 20 := rankRows4

def eCodes14 : Fin 16 → ℕ := ![1062912094299808,398986270658670,141097714474798,39827473346461,108845599563248,26362852343130,3701709798997,1926370683882,646201172511,17147140568811,5499571081437,401549174848,79280735349,20114592012,192885614102,62948080436]
def eMat14 : Matrix (Fin 16) (Fin 50) (ZMod 2) := fun i => OrbitGeometry.Coordinates.decode (eCodes14 i)
def eFrom14 : Fin 16 → ℕ := ![1,3,4,14,23,49,87,149,439,537,1548,2952,5343,32980,67007,528164]
def inFrom14 : Fin 40 → ℕ := ![1,3,4,15,22,55,80,147,436,536,1555,2864,5839,4190,265,8401,18204,8932,30607,36540,43983,23544,48638,30967,53190,12126,22924,50071,10782,51544,11188,52414,40795,59040,32707,46405,0,30324,21225,39113]
def rowMat14 : Matrix (Fin 40) (Fin 50) (ZMod 2) :=
  mixedRowMatrix (OrbitGeometry.vectorOfCode 1892)
def sortedRows14 : Fin 16 → Fin 16 := ![0,1,2,4,3,5,9,10,6,7,8,11,14,12,15,13]
def sortedPivots14 : Fin 16 → Fin 50 := ![49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34]
def sortedMat14 : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  eMat14.submatrix (sortedRows14) (sortedPivots14)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem e14_from_rows : ∀ i : Fin 16, eMat14.row i = sumMask rowMat14.row (eFrom14 i) := by
  let : DecidablePred (fun i : Fin 16 => eMat14.row i = sumMask rowMat14.row (eFrom14 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem rows14_from_e : ∀ i : Fin 40, rowMat14.row i = sumMask eMat14.row (inFrom14 i) := by
  let : DecidablePred (fun i : Fin 40 => rowMat14.row i = sumMask eMat14.row (inFrom14 i)) :=
    fun _ => inferInstance
  apply OrbitGeometry.allFin
  decide +kernel

theorem span14 : Submodule.span (ZMod 2) (Set.range rowMat14.row) =
    Submodule.span (ZMod 2) (Set.range eMat14.row) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [rows14_from_e i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    rw [e14_from_rows i]
    apply sumMask_mem
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem tri14 : (sortedMat14).IsUpperTriangular := by
  let : ∀ i j : Fin 16, Decidable (j < i → sortedMat14 i j = 0) := fun _ _ => inferInstance
  have h : ∀ i j : Fin 16, j < i → sortedMat14 i j = 0 :=
    OrbitGeometry.allFin₂ _ (by decide +kernel)
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem det14 : (sortedMat14).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular tri14]
  decide +kernel

theorem rankE14 : eMat14.rank = 16 := by
  apply le_antisymm (Matrix.rank_le_card_height _)
  calc
    Fintype.card (Fin 16) = sortedMat14.rank := (Matrix.rank_of_det_ne_zero det14).symm
    _ ≤ eMat14.rank := Matrix.rank_submatrix_le _ _ _

theorem rankRows14 : rowMat14.rank = 16 := by
  calc
    rowMat14.rank = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range rowMat14.row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range eMat14.row)) := by rw [span14]
    _ = eMat14.rank := (Matrix.rank_eq_finrank_span_row _).symm
    _ = 16 := rankE14

theorem rankCode14 : ContractionRank.rank (mixedOfCode 14) = 16 := by
  rw [mixed_code14]
  calc
    ContractionRank.rank (mixedClass (OrbitGeometry.vectorOfCode 1892)) =
        (mixedRowMatrix (OrbitGeometry.vectorOfCode 1892)).rank :=
      ContractionRank.rank_mixedClass_matrix _
    _ = rowMat14.rank := rfl
    _ = 16 := rankRows14

theorem rankCode0 : ContractionRank.rank (mixedOfCode 0) = 0 := by
  rw [mixed_code0]
  have h : OrbitGeometry.vectorOfCode 0 = 0 := by
    ext i
    simp [OrbitGeometry.vectorOfCode]
  rw [h, map_zero, ContractionRank.rank_zero]

theorem rankCode14_eq_distinguished : mixedOfCode 14 = distinguishedClass := by
  apply OrbitGeometry.orbitCoordinates.injective
  rw [orbitCoordinates_mixedOfCode]
  exact OrbitGeometry.Coordinates.equiv_seed.symm

theorem rank_distinguishedClass : ContractionRank.rank distinguishedClass = 16 := by
  rw [← rankCode14_eq_distinguished]
  exact rankCode14

theorem mixedOfCode14_mem_orbit : mixedOfCode 14 ∈ distinguishedOrbit := by
  rw [rankCode14_eq_distinguished]
  exact distinguishedClass_mem_orbit

set_option maxHeartbeats 1000000 in
theorem rank_sixteen_implies_orbit_code (i : Fin 4096)
    (hr : ContractionRank.rank (mixedOfCode i.val) = 16) :
    mixedOfCode i.val ∈ distinguishedOrbit := by
  have H : ∀ n : ℕ, ∀ j : Fin 4096, forestHeight j = n →
      ContractionRank.rank (mixedOfCode j.val) = 16 → mixedOfCode j.val ∈ distinguishedOrbit := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj hrj
      rcases (forest_certificate j).2 with ⟨_, hbase⟩ | ⟨hlt, hstep⟩
      · rw [hbase] at hrj ⊢
        rcases forest_root_cases j with hz | ho | hf | hs
        · rw [hz, rankCode0] at hrj
          contradiction
        · rw [ho, rankCode1] at hrj
          contradiction
        · rw [hf, rankCode4] at hrj
          contradiction
        · rw [hs]
          exact mixedOfCode14_mem_orbit
      · have ha := mixedOfCode_action (forestChoice j) (forestParent j).val
        rw [hstep] at ha
        have hrp : ContractionRank.rank (mixedOfCode (forestParent j).val) = 16 := by
          rw [← ContractionRank.rank_invariant
            (OrbitGeometry.Coordinates.generator (forestChoice j)).val, ha]
          exact hrj
        have hp := ih (forestHeight (forestParent j)) (hj ▸ hlt) (forestParent j) rfl hrp
        have ho := (localHomologyAction_preserves_orbit
          (OrbitGeometry.Coordinates.generator (forestChoice j)) _).mp hp
        exact ha ▸ ho
  exact H (forestHeight i) i rfl hr

theorem code_surjective : Function.Surjective
    (fun n : Fin 4096 => OrbitGeometry.vectorOfCode n.val) := by
  have hb : Function.Bijective (fun n : Fin 4096 => OrbitGeometry.vectorOfCode n.val) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨OrbitGeometry.vectorOfCode_injective, by
        simp [OrbitGeometry.CoordinateSpace, ZMod.card]⟩
  exact hb.2

/-- The distinguished local orbit is exactly the rank-sixteen fibre. -/
theorem distinguishedOrbit_iff_rank_sixteen (h : NaturalHomology) :
    h ∈ distinguishedOrbit ↔ ContractionRank.rank h = 16 := by
  constructor
  · intro hh
    calc
      ContractionRank.rank h = ContractionRank.rank distinguishedClass :=
        ContractionRank.rank_eq_seed_of_mem_orbit h hh
      _ = 16 := rank_distinguishedClass
  · intro hr
    obtain ⟨n, hn⟩ := code_surjective (OrbitGeometry.orbitCoordinates h)
    have heq : mixedOfCode n.val = h := by
      apply OrbitGeometry.orbitCoordinates.injective
      rw [orbitCoordinates_mixedOfCode]
      exact hn
    rw [← heq] at hr ⊢
    exact rank_sixteen_implies_orbit_code n hr

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank.Census
