module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.Packed

/-!
# Checked Co₁ local matrices and eight-dimensional action

The first twelve products evaluate the published `Co1G1-max5W1` program.
The remaining products evaluate z = (x*y^3)^14. The two local generators
commute with z, and their actions intertwine with two invertible 8-by-8
matrices through an explicitly split injection. All certificates use kernel
reduction of packed rows, followed by `Packed.decode_product`.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/Co1G1-max5W1 .
The exact program, reproducible generator and coordinate convention are in
`CentralizerSection/source/`. No group order or recognition is assumed.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.Matrices
open Packed

def aRows : Fin 24 → ℕ :=
  ![14568742, 8730514, 16056698, 3053411, 7222122, 11550909, 6184221, 8477716, 11437002, 10461699, 6969765, 13973477, 1322595, 15457769, 1328873, 13337339, 10191992, 3643281, 15394642, 8995024, 9732588, 6652923, 12246250, 12562466]

def bRows : Fin 24 → ℕ :=
  ![6360623, 14740635, 11798632, 6366879, 7578691, 12993865, 16345908, 15448472, 7321200, 2745588, 9841156, 1296923, 6426820, 2765237, 12296090, 4376699, 12707437, 5432847, 14747083, 16526157, 2229586, 2736718, 1418073, 12866597]

def step01Rows : Fin 24 → ℕ :=
  ![8344296, 270130, 5776780, 2647601, 12795410, 10384617, 9188136, 10383650, 3529909, 11042845, 13608438, 4905435, 16513294, 3321858, 1306278, 9570129, 7353478, 7369086, 4179272, 2322544, 2855845, 6287299, 2794656, 7208197]

def step02Rows : Fin 24 → ℕ :=
  ![13996145, 1419781, 2537448, 3106553, 3512924, 1618500, 7367296, 1259703, 12508501, 9761222, 4025207, 14542737, 5100504, 11740290, 12025773, 9375392, 8335963, 16458892, 1929158, 390905, 14195148, 3828792, 5513239, 7245636]

def step03Rows : Fin 24 → ℕ :=
  ![1081650, 10657398, 10695716, 7004982, 1311655, 10509888, 9771279, 11527896, 14201196, 3653657, 6609785, 392853, 14712078, 8225415, 10170538, 13243725, 5598356, 47565, 10137930, 11186304, 11260055, 15903626, 13530603, 6428470]

def step04Rows : Fin 24 → ℕ :=
  ![11515687, 13395581, 4138865, 14743180, 12616528, 2624994, 4251870, 13552489, 14600511, 11098954, 10919630, 6140460, 9100176, 11631428, 7116841, 1455012, 3489336, 6884554, 11661579, 12761581, 7622547, 13575103, 6562313, 14829339]

def step05Rows : Fin 24 → ℕ :=
  ![9985479, 13752466, 16466655, 10959251, 531533, 14266475, 10971039, 6837654, 7665122, 10733219, 2592574, 617389, 2632717, 11824471, 16348473, 15718992, 8585838, 5285134, 10655695, 6654362, 1122740, 3880661, 9850801, 8525289]

def step06Rows : Fin 24 → ℕ :=
  ![13877773, 5378329, 4497764, 14030432, 12991926, 5728225, 15492239, 7115917, 3258363, 8145004, 17414, 7255605, 11611759, 8034338, 11173178, 6201032, 66351, 7672877, 10292984, 10804452, 11079093, 11164480, 8896118, 8260249]

def step07Rows : Fin 24 → ℕ :=
  ![9304319, 9739192, 10179330, 6228244, 14351329, 5010515, 2778959, 4236901, 9840728, 13806575, 7366612, 13812510, 2590363, 5051102, 11273504, 1738420, 217073, 11458129, 16020549, 13314618, 5673937, 2868512, 13265631, 11826560]

def step08Rows : Fin 24 → ℕ :=
  ![1439333, 11348075, 225553, 12512193, 10041440, 7629110, 1691039, 15979761, 14122167, 15077836, 1825498, 10103481, 10271831, 16016111, 9115609, 14891104, 4132804, 5819691, 8217717, 5522524, 15853983, 15263560, 12570307, 14483091]

def step09Rows : Fin 24 → ℕ :=
  ![10940257, 8734986, 310443, 1637615, 6588481, 14985856, 9654081, 6273570, 2141633, 5196448, 1201466, 16705482, 5499217, 5987447, 15289581, 5552466, 10125216, 1345157, 12011787, 5534786, 11471379, 14659941, 6551971, 13024730]

def step10Rows : Fin 24 → ℕ :=
  ![12572080, 8997550, 9292303, 6032897, 2493190, 13207087, 1326899, 5076797, 12990300, 8047397, 2096695, 10633086, 15395268, 8934898, 2360603, 7715604, 5661507, 3579256, 8092630, 7021608, 7583520, 4073827, 2792487, 15163362]

def step11Rows : Fin 24 → ℕ :=
  ![4731259, 5256440, 2074965, 1294449, 8619711, 1124082, 2394222, 4945501, 6877797, 9783018, 15813912, 13214701, 10281840, 2341953, 1609472, 5407119, 13723880, 1779847, 11238862, 1072944, 12502311, 5133935, 10656328, 6065048]

def step12Rows : Fin 24 → ℕ :=
  ![7803729, 6337855, 8432390, 267409, 5287929, 4531465, 14610255, 15994630, 8596304, 14490563, 722776, 11194654, 10856214, 7534987, 8569857, 4448986, 13838635, 13489792, 1916665, 8842867, 11782446, 13638403, 7180600, 2959646]

def y2Rows : Fin 24 → ℕ :=
  ![1000997, 2591101, 577019, 6303001, 6080747, 2774185, 10795057, 2206750, 3902981, 14125077, 4682292, 15009058, 15186069, 1813092, 6147404, 214046, 14686864, 5166039, 1887982, 15601763, 1701804, 11899389, 8487783, 7816246]

def y3Rows : Fin 24 → ℕ :=
  ![6515429, 8457148, 4845048, 13510303, 5376230, 7694960, 12384284, 2579054, 3364093, 12489776, 7598275, 15927497, 16652166, 7759930, 3091106, 2333091, 15101457, 15492276, 1981714, 15691281, 9491555, 2704386, 15668562, 7460311]

def wRows : Fin 24 → ℕ :=
  ![6082725, 1937293, 16747112, 9680443, 13228035, 4794195, 16460866, 332439, 14881564, 2301381, 3305628, 9968384, 13900705, 7989904, 4427560, 1906085, 662005, 7099469, 6898438, 15186031, 8016821, 16433683, 5380202, 6325923]

def w2Rows : Fin 24 → ℕ :=
  ![12803731, 12337064, 14489588, 9373472, 9239127, 4687436, 448635, 15090499, 2089034, 6064274, 10636597, 7430913, 12412259, 7312410, 10073178, 1353217, 16344279, 4720049, 2424823, 7390618, 2640052, 13427502, 3419540, 11126889]

def w4Rows : Fin 24 → ℕ :=
  ![9579307, 7679012, 11682730, 15347907, 10989142, 2037772, 1059844, 10393943, 1733901, 16456945, 11362734, 6288594, 9801594, 11131193, 13967737, 4857452, 6985215, 1516730, 11413755, 12171446, 10803523, 12687417, 13934825, 1965268]

def w6Rows : Fin 24 → ℕ :=
  ![2358008, 2832056, 5064519, 2411906, 15674139, 5440777, 4842862, 7515083, 7810692, 4069500, 7233412, 13946619, 2516984, 3496913, 10076138, 2973849, 13825600, 7211226, 12346040, 4186563, 6723971, 3867873, 74850, 12103043]

def w7Rows : Fin 24 → ℕ :=
  ![3773804, 13758544, 2290329, 10288642, 1713234, 5243769, 9048738, 11460779, 14123844, 3789154, 5053550, 5917240, 14334235, 4684918, 1365357, 4712765, 4043670, 7057725, 6410221, 1254795, 5998229, 14212558, 15599461, 7234912]

def zRows : Fin 24 → ℕ :=
  ![13508362, 12097739, 5630779, 7768010, 6861979, 4099377, 14322221, 3267391, 15561462, 16263874, 14245064, 7111256, 10103398, 7650101, 7658293, 9305509, 12565229, 11791427, 5388698, 662775, 7086573, 13279104, 2350326, 3974682]

def smallXRows : Fin 8 → ℕ :=
  ![235, 118, 123, 150, 87, 249, 161, 82]

def smallYRows : Fin 8 → ℕ :=
  ![193, 180, 236, 131, 132, 110, 183, 120]

def smallYInvRows : Fin 8 → ℕ :=
  ![44, 110, 90, 245, 148, 134, 103, 74]

def basisRows : Fin 24 → ℕ :=
  ![87, 3, 209, 84, 27, 207, 99, 53, 210, 116, 102, 8, 20, 195, 195, 37, 135, 125, 212, 151, 47, 196, 242, 16]

def leftInverseRows : Fin 8 → ℕ :=
  ![193, 195, 245, 677, 695, 515, 577, 51]

theorem step01_product : (decode (n := 24) aRows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) bRows = decode (n := 24) step01Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step02_product : (decode (n := 24) step01Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) bRows = decode (n := 24) step02Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step03_product : (decode (n := 24) step01Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step02Rows = decode (n := 24) step03Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step04_product : (decode (n := 24) step03Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step03Rows = decode (n := 24) step04Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step05_product : (decode (n := 24) step04Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step03Rows = decode (n := 24) step05Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step06_product : (decode (n := 24) step02Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step03Rows = decode (n := 24) step06Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step07_product : (decode (n := 24) step02Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step06Rows = decode (n := 24) step07Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step08_product : (decode (n := 24) step07Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step06Rows = decode (n := 24) step08Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step09_product : (decode (n := 24) step01Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step01Rows = decode (n := 24) step09Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step10_product : (decode (n := 24) step08Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step09Rows = decode (n := 24) step10Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step11_product : (decode (n := 24) step10Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step03Rows = decode (n := 24) step11Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem step12_product : (decode (n := 24) step11Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step01Rows = decode (n := 24) step12Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem y2_product : (decode (n := 24) step12Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step12Rows = decode (n := 24) y2Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem y3_product : (decode (n := 24) y2Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) step12Rows = decode (n := 24) y3Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem w_product : (decode (n := 24) step05Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) y3Rows = decode (n := 24) wRows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem w2_product : (decode (n := 24) wRows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) wRows = decode (n := 24) w2Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem w4_product : (decode (n := 24) w2Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) w2Rows = decode (n := 24) w4Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem w6_product : (decode (n := 24) w4Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) w2Rows = decode (n := 24) w6Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem w7_product : (decode (n := 24) w6Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) wRows = decode (n := 24) w7Rows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem z_product : (decode (n := 24) w7Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) w7Rows = decode (n := 24) zRows :=
  mul_eq_of_certificate _ _ _ (by decide +kernel)

def identityRows (n : ℕ) : Fin n → ℕ := fun i => 2 ^ i.val

theorem decode_identity (n : ℕ) :
    (decode (identityRows n) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext i j
  simp [decode, identityRows, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem z_square : (decode (n := 24) zRows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) zRows = 1 := by
  rw [← decode_identity 24]
  exact mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem smallX_square : (decode (n := 8) smallXRows : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
    decode (n := 8) smallXRows = 1 := by
  rw [← decode_identity 8]
  exact mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem smallY_mul_inv : (decode (n := 8) smallYRows : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
    decode (n := 8) smallYInvRows = 1 := by
  rw [← decode_identity 8]
  exact mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem smallY_inv_mul : (decode (n := 8) smallYInvRows : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
    decode (n := 8) smallYRows = 1 := by
  rw [← decode_identity 8]
  exact mul_eq_of_certificate _ _ _ (by decide +kernel)

theorem x_commutes : (decode (n := 24) step05Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) zRows = decode (n := 24) zRows * decode (n := 24) step05Rows := by
  rw [← decode_product, ← decode_product]
  exact congrArg decode (show product step05Rows zRows = product zRows step05Rows from
    by decide +kernel)

theorem y_commutes : (decode (n := 24) step12Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    decode (n := 24) zRows = decode (n := 24) zRows * decode (n := 24) step12Rows := by
  rw [← decode_product, ← decode_product]
  exact congrArg decode (show product step12Rows zRows = product zRows step12Rows from
    by decide +kernel)

theorem x_intertwines : (decode (n := 24) step05Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    (decode (n := 8) basisRows : Matrix (Fin 24) (Fin 8) (ZMod 2)) =
      decode (n := 8) basisRows * decode (n := 8) smallXRows := by
  rw [← decode_product, ← decode_product]
  exact congrArg decode (show product step05Rows basisRows = product basisRows smallXRows from
    by decide +kernel)

theorem y_intertwines : (decode (n := 24) step12Rows : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    (decode (n := 8) basisRows : Matrix (Fin 24) (Fin 8) (ZMod 2)) =
      decode (n := 8) basisRows * decode (n := 8) smallYRows := by
  rw [← decode_product, ← decode_product]
  exact congrArg decode (show product step12Rows basisRows = product basisRows smallYRows from
    by decide +kernel)

theorem leftInverse_basis :
    (decode (n := 24) leftInverseRows : Matrix (Fin 8) (Fin 24) (ZMod 2)) *
      (decode (n := 8) basisRows : Matrix (Fin 24) (Fin 8) (ZMod 2)) = 1 := by
  rw [← decode_identity 8]
  exact mul_eq_of_certificate _ _ _ (by decide +kernel)

end Sporadic.LeechRelated.Co1.CentralizerSection.Matrices
