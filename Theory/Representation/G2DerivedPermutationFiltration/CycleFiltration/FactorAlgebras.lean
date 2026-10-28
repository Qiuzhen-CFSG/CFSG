module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixData
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion
import Mathlib.Algebra.BigOperators.Fin

/-!
# The full algebras of the two binary G₂ cycle-factor matrix pairs

For each of the literal pairs A, B from `MatrixData`, put g = A³B and
N = (1 + g)(1 + g²)(1 + g⁴ + g⁸). The checked polynomial NBN is the outer
product of two vectors. Their packed coordinates are (1672898027, 730482006)
for factor zero and (2211545814, 686370475) for factor one.

Each seed has a basis of 32 vectors in its orbit under A and B. We check the
orbit recursion and a left inverse of each basis matrix. The rank-one matrix
criterion then produces every matrix unit inside any algebra containing A, B.
Packed XOR products are proved to decode to ordinary binary matrix products;
every numerical identity below is verified by Lean's kernel.

The witness data comes from the cycle-factor calculation documented in
`MatrixData`. This is the finite matrix-algebra ingredient for the application
to Aschbacher–Smith G.7.2(3), printed pp.347–348 / PDF pp.358–359. Identifying
these matrices with the actual group action is a separate statement.
-/

@[expose] public section

open Matrix
namespace G2DerivedPermutationFiltration.CycleData.FactorCertificate
private abbrev Rows := Fin 32 → Nat
private abbrev Mat := Matrix (Fin 32) (Fin 32) (ZMod 2)
private def vector (x : Nat) : Half := fun i => bit x i.val
private def matrix (xs : Rows) : Mat := fun i => vector (xs i)

private lemma bit_xor (x y j : Nat) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

private def xorList : List Nat → Nat
  | [] => 0
  | x :: xs => x ^^^ xorList xs
private lemma bit_xorList (xs : List Nat) (j : Nat) :
    bit (xorList xs) j = (xs.map (fun x => bit x j)).sum := by
  induction xs with
  | nil => simp [xorList, bit]
  | cons x xs ih =>
    simpa only [xorList, bit_xor, List.map_cons, List.sum_cons] using congrArg (bit x j + ·) ih

private def rowProduct (x : Nat) (ys : Rows) : Nat :=
  xorList (List.ofFn (fun k : Fin 32 => if x.testBit k.val then ys k else 0))
private def product (xs ys : Rows) : Rows := fun i => rowProduct (xs i) ys
private lemma vector_rowProduct (x : Nat) (ys : Rows) :
    vector (rowProduct x ys) = vecMul (vector x) (matrix ys) := by
  funext j
  change bit (rowProduct x ys) j.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  simp only [vecMul, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  simp only [matrix, vector, bit]
  cases h : x.testBit k.val <;> simp [h]
private lemma matrix_product (xs ys : Rows) : matrix (product xs ys) = matrix xs * matrix ys := by
  funext i
  exact vector_rowProduct (xs i) ys

private def add (xs ys : Rows) : Rows := fun i => xs i ^^^ ys i
private lemma matrix_add (xs ys : Rows) : matrix (add xs ys) = matrix xs + matrix ys := by
  funext i j
  exact bit_xor _ _ _

private def identity : Rows := fun i => 2 ^ i.val
private lemma matrix_identity : matrix identity = 1 := by
  ext i j
  simp [matrix, vector, identity, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

private def rankOneRows (u v : Nat) : Rows := fun i => if u.testBit i.val then v else 0
private lemma matrix_rankOneRows (u v : Nat) :
    matrix (rankOneRows u v) = vecMulVec (vector u) (vector v) := by
  ext i j
  simp only [matrix, vector, rankOneRows, vecMulVec_apply, bit]
  by_cases h : u.testBit i.val = true <;> simp [h]

private lemma matrix_mul_mem (Q : Subalgebra (ZMod 2) Mat) (x y z : Rows)
    (hx : matrix x ∈ Q) (hy : matrix y ∈ Q) (h : product x y = z) : matrix z ∈ Q := by
  rw [← h, matrix_product]
  exact Q.mul_mem hx hy
private lemma matrix_add_mem (Q : Subalgebra (ZMod 2) Mat) (x y : Rows)
    (hx : matrix x ∈ Q) (hy : matrix y ∈ Q) : matrix (add x y) ∈ Q := by
  rw [matrix_add]
  exact Q.add_mem hx hy

private lemma span_rows_of_inverse (xs ys : Rows) (h : product ys xs = identity) :
    Submodule.span (ZMod 2) (Set.range (matrix xs)) = ⊤ := by
  have hm : matrix ys * matrix xs = 1 := by
    rw [← matrix_product, h, matrix_identity]
  change Submodule.span (ZMod 2) (Set.range (matrix xs).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (matrix ys), ?_⟩
  change vecMul (vecMul v (matrix ys)) (matrix xs) = v
  rw [vecMul_vecMul, hm, vecMul_one]


private lemma column_realizations (Q : Subalgebra (ZMod 2) Mat) (A : Fin 2 → Mat)
    (hA : ∀ a, A a ∈ Q) (xs : Rows) (p : Fin 31 → Fin 32) (a : Fin 31 → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (xs (p i))) = vector (xs i.succ)) :
    ∀ i, ∃ L : Mat, L ∈ Q ∧ L.mulVec (vector (xs 0)) = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, hs i]

private lemma row_realizations (Q : Subalgebra (ZMod 2) Mat) (A : Fin 2 → Mat)
    (hA : ∀ a, A a ∈ Q) (xs : Rows) (p : Fin 31 → Fin 32) (a : Fin 31 → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (xs (p i))) (A (a i)) = vector (xs i.succ)) :
    ∀ i, ∃ R : Mat, R ∈ Q ∧ vecMul (vector (xs 0)) R = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, hs i]

private lemma full_of_orbits (Q : Subalgebra (ZMod 2) Mat) (A : Fin 2 → Mat)
    (hA : ∀ a, A a ∈ Q) (cols rows ci ri : Rows)
    (cp rp : Fin 31 → Fin 32) (ca ra : Fin 31 → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, (A (ca i)).mulVec (vector (cols (cp i))) = vector (cols i.succ))
    (hrs : ∀ i, vecMul (vector (rows (rp i))) (A (ra i)) = vector (rows i.succ))
    (hci : product ci cols = identity) (hri : product ri rows = identity)
    (huv : vecMulVec (vector (cols 0)) (vector (rows 0)) ∈ Q) : Q = ⊤ := by
  classical
  choose L hL heL using column_realizations Q A hA cols cp ca hcp hcs
  choose R hR heR using row_realizations Q A hA rows rp ra hrp hrs
  apply CycleMatrixCriterion.algebra_eq_top_of_rank_one Q (vector (cols 0))
    (vector (rows 0)) L R hL hR huv
  · have he : (fun i => (L i).mulVec (vector (cols 0))) = matrix cols := funext heL
    rw [he]
    exact span_rows_of_inverse cols ci hci
  · have he : (fun i => vecMul (vector (rows 0)) (R i)) = matrix rows := funext heR
    rw [he]
    exact span_rows_of_inverse rows ri hri



private def a2 : Fin 2 → Rows :=
  ![![2203489550, 3791872274, 256, 3759634898, 1024, 3231476475, 160653335, 2760263558, 260, 2631723291, 3993923617, 1, 3720523152, 3065157053, 262144, 519304440, 8388608, 3188950178, 2415922058, 131072, 1222869078, 1611137024, 3305717097, 2138341009, 2138341011, 1608189683, 3305717225, 671088640, 2519958690, 134217728, 268435456, 2893902842],
    ![1224389416, 3263422720, 1148734435, 688055752, 134406640, 4096189662, 2855885459, 3963181715, 1115685140, 3062880696, 3824769755, 1199189810, 2332291560, 1870815512, 3959841072, 1669488952, 2264925408, 3818984640, 3843257836, 721653800, 1325633560, 930298819, 158994307, 2608544739, 2675653601, 2776308683, 3296974296, 2198074856, 3254378027, 1627426816, 1627545904, 1105288747]]

private def a3 : Fin 2 → Rows :=
  ![![128, 1125865392, 536870912, 8, 3791876370, 4226488714, 3720523153, 1, 134217728, 4161920515, 3695357328, 71303168, 231956567, 833658809, 699572153, 3262458874, 204674597, 1222869078, 4194304, 1048576, 524288, 3065419197, 262144, 2544628546, 2544629634, 970839122, 264192, 256, 1222893910, 4, 4217655621, 983586181],
    ![777800309, 1617162522, 1741002236, 2152371053, 3624713120, 4265433839, 675021005, 2785177657, 2826426802, 267785355, 376968210, 4256077187, 1982980199, 1806439635, 1570666406, 644083994, 397000028, 3894721477, 1778349270, 3195841442, 3655722393, 2548444697, 4267268847, 4137241041, 1900745029, 2812159251, 1637786897, 2020419748, 268435456, 2785017856, 3321888768, 1073774594]]

private def g : Fin 2 → Rows :=
  ![![33554432, 969530371, 3019396863, 1513615285, 2147483648, 2203489550, 2760263558, 2903844753, 609460605, 6144, 160653399, 3040851893, 423806031, 4236216069, 3800888317, 524288, 2887874878, 3812851822, 3393964326, 1190483859, 1477594997, 3065419197, 3065157053, 2097152, 6291456, 4161920515, 3475388374, 675338136, 921911844, 1071015069, 3384370098, 512],
    ![2182610968, 2262743805, 3880044765, 3381610672, 2550231312, 659011310, 2899655672, 2962821400, 2804501590, 2952923928, 2458645325, 1175927728, 1180486381, 2416728760, 240156749, 2933312253, 536936984, 785584717, 1175202730, 777837285, 3247319936, 2291153848, 2560319504, 249998333, 2834574264, 2395388157, 2262812901, 2254228221, 538665224, 268435456, 134348808, 404385812]]

private def g2 : Fin 2 → Rows :=
  ![![4161920515, 31487586, 3305717225, 3710467252, 512, 3679793071, 833658809, 402784256, 3305717097, 2893902842, 2369050687, 1012256834, 3602198794, 536870912, 1073741824, 1190483859, 2276080744, 1048576, 3695356304, 24576, 8192, 2291683420, 1121163642, 3065419197, 262144, 1615626891, 2186277761, 4, 4217655621, 256, 1222893910, 6144],
    ![679477292, 2151220232, 2959985283, 290240165, 2037707943, 2847474732, 3566138070, 1506801287, 2713237641, 106972687, 4183092874, 33053218, 4027952300, 672662541, 2038464517, 3761832968, 3515691168, 826028197, 1911878306, 3784893444, 2166367237, 269633641, 1474706121, 2554917511, 273281670, 1505047688, 2578719920, 2014096800, 33177379, 538665224, 1627426816, 3221479688]]

private def g4 : Fin 2 → Rows :=
  ![![8388608, 32, 402653184, 2138341011, 2893902842, 275236451, 1802787531, 4218704193, 131072, 3791876354, 1, 2147483648, 3677876149, 256, 1222893910, 519271672, 2887874878, 8192, 4104157780, 1610612736, 536870912, 160653399, 71303168, 1024, 3695356304, 2097152, 4194304, 3305717225, 2597468954, 3305717097, 2768321897, 3940606280],
    ![3368502821, 2302411247, 2292220166, 2040716770, 3485911840, 1090388969, 2212555457, 1213698785, 1098694380, 148451866, 3359812326, 146833920, 3227644676, 1213898281, 3359157549, 3358060775, 1096954406, 2153793218, 1213986349, 2436461577, 2314828751, 2372252119, 1155402217, 155516869, 1212580833, 3362171621, 2306605519, 3384970146, 403202178, 1098787624, 1098820394, 1088945953]]

private def g8 : Fin 2 → Rows :=
  ![![1024, 275236451, 1608189683, 2631723291, 3712564404, 2, 3191047330, 671088640, 8192, 3040851893, 8388608, 3940606280, 3602198794, 131072, 1222738006, 519304440, 2276080744, 256, 926411221, 1611137024, 3305717097, 33554432, 67108864, 1, 3720523153, 160653399, 71303168, 4217655617, 4217655621, 1048576, 1572864, 2048],
    ![77748823, 1716609365, 2244211827, 3728253681, 1159913844, 586366720, 1259658274, 2413026418, 1645529349, 1648363636, 106214774, 1151778675, 3227640580, 1699012948, 625377364, 105996629, 2170751488, 3279162113, 606397296, 4249510228, 571875457, 1154997362, 653475586, 131259507, 3327514739, 2190587206, 1651600213, 1160806992, 33177379, 538665224, 1627426816, 2179120931]]

private def n1 : Fin 2 → Rows :=
  ![![2589809801, 676752392, 904543394, 2266684169, 2147490320, 1735902224, 87479284, 1223111363, 257223989, 1184729266, 3639033224, 2305454055, 771003479, 3819553688, 1798688847, 1191032723, 730547542, 3141783323, 467534049, 1477329771, 2759714928, 1041154529, 677618007, 1049544161, 3408906534, 2598198408, 1223279703, 2478342499, 3449164641, 998622432, 4227520353, 746416634],
    ![1001281462, 45792731, 3317590620, 141223996, 4031554054, 2062452037, 2783027277, 408685629, 172292091, 2829329975, 3518085396, 27538689, 1654266436, 4290917909, 2752342472, 1387285969, 1849911069, 2191423049, 3920277305, 3276870725, 521866913, 3752219991, 1181051774, 192645811, 414691870, 3489309943, 24048496, 4210331383, 1889498371, 299982379, 1904130984, 419423675]]

private def n : Fin 2 → Rows :=
  ![![2083824864, 2083824864, 730482006, 1472127414, 730482006, 2083824864, 1472127414, 2083824864, 1472127414, 730482006, 2083824864, 730482006, 0, 1472127414, 1472127414, 0, 0, 1472127414, 2083824864, 0, 1472127414, 2083824864, 0, 2083824864, 2083824864, 2083824864, 0, 730482006, 0, 1472127414, 1472127414, 730482006],
    ![686370475, 1217860993, 1618885418, 0, 1618885418, 686370475, 1217860993, 1217860993, 686370475, 1618885418, 0, 686370475, 0, 686370475, 686370475, 1217860993, 1217860993, 686370475, 686370475, 686370475, 1618885418, 0, 1618885418, 1217860993, 1217860993, 1217860993, 0, 686370475, 0, 0, 0, 1217860993]]

private def nb : Fin 2 → Rows :=
  ![![2126933024, 2126933024, 1957198428, 174986876, 1957198428, 2126933024, 174986876, 2126933024, 174986876, 1957198428, 2126933024, 1957198428, 0, 174986876, 174986876, 0, 0, 174986876, 2126933024, 0, 174986876, 2126933024, 0, 2126933024, 2126933024, 2126933024, 0, 1957198428, 0, 174986876, 174986876, 1957198428],
    ![3673877554, 3747015165, 95159759, 0, 95159759, 3673877554, 3747015165, 3747015165, 3673877554, 95159759, 0, 3673877554, 0, 3673877554, 3673877554, 3747015165, 3747015165, 3673877554, 3673877554, 3673877554, 95159759, 0, 95159759, 3747015165, 3747015165, 3747015165, 0, 3673877554, 0, 0, 0, 3747015165]]

private def columns : Fin 2 → Rows :=
  ![![1672898027, 3813308726, 2674406125, 155799453, 100947652, 1010051668, 3782056100, 4187839755, 2883657331, 4231409643, 3705955908, 4287115175, 3587438392, 2959557506, 911862588, 2214647737, 1855029223, 3879021896, 3931484164, 3700715857, 262460897, 1268813497, 2807187042, 677798746, 1735515967, 802982959, 458098148, 69185726, 929139825, 189003683, 1941136861, 4103373988],
    ![2211545814, 1176655693, 119568035, 523704995, 1811892514, 3449382375, 2327591758, 1379753420, 2733512680, 2487270699, 3273196887, 2497106725, 271612972, 4246095308, 1776984024, 1789896242, 2594457114, 4236502443, 2349483031, 2246698983, 2860632714, 2314074218, 714918703, 81242667, 1305780935, 1712475410, 285500592, 3717299685, 67279290, 422956709, 1228061030, 1271220669]]

private def columnInverse : Fin 2 → Rows :=
  ![![4273269823, 2580791003, 263199542, 4154464358, 3022659722, 2609464464, 3334328471, 4256990967, 1138084146, 1051264722, 3385133594, 1553637915, 199499896, 527959190, 1027002223, 1373736061, 255567744, 142343731, 1437718225, 893925789, 1930571261, 4168748431, 1897076339, 1866306657, 4174276628, 1253315775, 3926551799, 696844782, 2739581095, 3195822153, 763941041, 3800784083],
    ![1551557520, 3163333021, 3527874643, 4122374279, 1902562498, 2804761949, 1856455431, 3380909410, 816548851, 212104810, 949183596, 1611437957, 1475059963, 3884582048, 3231705661, 3364410736, 464257235, 2808496085, 3196490492, 3104221366, 1445345129, 3304491290, 753890467, 2811572759, 2158115461, 2694178310, 777493455, 294500766, 980237941, 1934973561, 1805045876, 2590354943]]

private def columnParent : Fin 2 → Fin 31 → Fin 32 :=
  ![![0, 0, 1, 1, 2, 2, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 16, 17, 17],
    ![0, 0, 1, 1, 2, 2, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 19]]

private def columnActor : Fin 2 → Fin 31 → Fin 2 :=
  ![![0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]]

private def rows : Fin 2 → Rows :=
  ![![730482006, 150018674, 1957198428, 3293640563, 859717785, 1096394036, 2667137531, 3489982682, 1070794419, 1881883888, 3933234999, 1248332328, 2897482505, 4214255824, 2944917675, 1536253239, 2406177263, 1844122112, 2141543654, 304913342, 2568933003, 1691335735, 849845974, 3996353698, 2123350441, 4131899981, 71696, 1506925682, 3678857475, 3171591879, 3281228673, 2205603598],
    ![686370475, 1581032836, 3673877554, 764951143, 1551781988, 3835540120, 1517932715, 4049109088, 764817631, 2200286642, 709132141, 2677269655, 1240452844, 76169696, 1599870842, 3286921726, 2473370825, 1474970233, 3332550401, 1781676058, 1950512418, 3837609671, 2538635360, 3686255625, 1686413986, 3832125925, 1869520500, 1847249708, 3713670552, 1334221335, 649186309, 1738164029]]

private def rowInverse : Fin 2 → Rows :=
  ![![1359486466, 167877040, 853359553, 738391564, 1841602009, 2029748395, 554673835, 1521985904, 2983040792, 1105949392, 3356707352, 2611605542, 507889282, 2144933714, 2820162457, 2238942600, 3962088317, 2464090970, 388454544, 557360679, 646562588, 2769638547, 503138084, 2752614889, 175010582, 1670995676, 2511916770, 745442336, 1534347875, 4156463845, 1486658365, 3987430805],
    ![3155875852, 2864846288, 2462688644, 1864198369, 2001128465, 1590861666, 1042092430, 1842167626, 864887756, 2718067846, 1292691346, 3530586381, 512492839, 3763775163, 3509106997, 3052810203, 2377275959, 3607105722, 19105092, 2366997925, 1581010359, 1971261414, 2185923905, 1606716700, 860456806, 3167608163, 3933606748, 89894691, 3248591352, 989802172, 3776013734, 2908535136]]

private def rowParent : Fin 2 → Fin 31 → Fin 32 :=
  ![![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 16, 17],
    ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 16, 18]]

private def rowActor : Fin 2 → Fin 31 → Fin 2 :=
  ![![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1]]

private def transposedActors : Fin 2 → Fin 2 → Rows :=
  ![![![277737528, 3306720776, 4270426168, 3288719384, 1107563568, 2208129032, 2432754210, 35395634, 1947041320, 1099700232, 127793674, 33907424, 395077184, 1126790192, 358714400, 3289678368, 3264771112, 3298135592, 336140856, 33636872, 1150685232, 1401159720, 2499903497, 17631760, 3607949344, 3557819960, 1116829753, 1386058260, 1376878648, 2417835820, 2449557016, 2518187016],
    ![3156044349, 642886176, 946704412, 2821057284, 742248765, 2823653432, 2829604896, 898933565, 2556207385, 605616953, 3021848893, 2219438104, 3023393024, 2348881981, 880283932, 138873624, 3360751673, 139264060, 68258333, 543261216, 742246461, 873779224, 743556900, 808835108, 2751514677, 877953276, 2350208101, 342411583, 1946957886, 3154467589, 72964664, 2690920465]],
    ![![3805097508, 3091667001, 4281818333, 21453481, 2238673593, 3890250163, 3896767232, 3780457526, 535987690, 3930877740, 1817113911, 3847574772, 1764525563, 3867652574, 59934186, 2717402208, 1831634363, 4021649128, 4048901172, 1897496101, 1988305973, 303562752, 3930321667, 2168889891, 2265649292, 3335335460, 3359896323, 4048385328, 1387624657, 1377323141, 3953425884, 4159914860],
    ![246720718, 32371670, 1671248341, 3081286087, 121722219, 136839168, 10485760, 128124684, 430706388, 104581406, 265525411, 135978902, 2240563242, 2457056020, 2454420742, 30946041, 1917703376, 3090067005, 261929070, 2620425049, 518991142, 102484254, 104582430, 136387913, 2694465, 4219072, 4195392, 1176700684, 1111688972, 2483833361, 141033496, 2113792]]]

set_option maxRecDepth 100000 in
private theorem check_a2 : ∀ f : Fin 2, product (factorRows f 0) (factorRows f 0) = a2 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_a3 : ∀ f : Fin 2, product (a2 f) (factorRows f 0) = a3 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_g : ∀ f : Fin 2, product (a3 f) (factorRows f 1) = g f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_g2 : ∀ f : Fin 2, product (g f) (g f) = g2 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_g4 : ∀ f : Fin 2, product (g2 f) (g2 f) = g4 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_g8 : ∀ f : Fin 2, product (g4 f) (g4 f) = g8 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_n1 : ∀ f : Fin 2, product (add identity (g f)) (add identity (g2 f)) = n1 f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_n : ∀ f : Fin 2, product (n1 f) (add (add identity (g4 f)) (g8 f)) = n f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_nb : ∀ f : Fin 2, product (n f) (factorRows f 1) = nb f := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem check_rankOne : ∀ f : Fin 2, product (nb f) (n f) = rankOneRows (columns f 0) (rows f 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem column_parent_lt : ∀ (f : Fin 2) (i : Fin 31), columnParent f i < i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem column_step : ∀ (f : Fin 2) (i : Fin 31),
    rowProduct (columns f (columnParent f i)) (transposedActors f (columnActor f i)) = columns f i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem column_inverse : ∀ f : Fin 2, product (columnInverse f) (columns f) = identity := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_parent_lt : ∀ (f : Fin 2) (i : Fin 31), rowParent f i < i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_step : ∀ (f : Fin 2) (i : Fin 31),
    rowProduct (rows f (rowParent f i)) (factorRows f (rowActor f i)) = rows f i.succ := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem row_inverse : ∀ f : Fin 2, product (rowInverse f) (rows f) = identity := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem transpose_checked : ∀ (f a : Fin 2), matrix (transposedActors f a) = (factorMatrix f a).transpose := by
  decide +kernel

private lemma rankOne_mem (f : Fin 2) (Q : Subalgebra (ZMod 2) Mat)
    (h0 : factorMatrix f 0 ∈ Q) (h1 : factorMatrix f 1 ∈ Q) :
    vecMulVec (vector (columns f 0)) (vector (rows f 0)) ∈ Q := by
  have hI : matrix identity ∈ Q := by rw [matrix_identity]; exact Q.one_mem
  have ha2 := matrix_mul_mem Q _ _ _ h0 h0 (check_a2 f)
  have ha3 := matrix_mul_mem Q _ _ _ ha2 h0 (check_a3 f)
  have hg := matrix_mul_mem Q _ _ _ ha3 h1 (check_g f)
  have hg2 := matrix_mul_mem Q _ _ _ hg hg (check_g2 f)
  have hg4 := matrix_mul_mem Q _ _ _ hg2 hg2 (check_g4 f)
  have hg8 := matrix_mul_mem Q _ _ _ hg4 hg4 (check_g8 f)
  have hn1 := matrix_mul_mem Q _ _ _
    (matrix_add_mem Q _ _ hI hg) (matrix_add_mem Q _ _ hI hg2) (check_n1 f)
  have hn := matrix_mul_mem Q _ _ _ hn1
    (matrix_add_mem Q _ _ (matrix_add_mem Q _ _ hI hg4) hg8) (check_n f)
  have hnb := matrix_mul_mem Q _ _ _ hn h1 (check_nb f)
  rw [← matrix_rankOneRows]
  exact matrix_mul_mem Q _ _ _ hnb hn (check_rankOne f)

end G2DerivedPermutationFiltration.CycleData.FactorCertificate

namespace G2DerivedPermutationFiltration.CycleData
open FactorCertificate

/-- Each of the two literal cycle-factor matrix pairs generates the full binary
matrix algebra. All products and spanning certificates are kernel checked. -/
theorem fullFactorAlgebra (f : Fin 2) : FullFactorAlgebra f := by
  intro Q h0 h1
  have hA : ∀ a, factorMatrix f a ∈ Q := by
    intro a
    have ha : a = 0 ∨ a = 1 := by omega
    obtain rfl | rfl := ha
    · exact h0
    · exact h1
  apply full_of_orbits Q (factorMatrix f) hA (columns f) (rows f)
    (columnInverse f) (rowInverse f) (columnParent f) (rowParent f)
    (columnActor f) (rowActor f) (column_parent_lt f) (row_parent_lt f)
  · intro i
    have h := congrArg vector (column_step f i)
    rw [vector_rowProduct, transpose_checked, vecMul_transpose] at h
    exact h
  · intro i
    exact (vector_rowProduct _ _).symm.trans (congrArg vector (row_step f i))
  · exact column_inverse f
  · exact row_inverse f
  · exact rankOne_mem f Q h0 h1

end G2DerivedPermutationFiltration.CycleData
