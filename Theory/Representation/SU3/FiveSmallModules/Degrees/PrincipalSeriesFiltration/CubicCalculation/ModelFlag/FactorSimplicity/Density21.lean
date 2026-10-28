module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Assembly
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Density of the fixed cubic degree-21 image action

The two existing image matrices generate the full matrix algebra over the
four-element coefficient field. Write T = (A₀³ + I)⁷. The checked straight-line
program below produces T A₁³ A₀ T = u vᵀ. The generator orbits of u and v
contain bases, certified by explicit left inverses. The rank-one criterion
then gives every matrix unit in any coefficient subalgebra containing A₀, A₁.

All numerical witnesses come from `source/image_density.json` beside the
parent Data module. Its columns are stored as rows; the column recurrence
below converts that storage to the actual left matrix action. Every used
identity is checked by Lean's kernel through the proved packed arithmetic.
No diagnostic Python result is used as a proof.

The final corollary discharges the image-density premise of the existing
literal quotient certificates. Only the independent degree-84 middle density
remains for the parent assembly.

Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density21
open Certificate.Packed

def p0 : Fin 21 → Row := ![
    (1, 0), (2, 0), (4, 0),
    (8, 0), (16, 0), (32, 0),
    (64, 0), (128, 0), (256, 0),
    (512, 0), (1024, 0), (2048, 0),
    (4096, 0), (8192, 0), (16384, 0),
    (32768, 0), (65536, 0), (131072, 0),
    (262144, 0), (524288, 0), (1048576, 0)]
def p1 : Fin 21 → Row := ![
    (603776, 666881), (134096, 143040), (929536, 1092),
    (468546, 598080), (410688, 597888), (1904704, 734464),
    (858560, 8512), (928192, 868288), (530624, 11712),
    (635456, 271744), (134216, 2944), (11200, 726336),
    (725184, 394816), (597888, 147328), (865024, 856704),
    (132096, 9024), (8896, 139712), (998528, 726272),
    (725312, 402752), (984928, 987008), (991040, 917568)]
def p2 : Fin 21 → Row := ![
    (1854596, 1327680), (1844801, 1713280), (1728960, 1327168),
    (13952, 1199168), (477696, 943104), (1183298, 1190400),
    (550464, 1466496), (1835520, 1730752), (1844448, 1707552),
    (1180288, 1188928), (1450624, 1180160), (1575496, 1469504),
    (534144, 1721984), (1860672, 1574528), (1066176, 1582784),
    (134864, 1052160), (540800, 1713856), (550080, 286784),
    (1056832, 132224), (960000, 966784), (528000, 418432)]
def p3 : Fin 21 → Row := ![
    (1017385, 856297), (50880, 360584), (104108, 918220),
    (429080, 990432), (985608, 39144), (984672, 592488),
    (398368, 329408), (265440, 891432), (204384, 721096),
    (165408, 131272), (329290, 295040), (758976, 787112),
    (67296, 431752), (300072, 299976), (230944, 496160),
    (730696, 566464), (492544, 136832), (332328, 196840),
    (65568, 329288), (1740904, 758376), (824040, 852576)]
def p4 : Fin 21 → Row := ![
    (1677675, 1774626), (491848, 262402), (1742862, 361826),
    (934218, 1114216), (494626, 1313794), (1086824, 2006306),
    (1905928, 950536), (1514760, 1414178), (1939272, 857954),
    (1359112, 11330), (229402, 458752), (660584, 1479970),
    (2005064, 296970), (1706250, 364802), (1937416, 1675584),
    (557418, 789800), (1480, 688200), (1415170, 1316162),
    (1317120, 691530), (1511522, 2069602), (1674338, 1938528)]
def p5 : Fin 21 → Row := ![
    (1677674, 1774626), (491850, 262402), (1742858, 361826),
    (934210, 1114216), (494642, 1313794), (1086792, 2006306),
    (1905992, 950536), (1514888, 1414178), (1939016, 857954),
    (1359624, 11330), (230426, 458752), (662632, 1479970),
    (2000968, 296970), (1714442, 364802), (1953800, 1675584),
    (524650, 789800), (67016, 688200), (1546242, 1316162),
    (1054976, 691530), (2035810, 2069602), (625762, 1938528)]
def p6 : Fin 21 → Row := ![
    (1530848, 1114832), (286082, 464704), (416544, 131312),
    (1329992, 150208), (1378536, 1184056), (16464, 1444368),
    (350352, 82496), (1331824, 465872), (1069456, 473744),
    (344336, 560), (478400, 395712), (482064, 1376336),
    (344096, 479552), (325984, 72640), (68514, 6626),
    (49152, 1329968), (217968, 86528), (465632, 196624),
    (32, 148080), (594304, 268688), (530928, 1968368)]
def p7 : Fin 21 → Row := ![
    (2698, 1712818), (208912, 2562), (1054762, 8754),
    (1706040, 532658), (1188496, 1712664), (590354, 1245834),
    (70344, 399530), (1585682, 534538), (1772306, 758314),
    (202898, 144010), (97810, 90642), (592562, 1187882),
    (211120, 75938), (674, 137394), (227330, 7842),
    (768792, 1061682), (203304, 211466), (137736, 201360),
    (393978, 198848), (598568, 1247376), (1247376, 1714872)]
def p8 : Fin 21 → Row := ![
    (1720706, 636578), (191768, 154378), (1589698, 898722),
    (90008, 260746), (504448, 500160), (18442, 197778),
    (85208, 280586), (129738, 435474), (23370, 308754),
    (285514, 177746), (177746, 453912), (154378, 46610),
    (65048, 125322), (18442, 197778), (369024, 267072),
    (221144, 522890), (221144, 522890), (262144, 393280),
    (459922, 347352), (238016, 398080), (398080, 373440)]
def p9 : Fin 21 → Row := ![
    (129738, 435474), (131136, 262144), (129738, 435474),
    (0, 0), (131136, 262144), (131136, 262144),
    (393280, 131136), (0, 0), (262144, 393280),
    (262144, 393280), (393280, 131136), (262144, 393280),
    (262144, 393280), (131136, 262144), (262144, 393280),
    (0, 0), (0, 0), (0, 0),
    (262144, 393280), (262144, 393280), (393280, 131136)]
def p10 : Fin 21 → Row := ![
    (1854596, 1327680), (1844801, 1713280), (1728960, 1327168),
    (13952, 1199168), (477696, 943104), (1183298, 1190400),
    (550464, 1466496), (1835520, 1730752), (1844448, 1707552),
    (1180288, 1188928), (1450624, 1180160), (1575496, 1469504),
    (534144, 1721984), (1860672, 1574528), (1066176, 1582784),
    (134864, 1052160), (540800, 1713856), (550080, 286784),
    (1056832, 132224), (960000, 966784), (528000, 418432)]
def p11 : Fin 21 → Row := ![
    (1475336, 1231936), (411716, 1344000), (35872, 1099872),
    (281088, 410696), (1101320, 1460800), (1461321, 1066568),
    (1347072, 163904), (1182784, 34312), (1181250, 1493578),
    (1051648, 1466944), (1181760, 1180160), (1497160, 51720),
    (281152, 296960), (1441792, 164416), (427520, 1461248),
    (1525832, 1329736), (1706496, 1476608), (1344512, 1099840),
    (1050112, 412224), (1461328, 181328), (34376, 1478336)]
def p12 : Fin 21 → Row := ![
    (291056, 402552), (278984, 286800), (148698, 131098),
    (131208, 29824), (807000, 140360), (29836, 152576),
    (263320, 139408), (278728, 1339472), (156801, 28697),
    (148616, 24640), (8392, 16448), (282776, 421976),
    (421064, 411864), (24704, 8720), (140432, 271432),
    (274632, 413896), (172168, 303320), (148496, 132120),
    (17408, 16520), (476232, 74832), (275472, 279640)]
def p13 : Fin 21 → Row := ![
    (1599168, 1720394), (662082, 750080), (613914, 807634),
    (142338, 527432), (945698, 790602), (662218, 401996),
    (744458, 551552), (656514, 480832), (866953, 487426),
    (393226, 273024), (14850, 727104), (425154, 220738),
    (9802, 19586), (327872, 786112), (86664, 666634),
    (987650, 139330), (274498, 415298), (878280, 548874),
    (406088, 10370), (533706, 151048), (423112, 556938)]
def p14 : Fin 21 → Row := ![
    (841792, 815273), (397888, 397376), (841792, 815273),
    (0, 0), (397888, 397376), (397888, 397376),
    (512, 397888), (0, 0), (397376, 512),
    (397376, 512), (512, 397888), (397376, 512),
    (397376, 512), (397888, 397376), (397376, 512),
    (0, 0), (0, 0), (0, 0),
    (397376, 512), (397376, 512), (512, 397888)]
def p15 : Fin 21 → Row := ![
    (304466, 221144), (0, 0), (304466, 221144),
    (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0)]
def cols : Fin 21 → Row := ![
    (5, 0), (3, 0), (8, 1),
    (34, 0), (1025, 1), (2048, 2),
    (524296, 0), (288, 256), (1745948, 932791),
    (1765737, 391960), (1191366, 533915), (1083441, 35208),
    (1996773, 1722553), (1782215, 618898), (1820471, 1861830),
    (260, 260), (131055, 364617), (1752564, 1371692),
    (131080, 8), (1983444, 1589385), (2042737, 716907)]
def rows : Fin 21 → Row := ![
    (304466, 221144), (1508433, 733864), (162440, 1359843),
    (500740, 1601602), (890755, 1475865), (1078824, 1060383),
    (597192, 466932), (1879312, 1730177), (177593, 934026),
    (584917, 102644), (1742799, 248287), (1323138, 480141),
    (734638, 1564876), (1768616, 1679818), (680681, 440489),
    (2050744, 1492708), (1528394, 471091), (233590, 1719457),
    (151852, 1146561), (1035228, 1421202), (177045, 1546685)]
def ci : Fin 21 → Row := ![
    (32906, 32907), (32904, 32907), (32907, 32907),
    (32911, 1), (1688372, 437691), (32896, 32907),
    (509594, 1714735), (1394303, 43488), (32907, 139),
    (644709, 946045), (17, 32906), (32939, 3),
    (1012277, 266151), (1576102, 1690811), (820367, 432238),
    (1821740, 1273550), (356035, 536512), (295054, 32911),
    (1961548, 1731272), (32975, 1), (1130526, 527917)]
def ri : Fin 21 → Row := ![
    (1929307, 341526), (1023492, 882518), (967119, 433114),
    (1232378, 162875), (31994, 2046190), (790015, 1665137),
    (1725129, 746828), (1480949, 1431481), (445075, 171524),
    (853198, 1195489), (1548255, 1022926), (417840, 2093232),
    (548762, 84381), (957259, 804381), (1470298, 2064082),
    (1437336, 7540), (6044, 586235), (1270846, 1505069),
    (1875851, 1208985), (1326230, 354776), (1422080, 1887602)]
def cp : Fin 20 → Fin 21 := ![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10]
def rp : Fin 20 → Fin 21 := ![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10]
def ca : Fin 20 → Fin 2 := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
def ra : Fin 20 → Fin 2 := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

def vector {n : ℕ} (r : Row) : Fin n → CoefficientField := fun i => entry r i.val

def column {n : ℕ} (r : Row) : Fin n → Row := fun i =>
  (if r.1.testBit i.val then 1 else 0, if r.2.testBit i.val then 1 else 0)

theorem column_entry {n : ℕ} (r : Row) (i : Fin n) :
    entry (column r i) 0 = entry r i.val := by
  cases h₁ : r.1.testBit i.val <;> cases h₂ : r.2.testBit i.val <;>
    simp [column, entry, h₁, h₂]

theorem column_mul {n : ℕ} (a : Fin n → Row) (r s : Row)
    (h : ∀ i, mul a (column (n := n) r) i = column s i) :
    (matrix n a).mulVec (vector r) = vector s := by
  funext i
  have he := congrArg (fun M => M i (0 : Fin 1))
    (matrix_mul (p := 1) a (column (n := n) r))
  change entry (mul a (column (n := n) r) i) 0 =
    ∑ j : Fin n, entry (a i) j.val * entry (column r j) 0 at he
  simp only [column_entry, h] at he
  exact he.symm

theorem row_mul {n : ℕ} (a : Fin n → Row) (r s : Row)
    (h : mul (fun _ : Fin 1 => r) a 0 = s) :
    Matrix.vecMul (vector r) (matrix n a) = vector s := by
  funext i
  have he := congrArg (fun M => M (0 : Fin 1) i)
    (matrix_mul (p := n) (fun _ : Fin 1 => r) a)
  change entry (mul (fun _ : Fin 1 => r) a 0) i.val =
    ∑ j : Fin n, entry r j.val * entry (a j) i.val at he
  rw [h] at he
  exact he.symm

theorem matrix_add_rows {m n : ℕ} (a b : Fin m → Row) :
    matrix n (fun i => add (a i) (b i)) = matrix n a + matrix n b := by
  apply Matrix.ext
  intro i j
  exact entry_add _ _ _

theorem span_rows_of_inverse {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    (M N : Matrix n n k) (h : N * M = 1) :
    Submodule.span k (Set.range M) = ⊤ := by
  change Submodule.span k (Set.range M.row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro x
  refine ⟨Matrix.vecMul x N, ?_⟩
  change Matrix.vecMul (Matrix.vecMul x N) M = x
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
theorem step_0 : matrix 21 p0 = 1 := by
  have h : ∀ i, p0 i = identity 21 i := by decide +kernel
  rw [funext h, matrix_identity]

theorem step_1 : matrix 21 p1 = imageMatrices 0 := by rfl

theorem step_2 : matrix 21 p2 = imageMatrices 1 := by rfl

theorem step_3 : matrix 21 p3 = matrix 21 p1 * matrix 21 p1 := by
  have h : ∀ i, mul p1 p1 i = p3 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_4 : matrix 21 p4 = matrix 21 p3 * matrix 21 p1 := by
  have h : ∀ i, mul p3 p1 i = p4 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_5 : matrix 21 p5 = matrix 21 p4 + matrix 21 p0 := by
  have h : ∀ i, add (p4 i) (p0 i) = p5 i := by decide +kernel
  rw [← matrix_add_rows, funext h]

theorem step_6 : matrix 21 p6 = matrix 21 p5 * matrix 21 p5 := by
  have h : ∀ i, mul p5 p5 i = p6 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_7 : matrix 21 p7 = matrix 21 p6 * matrix 21 p6 := by
  have h : ∀ i, mul p6 p6 i = p7 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_8 : matrix 21 p8 = matrix 21 p7 * matrix 21 p6 := by
  have h : ∀ i, mul p7 p6 i = p8 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_9 : matrix 21 p9 = matrix 21 p8 * matrix 21 p5 := by
  have h : ∀ i, mul p8 p5 i = p9 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_10 : matrix 21 p10 = matrix 21 p0 * matrix 21 p2 := by
  have h : ∀ i, mul p0 p2 i = p10 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_11 : matrix 21 p11 = matrix 21 p10 * matrix 21 p2 := by
  have h : ∀ i, mul p10 p2 i = p11 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_12 : matrix 21 p12 = matrix 21 p11 * matrix 21 p2 := by
  have h : ∀ i, mul p11 p2 i = p12 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_13 : matrix 21 p13 = matrix 21 p12 * matrix 21 p1 := by
  have h : ∀ i, mul p12 p1 i = p13 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_14 : matrix 21 p14 = matrix 21 p9 * matrix 21 p13 := by
  have h : ∀ i, mul p9 p13 i = p14 i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem step_15 : matrix 21 p15 = matrix 21 p14 * matrix 21 p9 := by
  have h : ∀ i, mul p14 p9 i = p15 i := by decide +kernel
  rw [← matrix_mul, funext h]


theorem rank_one : matrix 21 p15 = Matrix.vecMulVec
    (vector (cols 0)) (vector (rows 0)) := by
  have h : ∀ i : Fin 21, p15 i =
      scale ((cols 0).1.testBit i.val) ((cols 0).2.testBit i.val) (rows 0) :=
    by decide +kernel
  apply Matrix.ext
  intro i j
  change entry (p15 i) j.val = entry (cols 0) i.val * entry (rows 0) j.val
  rw [h, entry_scale]
  rfl

theorem cols_step (i : Fin 20) :
    (imageMatrices (ca i)).mulVec (vector (cols (cp i))) = vector (cols i.succ) := by
  have h : ∀ (i : Fin 20) (j : Fin 21),
      mul (A (ca i)) (column (n := 21) (cols (cp i))) j = column (cols i.succ) j :=
    by decide +kernel
  exact column_mul _ _ _ (h i)

theorem rows_step (i : Fin 20) :
    Matrix.vecMul (vector (rows (rp i))) (imageMatrices (ra i)) = vector (rows i.succ) := by
  have h : ∀ i : Fin 20,
      mul (fun _ : Fin 1 => rows (rp i)) (A (ra i)) 0 = rows i.succ := by decide +kernel
  exact row_mul _ _ _ (h i)

theorem cp_lt (i : Fin 20) : cp i < i.succ := by
  have h : ∀ i : Fin 20, cp i < i.succ := by decide +kernel
  exact h i

theorem rp_lt (i : Fin 20) : rp i < i.succ := by
  have h : ∀ i : Fin 20, rp i < i.succ := by decide +kernel
  exact h i

theorem cols_inverse : matrix 21 ci * matrix 21 cols = 1 := by
  have h : ∀ i, mul ci cols i = identity 21 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

theorem rows_inverse : matrix 21 ri * matrix 21 rows = 1 := by
  have h : ∀ i, mul ri rows i = identity 21 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

attribute [local irreducible] p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  cols rows ci ri cp ca rp ra imageMatrices A A0 A1

theorem rank_one_mem
    (Q : Subalgebra CoefficientField (Matrix (Fin 21) (Fin 21) CoefficientField))
    (h : ∀ a, imageMatrices a ∈ Q) :
    Matrix.vecMulVec (vector (cols 0)) (vector (rows 0)) ∈ Q := by

  have hp0 : matrix 21 p0 ∈ Q := by
    rw [step_0]
    exact Q.one_mem

  have hp1 : matrix 21 p1 ∈ Q := by
    rw [step_1]
    exact h 0

  have hp2 : matrix 21 p2 ∈ Q := by
    rw [step_2]
    exact h 1

  have hp3 : matrix 21 p3 ∈ Q := by
    rw [step_3]
    exact Q.mul_mem hp1 hp1

  have hp4 : matrix 21 p4 ∈ Q := by
    rw [step_4]
    exact Q.mul_mem hp3 hp1

  have hp5 : matrix 21 p5 ∈ Q := by
    rw [step_5]
    exact Q.add_mem hp4 hp0

  have hp6 : matrix 21 p6 ∈ Q := by
    rw [step_6]
    exact Q.mul_mem hp5 hp5

  have hp7 : matrix 21 p7 ∈ Q := by
    rw [step_7]
    exact Q.mul_mem hp6 hp6

  have hp8 : matrix 21 p8 ∈ Q := by
    rw [step_8]
    exact Q.mul_mem hp7 hp6

  have hp9 : matrix 21 p9 ∈ Q := by
    rw [step_9]
    exact Q.mul_mem hp8 hp5

  have hp10 : matrix 21 p10 ∈ Q := by
    rw [step_10]
    exact Q.mul_mem hp0 hp2

  have hp11 : matrix 21 p11 ∈ Q := by
    rw [step_11]
    exact Q.mul_mem hp10 hp2

  have hp12 : matrix 21 p12 ∈ Q := by
    rw [step_12]
    exact Q.mul_mem hp11 hp2

  have hp13 : matrix 21 p13 ∈ Q := by
    rw [step_13]
    exact Q.mul_mem hp12 hp1

  have hp14 : matrix 21 p14 ∈ Q := by
    rw [step_14]
    exact Q.mul_mem hp9 hp13

  have hp15 : matrix 21 p15 ∈ Q := by
    rw [step_15]
    exact Q.mul_mem hp14 hp9

  rw [← rank_one]
  exact hp15


theorem column_orbit
    (Q : Subalgebra CoefficientField (Matrix (Fin 21) (Fin 21) CoefficientField))
    (h : ∀ a, imageMatrices a ∈ Q) (i : Fin 21) :
    ∃ L ∈ Q, L.mulVec (vector (cols 0)) = vector (cols i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, hLu⟩ := ih (cp i) (cp_lt i)
      refine ⟨imageMatrices (ca i) * L, Q.mul_mem (h _) hL, ?_⟩
      rw [← Matrix.mulVec_mulVec, hLu, cols_step]

theorem row_orbit
    (Q : Subalgebra CoefficientField (Matrix (Fin 21) (Fin 21) CoefficientField))
    (h : ∀ a, imageMatrices a ∈ Q) (i : Fin 21) :
    ∃ R ∈ Q, Matrix.vecMul (vector (rows 0)) R = vector (rows i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, hvR⟩ := ih (rp i) (rp_lt i)
      refine ⟨R * imageMatrices (ra i), Q.mul_mem hR (h _), ?_⟩
      rw [← Matrix.vecMul_vecMul, hvR, rows_step]

theorem density
    (Q : Subalgebra CoefficientField (Matrix (Fin 21) (Fin 21) CoefficientField))
    (h : ∀ a, imageMatrices a ∈ Q) : Q = ⊤ := by
  choose L hL hLu using column_orbit Q h
  choose R hR hvR using row_orbit Q h
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q (vector (cols 0)) (vector (rows 0)) L R hL hR (rank_one_mem Q h)
  · have hc : (fun i => (L i).mulVec (vector (cols 0))) = matrix 21 cols := funext hLu
    rw [hc]
    exact span_rows_of_inverse _ _ cols_inverse
  · have hr : (fun i => Matrix.vecMul (vector (rows 0)) (R i)) = matrix 21 rows := funext hvR
    rw [hr]
    exact span_rows_of_inverse _ _ rows_inverse

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density21

namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
universe v

/-- The exact degree-21 image matrices generate the full coefficient-field matrix algebra. -/
public theorem image_density : CubicCalculation.FactorSimplicity.MatrixDensity imageMatrices :=
  Density21.density

/-- Apply the image calculation to the original cubic flag certificates.
The independent middle-density proof is the sole remaining premise. -/
public theorem modelCertificates_of_middle_density
    (hm : CubicCalculation.FactorSimplicity.MatrixDensity middleMatrices) :
    CubicCalculation.FactorSimplicity.ModelCertificates.{v} :=
  modelCertificates_of_density image_density hm

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
