module
public import Theory.Representation.Mathieu.M22James.SylowFixed
public import Theory.GroupTheory.TwoThreeSolvable
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Native generators for the escaping triple-Mathieu overgroup

The seven letters are actual words in the ATLAS generators of 3.M₂₂.2.
They consist of four two-elements, the central scalar and its inverse, and
one moving involution. Explicit matrix products certify every word.
A common binary triangular flag supplies the two-subgroup used by the
coset and Sylow certificates in `SolvableOvergroup`.

This is the native calculation used in Aschbacher–Smith 14.7.36, printed
p.1059. The original ATLAS matrices and attribution are retained in the
imported J₄ `LinearModel/source/` files. No external group computation is
used as a proof.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.Escape.Certificate
open Ambient
def c : actionGroup := ⟨unitC,unitC_mem_actionGroup⟩
def d : actionGroup := ⟨unitD,unitD_mem_actionGroup⟩
def a : actionGroup := d⁻¹*c*d^2*c*d
def b : actionGroup := d*c*d⁻¹*(c*d)^3*d*(c*d⁻¹)^2*c*d*c*(d*c*d)^2*d
def z : actionGroup := (d*c*d)^3*c*d*c*d⁻¹*c*(d*c*d)^3
def t : actionGroup := (d*c*d)^2*(c*d)^2*d*c*d⁻¹*c*d*(d*c)^2*d^2*(c*d⁻¹)^2*c*d^2*c*d⁻¹*c
def e : actionGroup := ((c*d)^2*d^2)^4
def m : actionGroup := (d*c)^4*d⁻¹*c*d*(d*c)^2*(d*c*d)^2*c*d⁻¹*(c*d)^2*d
def words : Fin 7 → actionGroup := ![a,b,z,t,e,m,e⁻¹]
def matrices : Fin 7 → Matrix12 := ![
  fromRows ![509,1513,4,256,148,164,64,128,8,624,147,3095],
  fromRows ![916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],
  fromRows ![1310,1382,1376,558,1530,174,1913,678,786,654,1217,2671],
  fromRows ![916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],
  fromRows ![1533,1919,3296,1102,3735,278,3833,2183,1086,3449,1390,3810],
  fromRows ![58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536],
  fromRows ![1532,1917,3300,1094,3719,310,3769,2055,1342,3961,366,1762]]
def inverses : Fin 7 → Matrix12 := ![
  fromRows ![509,1513,4,256,148,164,64,128,8,624,147,3095],
  fromRows ![916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],
  fromRows ![1310,1382,1376,558,1530,174,1913,678,786,654,1217,2671],
  fromRows ![916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],
  fromRows ![1532,1917,3300,1094,3719,310,3769,2055,1342,3961,366,1762],
  fromRows ![58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536],
  fromRows ![1533,1919,3296,1102,3735,278,3833,2183,1086,3449,1390,3810]]
def units (i : Fin 7) : Matrix12ˣ where
  val := matrices i
  inv := inverses i
  val_inv := by revert i; decide +kernel
  inv_val := by revert i; decide +kernel
theorem words_matrix_0 : ((words 0 : Matrix12ˣ) : Matrix12) = matrices 0 := by decide +kernel
theorem words_matrix_1 : ((words 1 : Matrix12ˣ) : Matrix12) = matrices 1 := by decide +kernel
theorem words_matrix_2 : ((words 2 : Matrix12ˣ) : Matrix12) = matrices 2 := by decide +kernel
theorem words_matrix_3 : ((words 3 : Matrix12ˣ) : Matrix12) = matrices 3 := by decide +kernel
theorem words_matrix_4 : ((words 4 : Matrix12ˣ) : Matrix12) = matrices 4 := by
  have he : ((unitC * unitD)^2 * unitD^2)^4 = scalarUnit := by
    simp only [scalarUnit,coreA,coreB,pow_two]
  change ((((unitC * unitD)^2 * unitD^2)^4 : Matrix12ˣ) : Matrix12) = _
  rw [he,coe_scalarUnit]
  decide +kernel
theorem words_matrix_5 : ((words 5 : Matrix12ˣ) : Matrix12) = matrices 5 := by
  let dc : Matrix12 := fromRows ![7,32,64,1,100,512,1024,1185,3453,3061,412,3524]
  have hdc : matrixD * matrixC = dc := by decide +kernel
  let dc2 : Matrix12 := fromRows ![103,512,1024,7,1600,3061,412,1850,1799,2510,2553,452]
  have hdc2 : dc ^ 2 = dc2 := by decide +kernel
  let dc4 : Matrix12 := fromRows ![3086,2510,2553,1639,427,121,634,2178,343,1634,3504,1441]
  have hdc4 : dc2 * dc2 = dc4 := by decide +kernel
  let dcd : Matrix12 := fromRows ![28,128,256,4,400,2976,1639,1513,1412,2891,2823,1559]
  have hdcd : dc * matrixD = dcd := by decide +kernel
  let dcd2 : Matrix12 := fromRows ![148,1513,1412,256,509,1681,3095,1717,2666,3623,2372,64]
  have hdcd2 : dcd ^ 2 = dcd2 := by decide +kernel
  let cd2 : Matrix12 := fromRows ![128,28,412,2976,1639,4,400,2891,2823,1513,1412,1499]
  have hcd2 : (matrixC * matrixD) ^ 2 = cd2 := by decide +kernel
  have hfour : dc ^ 4 = dc4 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl,pow_add,hdc2,hdc4]
  change (matrixD * matrixC)^4 * matrixDInv * matrixC * matrixD * (matrixD * matrixC)^2 *
    (matrixD * matrixC * matrixD)^2 * matrixC * matrixDInv * (matrixC * matrixD)^2 * matrixD = _
  rw [hdc,hfour,hdc2,hdcd,hdcd2,hcd2]
  let p0 : Matrix12 := fromRows ![3095,2817,2233,1024,991,2521,2308,296,2616,1054,4050,3785]
  have h0 : dc4 * matrixDInv = p0 := by decide +kernel
  rw [h0]
  let p1 : Matrix12 := fromRows ![3129,2559,3863,256,1780,2831,2426,1064,3477,358,2732,3791]
  have h1 : p0 * matrixC = p1 := by decide +kernel
  rw [h1]
  let p2 : Matrix12 := fromRows ![3220,225,4014,2048,3906,2516,1023,1765,1804,2456,594,1465]
  have h2 : p1 * matrixD = p2 := by decide +kernel
  rw [h2]
  let p3 : Matrix12 := fromRows ![3399,3380,3132,452,1384,549,954,2307,823,1982,3090,1041]
  have h3 : p2 * dc2 = p3 := by decide +kernel
  rw [h3]
  let p4 : Matrix12 := fromRows ![3968,390,2796,1356,2216,3494,381,3927,984,3517,3344,2093]
  have h4 : p3 * dcd2 = p4 := by decide +kernel
  rw [h4]
  let p5 : Matrix12 := fromRows ![2813,1542,4034,1335,3925,2675,1149,2217,1776,2576,2109,3408]
  have h5 : p4 * matrixC = p5 := by decide +kernel
  rw [h5]
  let p6 : Matrix12 := fromRows ![2098,3551,1748,3812,1766,2073,1220,663,1074,462,690,1586]
  have h6 : p5 * matrixDInv = p6 := by decide +kernel
  rw [h6]
  let p7 : Matrix12 := fromRows ![932,3396,3405,3829,2866,2204,3779,2501,1019,3068,2269,1554]
  have h7 : p6 * cd2 = p7 := by decide +kernel
  rw [h7]
  let p8 : Matrix12 := fromRows ![58,1309,1307,1324,2397,2413,1451,116,315,2893,2153,3536]
  have h8 : p7 * matrixD = p8 := by decide +kernel
  rw [h8]
  rfl
theorem words_matrix_6 : ((words 6 : Matrix12ˣ) : Matrix12) = matrices 6 := by
  have he : ((e : actionGroup) : Matrix12ˣ) = units 4 := Units.ext words_matrix_4
  change ((((e : actionGroup) : Matrix12ˣ)⁻¹ : Matrix12ˣ) : Matrix12) = _
  rw [he]
  rfl
theorem words_matrix (i : Fin 7) : ((words i : Matrix12ˣ) : Matrix12) = matrices i := by
  fin_cases i
  · exact words_matrix_0
  · exact words_matrix_1
  · exact words_matrix_2
  · exact words_matrix_3
  · exact words_matrix_4
  · exact words_matrix_5
  · exact words_matrix_6

def gen (i : Fin 7) : actionGroup :=
  ⟨units i, (Units.ext (words_matrix i) : (words i : Matrix12ˣ) = units i) ▸ (words i).property⟩
def inverseIndex : Fin 7 → Fin 7 := ![0,1,2,3,6,5,4]
theorem gen_inv (i : Fin 7) : gen (inverseIndex i) = (gen i)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  revert i
  decide +kernel
def H : Subgroup actionGroup := closure (Set.range gen)
theorem gen_mem (i : Fin 7) : gen i ∈ H := subset_closure ⟨i,rfl⟩
def basis : Matrix12 := fromRows ![293,100,1842,192,1072,768,1704,1696,128,1024,512,2048]
def basisInv : Matrix12 := fromRows ![1323,52,1674,192,1424,1920,264,256,1056,1024,512,2048]
def basisUnit : Matrix12ˣ where
  val := basis
  inv := basisInv
  val_inv := by decide +kernel
  inv_val := by decide +kernel
def coordinates : actionGroup →* Matrix12 :=
  (Units.coeHom Matrix12).comp ((MulAut.conj basisUnit⁻¹).toMonoidHom.comp actionGroup.subtype)
theorem coordinates_injective : Function.Injective coordinates :=
  Units.val_injective.comp ((MulAut.conj basisUnit⁻¹).injective.comp actionGroup.subtype_injective)
def lowerMonoid : Submonoid actionGroup :=
  (Matrix.blockTriangularSubsemiring (ZMod 2) (OrderDual.toDual : Fin 12 → OrderDual (Fin 12))).toSubmonoid.comap coordinates
def lower : Subgroup actionGroup where
  carrier := lowerMonoid
  one_mem' := lowerMonoid.one_mem
  mul_mem' := lowerMonoid.mul_mem
  inv_mem' := by
    intro a ha
    change a⁻¹ ∈ lowerMonoid
    rw [←one_mul a⁻¹,←pow_one a,←pow_orderOf_eq_one a,←pow_sub a (orderOf_pos a)]
    exact lowerMonoid.pow_mem ha _
theorem lower_two : IsPGroup 2 lower := by
  apply IsPGroup.of_injective_binary_lowerTriangular (coordinates.comp lower.subtype)
    (coordinates_injective.comp lower.subtype_injective)
  intro g i j hij
  exact g.property hij
def K : Subgroup H := lower.subgroupOf H
theorem K_two : IsPGroup 2 K := lower_two.comap_subtype
def pcWords : Fin 8 → List (Fin 7) := ![[3],[3,0,3,1,2,0,1,0],[1],[3,2,0,3,2],[0,3,1,0,3,1,0],[1,2,0,2,1,0],[0],[2,0,2,0]]
def pc (i : Fin 8) : actionGroup := ((pcWords i).map gen).prod
def pcMatrices : Fin 8 → Matrix12 := ![
  fromRows ![916,1735,1129,558,472,174,1648,14,1432,38,1888,3819],
  fromRows ![551,1543,312,1303,2017,1773,116,1451,1055,1012,1774,2837],
  fromRows ![916,1735,1130,556,1265,175,858,922,1505,1761,1818,3781],
  fromRows ![509,867,504,673,2018,1582,444,380,937,1703,147,4082],
  fromRows ![1848,855,1128,1841,1330,366,1869,1933,1549,1143,278,3703],
  fromRows ![1776,1309,1519,1549,1265,298,64,128,538,1761,1019,3589],
  fromRows ![509,1513,4,256,148,164,64,128,8,624,147,3095],
  fromRows ![1322,2,1307,1315,901,1706,1375,1439,1067,405,1953,2240]]
theorem pc_matrix (i : Fin 8) : ((pc i : Matrix12ˣ) : Matrix12) = pcMatrices i := by
  revert i
  decide +kernel
theorem pc_mem (i : Fin 8) : pc i ∈ H :=
  H.list_prod_mem (by intro g hg; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg; exact gen_mem j)
theorem pc_lower (i : Fin 8) : pc i ∈ lower := by
  change (basisInv * (((pc i : actionGroup) : Matrix12ˣ) : Matrix12) * basis).BlockTriangular
    (OrderDual.toDual : Fin 12 → OrderDual (Fin 12))
  rw [pc_matrix]
  revert i
  decide +kernel

end Sporadic.Mathieu.M22TripleCover.Escape.Certificate
