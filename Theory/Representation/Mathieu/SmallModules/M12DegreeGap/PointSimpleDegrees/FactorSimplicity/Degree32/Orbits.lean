module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree32.Peak

/-!
# Degree-32 cyclic bases for the M₁₁ coset factor

The packed columns use exactly `Data.modelMatrix`, acting on column vectors.
All finite identities are checked by the Lean kernel. The low-rank operator
and the orbit bases are reproduced by `../source/discover.py` and `export.py`.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree32
open Matrix

def transpose0 : Fin 32 → ℕ := fun j => (#[2, 1, 8, 4, 64, 128, 16, 32, 2048, 8192, 32768, 256, 262144, 512, 1048576, 1024, 8388608, 8619248, 4096, 134217728, 16384, 1073741824, 1385065507, 65536, 1748948935, 1908985876, 1725435243, 524288, 2033895271, 1237285067, 2097152, 3670394812] : Array ℕ)[j.val]!

def transpose1 : Fin 32 → ℕ := fun j => (#[16, 1, 2, 4096, 4, 8, 2097152, 16777216, 32, 64, 128, 2147483648, 256, 1572690379, 512, 3330901500, 1024, 2048, 1443205168, 8192, 2447337508, 16384, 32768, 1772543937, 65536, 131072, 262144, 2959583711, 524288, 1048576, 2402744635, 33554432] : Array ℕ)[j.val]!

def transposes : Fin 2 → Fin 32 → ℕ := ![transpose0, transpose1]

theorem transposes_eq : ∀ s, matrix (m := 32) (transposes s) = (matrix (generators s)).transpose := by decide +kernel

def columns : Fin 32 → ℕ := fun j => (#[498319103, 1674569727, 3749541815, 1610545899, 3173866975, 4276766702, 1486788991, 4231637181, 3526754164, 1993741119, 962497907, 1123352536, 3857709913, 828733647, 2927685951, 2387140051, 920105863, 2902152809, 1844789078, 87729918, 2539458255, 2154314047, 2423733775, 2257026603, 4015813662, 2075249514, 630969053, 1258481405, 1918461941, 3037163190, 3674475471, 2707608548] : Array ℕ)[j.val]!

def columnsInverse : Fin 32 → ℕ := fun j => (#[990635610, 1262365730, 4119392256, 743413282, 2424872070, 907305088, 589576992, 3949792248, 2108185996, 3040408037, 3114019145, 4267882813, 2985110136, 479512736, 1933957211, 3906522934, 808307721, 2962040138, 3054617345, 2799658818, 290889180, 2509633403, 1511934892, 1894557605, 2923888892, 1895437880, 941257143, 3294285834, 1455991290, 4041024997, 2782832707, 1219071392] : Array ℕ)[j.val]!

def columnsParent : Fin 31 → Fin 32 := fun j => (#[0, 1, 2, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 25] : Array (Fin 32))[j.val]!

def columnsGenerator : Fin 31 → Fin 2 := fun j => (#[0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1] : Array (Fin 2))[j.val]!

private theorem columns_earlier : ∀ i, columnsParent i < i.succ := by decide +kernel

private theorem columns_step : ∀ i, act (generators (columnsGenerator i)) (columns (columnsParent i)) = columns i.succ := by decide +kernel

private theorem columns_inverse : product columns columnsInverse = identity 32 := by decide +kernel

theorem columns_top (U : Submodule (ZMod 2) (Fin 32 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s))) (hseed : vector 498319103 ∈ U) : U = ⊤ := by
  exact eq_top_of_column_orbit U generators hA columns columnsInverse
    columnsParent columnsGenerator columns_earlier columns_step columns_inverse hseed

def otherColumns : Fin 32 → ℕ := fun j => (#[1559492319, 1677583999, 4252853239, 1341815547, 1026351063, 3131721711, 3726556539, 4229540031, 3525697398, 4276034351, 970886455, 1660206553, 2246572893, 971864463, 3213031742, 2383011275, 920072599, 2898990699, 1641365342, 356160766, 392105933, 2188261821, 2440543790, 109533803, 4011602975, 1536281390, 631231165, 1258734845, 1917921277, 3070719666, 1526995950, 3790786996] : Array ℕ)[j.val]!

def otherColumnsInverse : Fin 32 → ℕ := fun j => (#[1688555008, 1546305563, 634424080, 460545409, 389077121, 3084958410, 1899648641, 3050316720, 3036581824, 49057993, 2730197275, 3495034322, 238046044, 1957305959, 208528165, 3635800605, 2704232585, 1331169291, 1643869418, 4274755487, 1853662754, 2189499330, 2073614472, 4071273748, 1076910023, 290212067, 1496066860, 2235608459, 922189621, 1737482221, 3133196678, 1764662932] : Array ℕ)[j.val]!

def otherColumnsParent : Fin 31 → Fin 32 := fun j => (#[0, 1, 2, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 25] : Array (Fin 32))[j.val]!

def otherColumnsGenerator : Fin 31 → Fin 2 := fun j => (#[0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1] : Array (Fin 2))[j.val]!

private theorem otherColumns_earlier : ∀ i, otherColumnsParent i < i.succ := by decide +kernel

private theorem otherColumns_step : ∀ i, act (generators (otherColumnsGenerator i)) (otherColumns (otherColumnsParent i)) = otherColumns i.succ := by decide +kernel

private theorem otherColumns_inverse : product otherColumns otherColumnsInverse = identity 32 := by decide +kernel

theorem otherColumns_top (U : Submodule (ZMod 2) (Fin 32 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s))) (hseed : vector 1559492319 ∈ U) : U = ⊤ := by
  exact eq_top_of_column_orbit U generators hA otherColumns otherColumnsInverse
    otherColumnsParent otherColumnsGenerator otherColumns_earlier otherColumns_step otherColumns_inverse hseed

def rows : Fin 32 → ℕ := fun j => (#[1, 2, 16, 64, 4, 2097152, 8, 1073741824, 16384, 4096, 2402744635, 1048576, 512, 262144, 256, 3849590323, 1854854849, 2447337508, 8192, 1443205168, 2048, 32, 1257881842, 1443992950, 3343757625, 2438818887, 1908985876, 1572690379, 1854803672, 531950075, 2147483648, 128] : Array ℕ)[j.val]!

def rowsInverse : Fin 32 → ℕ := fun j => (#[1, 2, 16, 64, 4, 2097152, 8, 2147483648, 16384, 4096, 8939546, 1048576, 512, 262144, 256, 269550405, 59769152, 2116000381, 8192, 2825809881, 2048, 32, 906385980, 2092298860, 1036917693, 2479583064, 1657283008, 3807880058, 3802820121, 698921724, 128, 1073741824] : Array ℕ)[j.val]!

def rowsParent : Fin 31 → Fin 32 := fun j => (#[0, 0, 2, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 12, 13, 14, 14, 15, 16, 16, 17, 17, 18, 19, 19, 20, 21] : Array (Fin 32))[j.val]!

def rowsGenerator : Fin 31 → Fin 2 := fun j => (#[0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] : Array (Fin 2))[j.val]!

private theorem rows_earlier : ∀ i, rowsParent i < i.succ := by decide +kernel

private theorem rows_step : ∀ i, act (transposes (rowsGenerator i)) (rows (rowsParent i)) = rows i.succ := by decide +kernel

private theorem rows_inverse : product rows rowsInverse = identity 32 := by decide +kernel

theorem simple_of_detects (U : Submodule (ZMod 2) (Fin 32 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s)))
    (hbase : ∀ x ∈ U, vector 1 ⬝ᵥ x ≠ 0 → U = ⊤) : U = ⊥ ∨ U = ⊤ := by
  exact simple_of_row_orbit U generators transposes hA transposes_eq rows rowsInverse
    rowsParent rowsGenerator rows_earlier rows_step rows_inverse hbase

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree32
