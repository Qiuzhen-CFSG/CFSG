module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates

/-!
# Native words for the linear-five subgroup

The four octad lifts are words in the literal ATLAS max1 generators. The lists
obtained by the GAP discovery are reversed, without inversion of their letters,
to use Lean's multiplication convention. The shared products below only
reassociate those lists. Corrections are in the existing eleven-bit kernel.

The subgroup `F` is the actual closure of these ten native generators.
Source: Kleidman--Wilson (1988), pp.485,490, and ATLAS J4G1-max1W1.
The defining words are discovery data; their properties require the checked
matrix evaluations and quotient markings in the following modules.
-/

set_option maxRecDepth 10000
@[expose] public section
namespace Janko4.LocalStructure.LinearFive
open Janko4 Cardinality KernelCount Simplicity.Max1Fusion.KernelOrbits

namespace NativeWords
variable {G : Type*} [Group G] (x y : G)
def d3 : G := x * y
def d4 : G := x * y⁻¹
def d5 : G := x⁻¹ * y
def d6 : G := x⁻¹ * y⁻¹
def d7 : G := (d4 x y) * (d3 x y)
def d8 : G := (d5 x y) * (d5 x y)
def d9 : G := (d6 x y) * (d6 x y)
def d10 : G := (d4 x y) * (d7 x y)
def d11 : G := (d3 x y) * (d3 x y)
def d12 : G := (d4 x y) * (d10 x y)
def d13 : G := (d5 x y) * (d6 x y)
def d14 : G := (d3 x y) * (d7 x y)
def d15 : G := (d5 x y) * (d9 x y)
def d16 : G := (d7 x y) * (d11 x y)
def d17 : G := (d13 x y) * (d8 x y)
def d18 : G := (d10 x y) * (d14 x y)
def d19 : G := (d4 x y) * (d12 x y)
def d20 : G := (d6 x y) * (d8 x y)
def d21 : G := (d3 x y) * (d12 x y)
def d22 : G := (d7 x y) * (d14 x y)
def d23 : G := (d8 x y) * (d8 x y)
def d24 : G := (d4 x y) * (d19 x y)
def d25 : G := (d4 x y) * y⁻¹
def d26 : G := (d13 x y) * y⁻¹
def d27 : G := (d11 x y) * (d16 x y)
def d28 : G := (d9 x y) * (d8 x y)
def d29 : G := (d7 x y) * (d10 x y)
def d30 : G := (d4 x y) * x
def d31 : G := (d11 x y) * (d21 x y)
def d32 : G := (d12 x y) * (d27 x y)
def d33 : G := (d32 x y) * (d3 x y)
def d34 : G := (d33 x y) * (d13 x y)
def d35 : G := (d34 x y) * (d26 x y)
def d36 : G := (d35 x y) * (d21 x y)
def d37 : G := (d36 x y) * (d11 x y)
def d38 : G := (d8 x y) * y
def d39 : G := (d7 x y) * (d12 x y)
def d40 : G := (d3 x y) * x
def d41 : G := (d22 x y) * (d11 x y)
def d42 : G := (d17 x y) * (d15 x y)
def d43 : G := (d9 x y) * (d6 x y)
def d44 : G := (d18 x y) * (d10 x y)
def d45 : G := (d16 x y) * (d14 x y)
def p0_0 : G := (d23 x y) * (d6 x y)
def p0_1 : G := (p0_0 x y) * (d13 x y)
def p0_2 : G := (p0_1 x y) * (d15 x y)
def p0_3 : G := (p0_2 x y) * (d13 x y)
def p0_4 : G := (p0_3 x y) * (d12 x y)
def p0_5 : G := (p0_4 x y) * (d29 x y)
def p0_6 : G := (p0_5 x y) * (d18 x y)
def p0_7 : G := (p0_6 x y) * (d3 x y)
def p0_8 : G := (p0_7 x y) * (d10 x y)
def p0_9 : G := (p0_8 x y) * (d11 x y)
def p0_10 : G := (p0_9 x y) * (d7 x y)
def p0_11 : G := (p0_10 x y) * (d19 x y)
def p0_12 : G := (p0_11 x y) * (d19 x y)
def p0_13 : G := (p0_12 x y) * (d30 x y)
def p0_14 : G := (p0_13 x y) * (d16 x y)
def p0_15 : G := (p0_14 x y) * (d31 x y)
def p0_16 : G := (p0_15 x y) * (d24 x y)
def p0_17 : G := (p0_16 x y) * (d25 x y)
def p0_18 : G := (p0_17 x y) * (d17 x y)
def p0_19 : G := (p0_18 x y) * (d26 x y)
def p0_20 : G := (p0_19 x y) * (d27 x y)
def p0_21 : G := (p0_20 x y) * (d10 x y)
def p0_22 : G := (p0_21 x y) * (d37 x y)
def p1_0 : G := (d23 x y) * (d38 x y)
def p1_1 : G := (p1_0 x y) * (d7 x y)
def p1_2 : G := (p1_1 x y) * (d39 x y)
def p1_3 : G := (p1_2 x y) * (d40 x y)
def p1_4 : G := (p1_3 x y) * (d7 x y)
def p1_5 : G := (p1_4 x y) * (d41 x y)
def p1_6 : G := (p1_5 x y) * x
def p1_7 : G := (p1_6 x y) * (d4 x y)
def p1_8 : G := (p1_7 x y) * (d24 x y)
def p1_9 : G := (p1_8 x y) * y
def p1_10 : G := (p1_9 x y) * (d15 x y)
def p1_11 : G := (p1_10 x y) * (d28 x y)
def p1_12 : G := (p1_11 x y) * (d9 x y)
def p1_13 : G := (p1_12 x y) * (d15 x y)
def p1_14 : G := (p1_13 x y) * (d5 x y)
def p1_15 : G := (p1_14 x y) * (d14 x y)
def p1_16 : G := (p1_15 x y) * (d25 x y)
def p1_17 : G := (p1_16 x y) * (d20 x y)
def p1_18 : G := (p1_17 x y) * (d6 x y)
def p1_19 : G := (p1_18 x y) * (d5 x y)
def p1_20 : G := (p1_19 x y) * (d31 x y)
def p1_21 : G := (p1_20 x y) * (d3 x y)
def p1_22 : G := (p1_21 x y) * (d25 x y)
def p1_23 : G := (p1_22 x y) * (d9 x y)
def p1_24 : G := (p1_23 x y) * (d42 x y)
def p1_25 : G := (p1_24 x y) * (d20 x y)
def p1_26 : G := (p1_25 x y) * (d13 x y)
def p1_27 : G := (p1_26 x y) * (d5 x y)
def p1_28 : G := (p1_27 x y) * y
def p1_29 : G := (p1_28 x y) * (d7 x y)
def p1_30 : G := (p1_29 x y) * (d4 x y)
def p1_31 : G := (p1_30 x y) * (d4 x y)
def p1_32 : G := (p1_31 x y) * (d43 x y)
def p1_33 : G := (p1_32 x y) * (d15 x y)
def p1_34 : G := (p1_33 x y) * (d20 x y)
def p1_35 : G := (p1_34 x y) * (d17 x y)
def p2_0 : G := (d8 x y) * (d6 x y)
def p2_1 : G := (p2_0 x y) * (d42 x y)
def p2_2 : G := (p2_1 x y) * (d8 x y)
def p2_3 : G := (p2_2 x y) * (d7 x y)
def p2_4 : G := (p2_3 x y) * (d44 x y)
def p2_5 : G := (p2_4 x y) * (d3 x y)
def p2_6 : G := (p2_5 x y) * (d30 x y)
def p2_7 : G := (p2_6 x y) * (d22 x y)
def p2_8 : G := (p2_7 x y) * (d45 x y)
def p2_9 : G := (p2_8 x y) * (d7 x y)
def p2_10 : G := (p2_9 x y) * (d24 x y)
def p2_11 : G := (p2_10 x y) * (d9 x y)
def p2_12 : G := (p2_11 x y) * (d9 x y)
def p2_13 : G := (p2_12 x y) * (d9 x y)
def p2_14 : G := (p2_13 x y) * y⁻¹
def p2_15 : G := (p2_14 x y) * (d17 x y)
def p2_16 : G := (p2_15 x y) * (d20 x y)
def p2_17 : G := (p2_16 x y) * (d38 x y)
def p2_18 : G := (p2_17 x y) * (d12 x y)
def p2_19 : G := (p2_18 x y) * (d9 x y)
def p2_20 : G := (p2_19 x y) * (d28 x y)
def p2_21 : G := (p2_20 x y) * (d6 x y)
def p2_22 : G := (p2_21 x y) * (d15 x y)
def p2_23 : G := (p2_22 x y) * (d43 x y)
def p3_0 : G := y⁻¹ * (d11 x y)
def p3_1 : G := (p3_0 x y) * (d18 x y)
def p3_2 : G := (p3_1 x y) * (d6 x y)
def p3_3 : G := (p3_2 x y) * (d11 x y)
def p3_4 : G := (p3_3 x y) * (d11 x y)
def p3_5 : G := (p3_4 x y) * (d10 x y)
def p3_6 : G := (p3_5 x y) * (d18 x y)
def p3_7 : G := (p3_6 x y) * (d44 x y)
def p3_8 : G := (p3_7 x y) * (d40 x y)
def p3_9 : G := (p3_8 x y) * (d45 x y)
def p3_10 : G := (p3_9 x y) * (d39 x y)
def p3_11 : G := (p3_10 x y) * (d41 x y)
def p3_12 : G := (p3_11 x y) * (d4 x y)
def p3_13 : G := (p3_12 x y) * (d15 x y)
def p3_14 : G := (p3_13 x y) * (d8 x y)
def p3_15 : G := (p3_14 x y) * (d9 x y)
def p3_16 : G := (p3_15 x y) * (d20 x y)
def p3_17 : G := (p3_16 x y) * (d28 x y)
def p3_18 : G := (p3_17 x y) * (d17 x y)
def p3_19 : G := (p3_18 x y) * (d22 x y)
def p3_20 : G := (p3_19 x y) * (d29 x y)
def p3_21 : G := (p3_20 x y) * (d37 x y)
def lifts : Fin 4 → G := ![p0_22 x y, p1_35 x y, p2_23 x y, p3_21 x y]

private theorem map_d3 {H : Type*} [Group H] (f : G →* H) :
    f (d3 x y) = d3 (f x) (f y) := by
  simp only [d3, map_mul]
private theorem map_d4 {H : Type*} [Group H] (f : G →* H) :
    f (d4 x y) = d4 (f x) (f y) := by
  simp only [d4, map_mul, map_inv]
private theorem map_d5 {H : Type*} [Group H] (f : G →* H) :
    f (d5 x y) = d5 (f x) (f y) := by
  simp only [d5, map_mul, map_inv]
private theorem map_d6 {H : Type*} [Group H] (f : G →* H) :
    f (d6 x y) = d6 (f x) (f y) := by
  simp only [d6, map_mul, map_inv]
private theorem map_d7 {H : Type*} [Group H] (f : G →* H) :
    f (d7 x y) = d7 (f x) (f y) := by
  simp only [d7, map_mul, map_d4, map_d3]
private theorem map_d8 {H : Type*} [Group H] (f : G →* H) :
    f (d8 x y) = d8 (f x) (f y) := by
  simp only [d8, map_mul, map_d5]
private theorem map_d9 {H : Type*} [Group H] (f : G →* H) :
    f (d9 x y) = d9 (f x) (f y) := by
  simp only [d9, map_mul, map_d6]
private theorem map_d10 {H : Type*} [Group H] (f : G →* H) :
    f (d10 x y) = d10 (f x) (f y) := by
  simp only [d10, map_mul, map_d4, map_d7]
private theorem map_d11 {H : Type*} [Group H] (f : G →* H) :
    f (d11 x y) = d11 (f x) (f y) := by
  simp only [d11, map_mul, map_d3]
private theorem map_d12 {H : Type*} [Group H] (f : G →* H) :
    f (d12 x y) = d12 (f x) (f y) := by
  simp only [d12, map_mul, map_d4, map_d10]
private theorem map_d13 {H : Type*} [Group H] (f : G →* H) :
    f (d13 x y) = d13 (f x) (f y) := by
  simp only [d13, map_mul, map_d5, map_d6]
private theorem map_d14 {H : Type*} [Group H] (f : G →* H) :
    f (d14 x y) = d14 (f x) (f y) := by
  simp only [d14, map_mul, map_d3, map_d7]
private theorem map_d15 {H : Type*} [Group H] (f : G →* H) :
    f (d15 x y) = d15 (f x) (f y) := by
  simp only [d15, map_mul, map_d5, map_d9]
private theorem map_d16 {H : Type*} [Group H] (f : G →* H) :
    f (d16 x y) = d16 (f x) (f y) := by
  simp only [d16, map_mul, map_d7, map_d11]
private theorem map_d17 {H : Type*} [Group H] (f : G →* H) :
    f (d17 x y) = d17 (f x) (f y) := by
  simp only [d17, map_mul, map_d13, map_d8]
private theorem map_d18 {H : Type*} [Group H] (f : G →* H) :
    f (d18 x y) = d18 (f x) (f y) := by
  simp only [d18, map_mul, map_d10, map_d14]
private theorem map_d19 {H : Type*} [Group H] (f : G →* H) :
    f (d19 x y) = d19 (f x) (f y) := by
  simp only [d19, map_mul, map_d4, map_d12]
private theorem map_d20 {H : Type*} [Group H] (f : G →* H) :
    f (d20 x y) = d20 (f x) (f y) := by
  simp only [d20, map_mul, map_d6, map_d8]
private theorem map_d21 {H : Type*} [Group H] (f : G →* H) :
    f (d21 x y) = d21 (f x) (f y) := by
  simp only [d21, map_mul, map_d3, map_d12]
private theorem map_d22 {H : Type*} [Group H] (f : G →* H) :
    f (d22 x y) = d22 (f x) (f y) := by
  simp only [d22, map_mul, map_d7, map_d14]
private theorem map_d23 {H : Type*} [Group H] (f : G →* H) :
    f (d23 x y) = d23 (f x) (f y) := by
  simp only [d23, map_mul, map_d8]
private theorem map_d24 {H : Type*} [Group H] (f : G →* H) :
    f (d24 x y) = d24 (f x) (f y) := by
  simp only [d24, map_mul, map_d4, map_d19]
private theorem map_d25 {H : Type*} [Group H] (f : G →* H) :
    f (d25 x y) = d25 (f x) (f y) := by
  simp only [d25, map_mul, map_inv, map_d4]
private theorem map_d26 {H : Type*} [Group H] (f : G →* H) :
    f (d26 x y) = d26 (f x) (f y) := by
  simp only [d26, map_mul, map_inv, map_d13]
private theorem map_d27 {H : Type*} [Group H] (f : G →* H) :
    f (d27 x y) = d27 (f x) (f y) := by
  simp only [d27, map_mul, map_d11, map_d16]
private theorem map_d28 {H : Type*} [Group H] (f : G →* H) :
    f (d28 x y) = d28 (f x) (f y) := by
  simp only [d28, map_mul, map_d9, map_d8]
private theorem map_d29 {H : Type*} [Group H] (f : G →* H) :
    f (d29 x y) = d29 (f x) (f y) := by
  simp only [d29, map_mul, map_d7, map_d10]
private theorem map_d30 {H : Type*} [Group H] (f : G →* H) :
    f (d30 x y) = d30 (f x) (f y) := by
  simp only [d30, map_mul, map_d4]
private theorem map_d31 {H : Type*} [Group H] (f : G →* H) :
    f (d31 x y) = d31 (f x) (f y) := by
  simp only [d31, map_mul, map_d11, map_d21]
private theorem map_d32 {H : Type*} [Group H] (f : G →* H) :
    f (d32 x y) = d32 (f x) (f y) := by
  simp only [d32, map_mul, map_d12, map_d27]
private theorem map_d33 {H : Type*} [Group H] (f : G →* H) :
    f (d33 x y) = d33 (f x) (f y) := by
  simp only [d33, map_mul, map_d32, map_d3]
private theorem map_d34 {H : Type*} [Group H] (f : G →* H) :
    f (d34 x y) = d34 (f x) (f y) := by
  simp only [d34, map_mul, map_d33, map_d13]
private theorem map_d35 {H : Type*} [Group H] (f : G →* H) :
    f (d35 x y) = d35 (f x) (f y) := by
  simp only [d35, map_mul, map_d34, map_d26]
private theorem map_d36 {H : Type*} [Group H] (f : G →* H) :
    f (d36 x y) = d36 (f x) (f y) := by
  simp only [d36, map_mul, map_d35, map_d21]
private theorem map_d37 {H : Type*} [Group H] (f : G →* H) :
    f (d37 x y) = d37 (f x) (f y) := by
  simp only [d37, map_mul, map_d36, map_d11]
private theorem map_d38 {H : Type*} [Group H] (f : G →* H) :
    f (d38 x y) = d38 (f x) (f y) := by
  simp only [d38, map_mul, map_d8]
private theorem map_d39 {H : Type*} [Group H] (f : G →* H) :
    f (d39 x y) = d39 (f x) (f y) := by
  simp only [d39, map_mul, map_d7, map_d12]
private theorem map_d40 {H : Type*} [Group H] (f : G →* H) :
    f (d40 x y) = d40 (f x) (f y) := by
  simp only [d40, map_mul, map_d3]
private theorem map_d41 {H : Type*} [Group H] (f : G →* H) :
    f (d41 x y) = d41 (f x) (f y) := by
  simp only [d41, map_mul, map_d22, map_d11]
private theorem map_d42 {H : Type*} [Group H] (f : G →* H) :
    f (d42 x y) = d42 (f x) (f y) := by
  simp only [d42, map_mul, map_d17, map_d15]
private theorem map_d43 {H : Type*} [Group H] (f : G →* H) :
    f (d43 x y) = d43 (f x) (f y) := by
  simp only [d43, map_mul, map_d9, map_d6]
private theorem map_d44 {H : Type*} [Group H] (f : G →* H) :
    f (d44 x y) = d44 (f x) (f y) := by
  simp only [d44, map_mul, map_d18, map_d10]
private theorem map_d45 {H : Type*} [Group H] (f : G →* H) :
    f (d45 x y) = d45 (f x) (f y) := by
  simp only [d45, map_mul, map_d16, map_d14]
private theorem map_p0_0 {H : Type*} [Group H] (f : G →* H) :
    f (p0_0 x y) = p0_0 (f x) (f y) := by
  simp only [p0_0, map_mul, map_d23, map_d6]
private theorem map_p0_1 {H : Type*} [Group H] (f : G →* H) :
    f (p0_1 x y) = p0_1 (f x) (f y) := by
  simp only [p0_1, map_mul, map_p0_0, map_d13]
private theorem map_p0_2 {H : Type*} [Group H] (f : G →* H) :
    f (p0_2 x y) = p0_2 (f x) (f y) := by
  simp only [p0_2, map_mul, map_p0_1, map_d15]
private theorem map_p0_3 {H : Type*} [Group H] (f : G →* H) :
    f (p0_3 x y) = p0_3 (f x) (f y) := by
  simp only [p0_3, map_mul, map_p0_2, map_d13]
private theorem map_p0_4 {H : Type*} [Group H] (f : G →* H) :
    f (p0_4 x y) = p0_4 (f x) (f y) := by
  simp only [p0_4, map_mul, map_p0_3, map_d12]
private theorem map_p0_5 {H : Type*} [Group H] (f : G →* H) :
    f (p0_5 x y) = p0_5 (f x) (f y) := by
  simp only [p0_5, map_mul, map_p0_4, map_d29]
private theorem map_p0_6 {H : Type*} [Group H] (f : G →* H) :
    f (p0_6 x y) = p0_6 (f x) (f y) := by
  simp only [p0_6, map_mul, map_p0_5, map_d18]
private theorem map_p0_7 {H : Type*} [Group H] (f : G →* H) :
    f (p0_7 x y) = p0_7 (f x) (f y) := by
  simp only [p0_7, map_mul, map_p0_6, map_d3]
private theorem map_p0_8 {H : Type*} [Group H] (f : G →* H) :
    f (p0_8 x y) = p0_8 (f x) (f y) := by
  simp only [p0_8, map_mul, map_p0_7, map_d10]
private theorem map_p0_9 {H : Type*} [Group H] (f : G →* H) :
    f (p0_9 x y) = p0_9 (f x) (f y) := by
  simp only [p0_9, map_mul, map_p0_8, map_d11]
private theorem map_p0_10 {H : Type*} [Group H] (f : G →* H) :
    f (p0_10 x y) = p0_10 (f x) (f y) := by
  simp only [p0_10, map_mul, map_p0_9, map_d7]
private theorem map_p0_11 {H : Type*} [Group H] (f : G →* H) :
    f (p0_11 x y) = p0_11 (f x) (f y) := by
  simp only [p0_11, map_mul, map_p0_10, map_d19]
private theorem map_p0_12 {H : Type*} [Group H] (f : G →* H) :
    f (p0_12 x y) = p0_12 (f x) (f y) := by
  simp only [p0_12, map_mul, map_p0_11, map_d19]
private theorem map_p0_13 {H : Type*} [Group H] (f : G →* H) :
    f (p0_13 x y) = p0_13 (f x) (f y) := by
  simp only [p0_13, map_mul, map_p0_12, map_d30]
private theorem map_p0_14 {H : Type*} [Group H] (f : G →* H) :
    f (p0_14 x y) = p0_14 (f x) (f y) := by
  simp only [p0_14, map_mul, map_p0_13, map_d16]
private theorem map_p0_15 {H : Type*} [Group H] (f : G →* H) :
    f (p0_15 x y) = p0_15 (f x) (f y) := by
  simp only [p0_15, map_mul, map_p0_14, map_d31]
private theorem map_p0_16 {H : Type*} [Group H] (f : G →* H) :
    f (p0_16 x y) = p0_16 (f x) (f y) := by
  simp only [p0_16, map_mul, map_p0_15, map_d24]
private theorem map_p0_17 {H : Type*} [Group H] (f : G →* H) :
    f (p0_17 x y) = p0_17 (f x) (f y) := by
  simp only [p0_17, map_mul, map_p0_16, map_d25]
private theorem map_p0_18 {H : Type*} [Group H] (f : G →* H) :
    f (p0_18 x y) = p0_18 (f x) (f y) := by
  simp only [p0_18, map_mul, map_p0_17, map_d17]
private theorem map_p0_19 {H : Type*} [Group H] (f : G →* H) :
    f (p0_19 x y) = p0_19 (f x) (f y) := by
  simp only [p0_19, map_mul, map_p0_18, map_d26]
private theorem map_p0_20 {H : Type*} [Group H] (f : G →* H) :
    f (p0_20 x y) = p0_20 (f x) (f y) := by
  simp only [p0_20, map_mul, map_p0_19, map_d27]
private theorem map_p0_21 {H : Type*} [Group H] (f : G →* H) :
    f (p0_21 x y) = p0_21 (f x) (f y) := by
  simp only [p0_21, map_mul, map_p0_20, map_d10]
private theorem map_p0_22 {H : Type*} [Group H] (f : G →* H) :
    f (p0_22 x y) = p0_22 (f x) (f y) := by
  simp only [p0_22, map_mul, map_p0_21, map_d37]
private theorem map_p1_0 {H : Type*} [Group H] (f : G →* H) :
    f (p1_0 x y) = p1_0 (f x) (f y) := by
  simp only [p1_0, map_mul, map_d23, map_d38]
private theorem map_p1_1 {H : Type*} [Group H] (f : G →* H) :
    f (p1_1 x y) = p1_1 (f x) (f y) := by
  simp only [p1_1, map_mul, map_p1_0, map_d7]
private theorem map_p1_2 {H : Type*} [Group H] (f : G →* H) :
    f (p1_2 x y) = p1_2 (f x) (f y) := by
  simp only [p1_2, map_mul, map_p1_1, map_d39]
private theorem map_p1_3 {H : Type*} [Group H] (f : G →* H) :
    f (p1_3 x y) = p1_3 (f x) (f y) := by
  simp only [p1_3, map_mul, map_p1_2, map_d40]
private theorem map_p1_4 {H : Type*} [Group H] (f : G →* H) :
    f (p1_4 x y) = p1_4 (f x) (f y) := by
  simp only [p1_4, map_mul, map_p1_3, map_d7]
private theorem map_p1_5 {H : Type*} [Group H] (f : G →* H) :
    f (p1_5 x y) = p1_5 (f x) (f y) := by
  simp only [p1_5, map_mul, map_p1_4, map_d41]
private theorem map_p1_6 {H : Type*} [Group H] (f : G →* H) :
    f (p1_6 x y) = p1_6 (f x) (f y) := by
  simp only [p1_6, map_mul, map_p1_5]
private theorem map_p1_7 {H : Type*} [Group H] (f : G →* H) :
    f (p1_7 x y) = p1_7 (f x) (f y) := by
  simp only [p1_7, map_mul, map_p1_6, map_d4]
private theorem map_p1_8 {H : Type*} [Group H] (f : G →* H) :
    f (p1_8 x y) = p1_8 (f x) (f y) := by
  simp only [p1_8, map_mul, map_p1_7, map_d24]
private theorem map_p1_9 {H : Type*} [Group H] (f : G →* H) :
    f (p1_9 x y) = p1_9 (f x) (f y) := by
  simp only [p1_9, map_mul, map_p1_8]
private theorem map_p1_10 {H : Type*} [Group H] (f : G →* H) :
    f (p1_10 x y) = p1_10 (f x) (f y) := by
  simp only [p1_10, map_mul, map_p1_9, map_d15]
private theorem map_p1_11 {H : Type*} [Group H] (f : G →* H) :
    f (p1_11 x y) = p1_11 (f x) (f y) := by
  simp only [p1_11, map_mul, map_p1_10, map_d28]
private theorem map_p1_12 {H : Type*} [Group H] (f : G →* H) :
    f (p1_12 x y) = p1_12 (f x) (f y) := by
  simp only [p1_12, map_mul, map_p1_11, map_d9]
private theorem map_p1_13 {H : Type*} [Group H] (f : G →* H) :
    f (p1_13 x y) = p1_13 (f x) (f y) := by
  simp only [p1_13, map_mul, map_p1_12, map_d15]
private theorem map_p1_14 {H : Type*} [Group H] (f : G →* H) :
    f (p1_14 x y) = p1_14 (f x) (f y) := by
  simp only [p1_14, map_mul, map_p1_13, map_d5]
private theorem map_p1_15 {H : Type*} [Group H] (f : G →* H) :
    f (p1_15 x y) = p1_15 (f x) (f y) := by
  simp only [p1_15, map_mul, map_p1_14, map_d14]
private theorem map_p1_16 {H : Type*} [Group H] (f : G →* H) :
    f (p1_16 x y) = p1_16 (f x) (f y) := by
  simp only [p1_16, map_mul, map_p1_15, map_d25]
private theorem map_p1_17 {H : Type*} [Group H] (f : G →* H) :
    f (p1_17 x y) = p1_17 (f x) (f y) := by
  simp only [p1_17, map_mul, map_p1_16, map_d20]
private theorem map_p1_18 {H : Type*} [Group H] (f : G →* H) :
    f (p1_18 x y) = p1_18 (f x) (f y) := by
  simp only [p1_18, map_mul, map_p1_17, map_d6]
private theorem map_p1_19 {H : Type*} [Group H] (f : G →* H) :
    f (p1_19 x y) = p1_19 (f x) (f y) := by
  simp only [p1_19, map_mul, map_p1_18, map_d5]
private theorem map_p1_20 {H : Type*} [Group H] (f : G →* H) :
    f (p1_20 x y) = p1_20 (f x) (f y) := by
  simp only [p1_20, map_mul, map_p1_19, map_d31]
private theorem map_p1_21 {H : Type*} [Group H] (f : G →* H) :
    f (p1_21 x y) = p1_21 (f x) (f y) := by
  simp only [p1_21, map_mul, map_p1_20, map_d3]
private theorem map_p1_22 {H : Type*} [Group H] (f : G →* H) :
    f (p1_22 x y) = p1_22 (f x) (f y) := by
  simp only [p1_22, map_mul, map_p1_21, map_d25]
private theorem map_p1_23 {H : Type*} [Group H] (f : G →* H) :
    f (p1_23 x y) = p1_23 (f x) (f y) := by
  simp only [p1_23, map_mul, map_p1_22, map_d9]
private theorem map_p1_24 {H : Type*} [Group H] (f : G →* H) :
    f (p1_24 x y) = p1_24 (f x) (f y) := by
  simp only [p1_24, map_mul, map_p1_23, map_d42]
private theorem map_p1_25 {H : Type*} [Group H] (f : G →* H) :
    f (p1_25 x y) = p1_25 (f x) (f y) := by
  simp only [p1_25, map_mul, map_p1_24, map_d20]
private theorem map_p1_26 {H : Type*} [Group H] (f : G →* H) :
    f (p1_26 x y) = p1_26 (f x) (f y) := by
  simp only [p1_26, map_mul, map_p1_25, map_d13]
private theorem map_p1_27 {H : Type*} [Group H] (f : G →* H) :
    f (p1_27 x y) = p1_27 (f x) (f y) := by
  simp only [p1_27, map_mul, map_p1_26, map_d5]
private theorem map_p1_28 {H : Type*} [Group H] (f : G →* H) :
    f (p1_28 x y) = p1_28 (f x) (f y) := by
  simp only [p1_28, map_mul, map_p1_27]
private theorem map_p1_29 {H : Type*} [Group H] (f : G →* H) :
    f (p1_29 x y) = p1_29 (f x) (f y) := by
  simp only [p1_29, map_mul, map_p1_28, map_d7]
private theorem map_p1_30 {H : Type*} [Group H] (f : G →* H) :
    f (p1_30 x y) = p1_30 (f x) (f y) := by
  simp only [p1_30, map_mul, map_p1_29, map_d4]
private theorem map_p1_31 {H : Type*} [Group H] (f : G →* H) :
    f (p1_31 x y) = p1_31 (f x) (f y) := by
  simp only [p1_31, map_mul, map_p1_30, map_d4]
private theorem map_p1_32 {H : Type*} [Group H] (f : G →* H) :
    f (p1_32 x y) = p1_32 (f x) (f y) := by
  simp only [p1_32, map_mul, map_p1_31, map_d43]
private theorem map_p1_33 {H : Type*} [Group H] (f : G →* H) :
    f (p1_33 x y) = p1_33 (f x) (f y) := by
  simp only [p1_33, map_mul, map_p1_32, map_d15]
private theorem map_p1_34 {H : Type*} [Group H] (f : G →* H) :
    f (p1_34 x y) = p1_34 (f x) (f y) := by
  simp only [p1_34, map_mul, map_p1_33, map_d20]
private theorem map_p1_35 {H : Type*} [Group H] (f : G →* H) :
    f (p1_35 x y) = p1_35 (f x) (f y) := by
  simp only [p1_35, map_mul, map_p1_34, map_d17]
private theorem map_p2_0 {H : Type*} [Group H] (f : G →* H) :
    f (p2_0 x y) = p2_0 (f x) (f y) := by
  simp only [p2_0, map_mul, map_d8, map_d6]
private theorem map_p2_1 {H : Type*} [Group H] (f : G →* H) :
    f (p2_1 x y) = p2_1 (f x) (f y) := by
  simp only [p2_1, map_mul, map_p2_0, map_d42]
private theorem map_p2_2 {H : Type*} [Group H] (f : G →* H) :
    f (p2_2 x y) = p2_2 (f x) (f y) := by
  simp only [p2_2, map_mul, map_p2_1, map_d8]
private theorem map_p2_3 {H : Type*} [Group H] (f : G →* H) :
    f (p2_3 x y) = p2_3 (f x) (f y) := by
  simp only [p2_3, map_mul, map_p2_2, map_d7]
private theorem map_p2_4 {H : Type*} [Group H] (f : G →* H) :
    f (p2_4 x y) = p2_4 (f x) (f y) := by
  simp only [p2_4, map_mul, map_p2_3, map_d44]
private theorem map_p2_5 {H : Type*} [Group H] (f : G →* H) :
    f (p2_5 x y) = p2_5 (f x) (f y) := by
  simp only [p2_5, map_mul, map_p2_4, map_d3]
private theorem map_p2_6 {H : Type*} [Group H] (f : G →* H) :
    f (p2_6 x y) = p2_6 (f x) (f y) := by
  simp only [p2_6, map_mul, map_p2_5, map_d30]
private theorem map_p2_7 {H : Type*} [Group H] (f : G →* H) :
    f (p2_7 x y) = p2_7 (f x) (f y) := by
  simp only [p2_7, map_mul, map_p2_6, map_d22]
private theorem map_p2_8 {H : Type*} [Group H] (f : G →* H) :
    f (p2_8 x y) = p2_8 (f x) (f y) := by
  simp only [p2_8, map_mul, map_p2_7, map_d45]
private theorem map_p2_9 {H : Type*} [Group H] (f : G →* H) :
    f (p2_9 x y) = p2_9 (f x) (f y) := by
  simp only [p2_9, map_mul, map_p2_8, map_d7]
private theorem map_p2_10 {H : Type*} [Group H] (f : G →* H) :
    f (p2_10 x y) = p2_10 (f x) (f y) := by
  simp only [p2_10, map_mul, map_p2_9, map_d24]
private theorem map_p2_11 {H : Type*} [Group H] (f : G →* H) :
    f (p2_11 x y) = p2_11 (f x) (f y) := by
  simp only [p2_11, map_mul, map_p2_10, map_d9]
private theorem map_p2_12 {H : Type*} [Group H] (f : G →* H) :
    f (p2_12 x y) = p2_12 (f x) (f y) := by
  simp only [p2_12, map_mul, map_p2_11, map_d9]
private theorem map_p2_13 {H : Type*} [Group H] (f : G →* H) :
    f (p2_13 x y) = p2_13 (f x) (f y) := by
  simp only [p2_13, map_mul, map_p2_12, map_d9]
private theorem map_p2_14 {H : Type*} [Group H] (f : G →* H) :
    f (p2_14 x y) = p2_14 (f x) (f y) := by
  simp only [p2_14, map_mul, map_inv, map_p2_13]
private theorem map_p2_15 {H : Type*} [Group H] (f : G →* H) :
    f (p2_15 x y) = p2_15 (f x) (f y) := by
  simp only [p2_15, map_mul, map_p2_14, map_d17]
private theorem map_p2_16 {H : Type*} [Group H] (f : G →* H) :
    f (p2_16 x y) = p2_16 (f x) (f y) := by
  simp only [p2_16, map_mul, map_p2_15, map_d20]
private theorem map_p2_17 {H : Type*} [Group H] (f : G →* H) :
    f (p2_17 x y) = p2_17 (f x) (f y) := by
  simp only [p2_17, map_mul, map_p2_16, map_d38]
private theorem map_p2_18 {H : Type*} [Group H] (f : G →* H) :
    f (p2_18 x y) = p2_18 (f x) (f y) := by
  simp only [p2_18, map_mul, map_p2_17, map_d12]
private theorem map_p2_19 {H : Type*} [Group H] (f : G →* H) :
    f (p2_19 x y) = p2_19 (f x) (f y) := by
  simp only [p2_19, map_mul, map_p2_18, map_d9]
private theorem map_p2_20 {H : Type*} [Group H] (f : G →* H) :
    f (p2_20 x y) = p2_20 (f x) (f y) := by
  simp only [p2_20, map_mul, map_p2_19, map_d28]
private theorem map_p2_21 {H : Type*} [Group H] (f : G →* H) :
    f (p2_21 x y) = p2_21 (f x) (f y) := by
  simp only [p2_21, map_mul, map_p2_20, map_d6]
private theorem map_p2_22 {H : Type*} [Group H] (f : G →* H) :
    f (p2_22 x y) = p2_22 (f x) (f y) := by
  simp only [p2_22, map_mul, map_p2_21, map_d15]
private theorem map_p2_23 {H : Type*} [Group H] (f : G →* H) :
    f (p2_23 x y) = p2_23 (f x) (f y) := by
  simp only [p2_23, map_mul, map_p2_22, map_d43]
private theorem map_p3_0 {H : Type*} [Group H] (f : G →* H) :
    f (p3_0 x y) = p3_0 (f x) (f y) := by
  simp only [p3_0, map_mul, map_inv, map_d11]
private theorem map_p3_1 {H : Type*} [Group H] (f : G →* H) :
    f (p3_1 x y) = p3_1 (f x) (f y) := by
  simp only [p3_1, map_mul, map_p3_0, map_d18]
private theorem map_p3_2 {H : Type*} [Group H] (f : G →* H) :
    f (p3_2 x y) = p3_2 (f x) (f y) := by
  simp only [p3_2, map_mul, map_p3_1, map_d6]
private theorem map_p3_3 {H : Type*} [Group H] (f : G →* H) :
    f (p3_3 x y) = p3_3 (f x) (f y) := by
  simp only [p3_3, map_mul, map_p3_2, map_d11]
private theorem map_p3_4 {H : Type*} [Group H] (f : G →* H) :
    f (p3_4 x y) = p3_4 (f x) (f y) := by
  simp only [p3_4, map_mul, map_p3_3, map_d11]
private theorem map_p3_5 {H : Type*} [Group H] (f : G →* H) :
    f (p3_5 x y) = p3_5 (f x) (f y) := by
  simp only [p3_5, map_mul, map_p3_4, map_d10]
private theorem map_p3_6 {H : Type*} [Group H] (f : G →* H) :
    f (p3_6 x y) = p3_6 (f x) (f y) := by
  simp only [p3_6, map_mul, map_p3_5, map_d18]
private theorem map_p3_7 {H : Type*} [Group H] (f : G →* H) :
    f (p3_7 x y) = p3_7 (f x) (f y) := by
  simp only [p3_7, map_mul, map_p3_6, map_d44]
private theorem map_p3_8 {H : Type*} [Group H] (f : G →* H) :
    f (p3_8 x y) = p3_8 (f x) (f y) := by
  simp only [p3_8, map_mul, map_p3_7, map_d40]
private theorem map_p3_9 {H : Type*} [Group H] (f : G →* H) :
    f (p3_9 x y) = p3_9 (f x) (f y) := by
  simp only [p3_9, map_mul, map_p3_8, map_d45]
private theorem map_p3_10 {H : Type*} [Group H] (f : G →* H) :
    f (p3_10 x y) = p3_10 (f x) (f y) := by
  simp only [p3_10, map_mul, map_p3_9, map_d39]
private theorem map_p3_11 {H : Type*} [Group H] (f : G →* H) :
    f (p3_11 x y) = p3_11 (f x) (f y) := by
  simp only [p3_11, map_mul, map_p3_10, map_d41]
private theorem map_p3_12 {H : Type*} [Group H] (f : G →* H) :
    f (p3_12 x y) = p3_12 (f x) (f y) := by
  simp only [p3_12, map_mul, map_p3_11, map_d4]
private theorem map_p3_13 {H : Type*} [Group H] (f : G →* H) :
    f (p3_13 x y) = p3_13 (f x) (f y) := by
  simp only [p3_13, map_mul, map_p3_12, map_d15]
private theorem map_p3_14 {H : Type*} [Group H] (f : G →* H) :
    f (p3_14 x y) = p3_14 (f x) (f y) := by
  simp only [p3_14, map_mul, map_p3_13, map_d8]
private theorem map_p3_15 {H : Type*} [Group H] (f : G →* H) :
    f (p3_15 x y) = p3_15 (f x) (f y) := by
  simp only [p3_15, map_mul, map_p3_14, map_d9]
private theorem map_p3_16 {H : Type*} [Group H] (f : G →* H) :
    f (p3_16 x y) = p3_16 (f x) (f y) := by
  simp only [p3_16, map_mul, map_p3_15, map_d20]
private theorem map_p3_17 {H : Type*} [Group H] (f : G →* H) :
    f (p3_17 x y) = p3_17 (f x) (f y) := by
  simp only [p3_17, map_mul, map_p3_16, map_d28]
private theorem map_p3_18 {H : Type*} [Group H] (f : G →* H) :
    f (p3_18 x y) = p3_18 (f x) (f y) := by
  simp only [p3_18, map_mul, map_p3_17, map_d17]
private theorem map_p3_19 {H : Type*} [Group H] (f : G →* H) :
    f (p3_19 x y) = p3_19 (f x) (f y) := by
  simp only [p3_19, map_mul, map_p3_18, map_d22]
private theorem map_p3_20 {H : Type*} [Group H] (f : G →* H) :
    f (p3_20 x y) = p3_20 (f x) (f y) := by
  simp only [p3_20, map_mul, map_p3_19, map_d29]
private theorem map_p3_21 {H : Type*} [Group H] (f : G →* H) :
    f (p3_21 x y) = p3_21 (f x) (f y) := by
  simp only [p3_21, map_mul, map_p3_20, map_d37]
theorem map_lifts {H : Type*} [Group H] (f : G →* H) (i : Fin 4) :
    f (lifts x y i) = lifts (f x) (f y) i := by
  fin_cases i
  · exact map_p0_22 x y f
  · exact map_p1_35 x y f
  · exact map_p2_23 x y f
  · exact map_p3_21 x y f
end NativeWords

noncomputable section
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY
def kernelMasks : Fin 6 → ℕ := ![51, 73, 140, 281, 515, 1041]
def correctionMasks : Fin 4 → ℕ := ![13, 13, 22, 15]
def kernelGenerator (i : Fin 6) : M := maskValue matrixA_mul_self matrixB_pow_four (kernelMasks i)
def lift (i : Fin 4) : M :=
  NativeWords.lifts (localX matrixA_mul_self matrixB_pow_four)
    (localY matrixA_mul_self matrixB_pow_four) i *
      maskValue matrixA_mul_self matrixB_pow_four (correctionMasks i)
def generators : Fin 10 → M := Fin.append kernelGenerator lift
def localF : Subgroup M := Subgroup.closure (Set.range generators)
def F : Subgroup Model := localF.map M.subtype
theorem F_le_M : F ≤ M := Subgroup.map_subtype_le _
theorem generator_mem_localF (i : Fin 10) : generators i ∈ localF :=
  Subgroup.subset_closure (Set.mem_range_self i)
theorem generator_mem_F (i : Fin 10) : (generators i : Model) ∈ F :=
  Subgroup.mem_map.mpr ⟨generators i, generator_mem_localF i, rfl⟩
end
end Janko4.LocalStructure.LinearFive
