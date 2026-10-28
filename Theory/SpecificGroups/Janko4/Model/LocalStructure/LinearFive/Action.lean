module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products0

/-!
# Native conjugation on the eleven-dimensional kernel

Conjugation is transported along the literal word DAG using the already proved
eleven-bit action. The four corrected lifts fix the six chosen kernel words.
Their complete right-conjugation matrices will determine the common fixed kernel.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Janko4.GeneratorCertificates Cardinality KernelCount KernelCount.Relations
open Simplicity.Max1Fusion.KernelOrbits QuotientCount.Image
open NativeRows NativeWords
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four
local notation "x" => localX matrixA_mul_self matrixB_pow_four
local notation "y" => localY matrixA_mul_self matrixB_pow_four
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
private theorem product_yy : packedMul yRows yRows = iyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem inverse_y_eq : y⁻¹ = y * y := by
  apply representation_injective matrixA_mul_self matrixB_pow_four
  exact (eval_inv ρ (representation_y _ _) (by
    rw [decoded_product inverse_y, decode_packedOne])).trans
      (eval_mul ρ (representation_y _ _) (representation_y _ _)
        (decoded_product product_yy)).symm

private theorem conjugate_product {G : Type*} [Group G] (e : ℕ → G)
    (g h : G) (a b : ℕ → ℕ)
    (hg : ∀ m, g⁻¹ * e m * g = e (a m))
    (hh : ∀ m, h⁻¹ * e m * h = e (b m)) (m : ℕ) :
    (g*h)⁻¹ * e m * (g*h) = e (b (a m)) := by
  calc
    _ = h⁻¹ * (g⁻¹ * e m * g) * h := by group
    _ = _ := by rw [hg, hh]

private def ax : ℕ → ℕ := maskImage xMasks
private def ay : ℕ → ℕ := maskImage yMasks
private def aiy (m : ℕ) : ℕ := ay (ay m)
private theorem conjugate_x (m : ℕ) : x⁻¹ * kernelValue m * x = kernelValue (ax m) :=
  right_conj_mask_x _ _ m
private theorem conjugate_ix (m : ℕ) : (x⁻¹)⁻¹ * kernelValue m * x⁻¹ = kernelValue (ax m) := by
  rw [inv_eq_of_mul_eq_one_left (localX_mul_self matrixA_mul_self matrixB_pow_four)]
  exact conjugate_x m
private theorem conjugate_y (m : ℕ) : y⁻¹ * kernelValue m * y = kernelValue (ay m) :=
  right_conj_mask_y _ _ m
private theorem conjugate_iy (m : ℕ) : (y⁻¹)⁻¹ * kernelValue m * y⁻¹ = kernelValue (aiy m) := by
  rw [inverse_y_eq]
  exact conjugate_product kernelValue y y ay ay conjugate_y conjugate_y m
private def a_d3 (m : ℕ) : ℕ := ay (ax m)
private theorem conjugate_d3 (m : ℕ) :
    (d3 x y)⁻¹ * kernelValue m * (d3 x y) = kernelValue (a_d3 m) :=
  conjugate_product kernelValue x y ax ay conjugate_x conjugate_y m
private def a_d4 (m : ℕ) : ℕ := aiy (ax m)
private theorem conjugate_d4 (m : ℕ) :
    (d4 x y)⁻¹ * kernelValue m * (d4 x y) = kernelValue (a_d4 m) :=
  conjugate_product kernelValue x y⁻¹ ax aiy conjugate_x conjugate_iy m
private def a_d5 (m : ℕ) : ℕ := ay (ax m)
private theorem conjugate_d5 (m : ℕ) :
    (d5 x y)⁻¹ * kernelValue m * (d5 x y) = kernelValue (a_d5 m) :=
  conjugate_product kernelValue x⁻¹ y ax ay conjugate_ix conjugate_y m
private def a_d6 (m : ℕ) : ℕ := aiy (ax m)
private theorem conjugate_d6 (m : ℕ) :
    (d6 x y)⁻¹ * kernelValue m * (d6 x y) = kernelValue (a_d6 m) :=
  conjugate_product kernelValue x⁻¹ y⁻¹ ax aiy conjugate_ix conjugate_iy m
private def a_d7 (m : ℕ) : ℕ := a_d3 (a_d4 m)
private theorem conjugate_d7 (m : ℕ) :
    (d7 x y)⁻¹ * kernelValue m * (d7 x y) = kernelValue (a_d7 m) :=
  conjugate_product kernelValue (d4 x y) (d3 x y) a_d4 a_d3 conjugate_d4 conjugate_d3 m
private def a_d8 (m : ℕ) : ℕ := a_d5 (a_d5 m)
private theorem conjugate_d8 (m : ℕ) :
    (d8 x y)⁻¹ * kernelValue m * (d8 x y) = kernelValue (a_d8 m) :=
  conjugate_product kernelValue (d5 x y) (d5 x y) a_d5 a_d5 conjugate_d5 conjugate_d5 m
private def a_d9 (m : ℕ) : ℕ := a_d6 (a_d6 m)
private theorem conjugate_d9 (m : ℕ) :
    (d9 x y)⁻¹ * kernelValue m * (d9 x y) = kernelValue (a_d9 m) :=
  conjugate_product kernelValue (d6 x y) (d6 x y) a_d6 a_d6 conjugate_d6 conjugate_d6 m
private def a_d10 (m : ℕ) : ℕ := a_d7 (a_d4 m)
private theorem conjugate_d10 (m : ℕ) :
    (d10 x y)⁻¹ * kernelValue m * (d10 x y) = kernelValue (a_d10 m) :=
  conjugate_product kernelValue (d4 x y) (d7 x y) a_d4 a_d7 conjugate_d4 conjugate_d7 m
private def a_d11 (m : ℕ) : ℕ := a_d3 (a_d3 m)
private theorem conjugate_d11 (m : ℕ) :
    (d11 x y)⁻¹ * kernelValue m * (d11 x y) = kernelValue (a_d11 m) :=
  conjugate_product kernelValue (d3 x y) (d3 x y) a_d3 a_d3 conjugate_d3 conjugate_d3 m
private def a_d12 (m : ℕ) : ℕ := a_d10 (a_d4 m)
private theorem conjugate_d12 (m : ℕ) :
    (d12 x y)⁻¹ * kernelValue m * (d12 x y) = kernelValue (a_d12 m) :=
  conjugate_product kernelValue (d4 x y) (d10 x y) a_d4 a_d10 conjugate_d4 conjugate_d10 m
private def a_d13 (m : ℕ) : ℕ := a_d6 (a_d5 m)
private theorem conjugate_d13 (m : ℕ) :
    (d13 x y)⁻¹ * kernelValue m * (d13 x y) = kernelValue (a_d13 m) :=
  conjugate_product kernelValue (d5 x y) (d6 x y) a_d5 a_d6 conjugate_d5 conjugate_d6 m
private def a_d14 (m : ℕ) : ℕ := a_d7 (a_d3 m)
private theorem conjugate_d14 (m : ℕ) :
    (d14 x y)⁻¹ * kernelValue m * (d14 x y) = kernelValue (a_d14 m) :=
  conjugate_product kernelValue (d3 x y) (d7 x y) a_d3 a_d7 conjugate_d3 conjugate_d7 m
private def a_d15 (m : ℕ) : ℕ := a_d9 (a_d5 m)
private theorem conjugate_d15 (m : ℕ) :
    (d15 x y)⁻¹ * kernelValue m * (d15 x y) = kernelValue (a_d15 m) :=
  conjugate_product kernelValue (d5 x y) (d9 x y) a_d5 a_d9 conjugate_d5 conjugate_d9 m
private def a_d16 (m : ℕ) : ℕ := a_d11 (a_d7 m)
private theorem conjugate_d16 (m : ℕ) :
    (d16 x y)⁻¹ * kernelValue m * (d16 x y) = kernelValue (a_d16 m) :=
  conjugate_product kernelValue (d7 x y) (d11 x y) a_d7 a_d11 conjugate_d7 conjugate_d11 m
private def a_d17 (m : ℕ) : ℕ := a_d8 (a_d13 m)
private theorem conjugate_d17 (m : ℕ) :
    (d17 x y)⁻¹ * kernelValue m * (d17 x y) = kernelValue (a_d17 m) :=
  conjugate_product kernelValue (d13 x y) (d8 x y) a_d13 a_d8 conjugate_d13 conjugate_d8 m
private def a_d18 (m : ℕ) : ℕ := a_d14 (a_d10 m)
private theorem conjugate_d18 (m : ℕ) :
    (d18 x y)⁻¹ * kernelValue m * (d18 x y) = kernelValue (a_d18 m) :=
  conjugate_product kernelValue (d10 x y) (d14 x y) a_d10 a_d14 conjugate_d10 conjugate_d14 m
private def a_d19 (m : ℕ) : ℕ := a_d12 (a_d4 m)
private theorem conjugate_d19 (m : ℕ) :
    (d19 x y)⁻¹ * kernelValue m * (d19 x y) = kernelValue (a_d19 m) :=
  conjugate_product kernelValue (d4 x y) (d12 x y) a_d4 a_d12 conjugate_d4 conjugate_d12 m
private def a_d20 (m : ℕ) : ℕ := a_d8 (a_d6 m)
private theorem conjugate_d20 (m : ℕ) :
    (d20 x y)⁻¹ * kernelValue m * (d20 x y) = kernelValue (a_d20 m) :=
  conjugate_product kernelValue (d6 x y) (d8 x y) a_d6 a_d8 conjugate_d6 conjugate_d8 m
private def a_d21 (m : ℕ) : ℕ := a_d12 (a_d3 m)
private theorem conjugate_d21 (m : ℕ) :
    (d21 x y)⁻¹ * kernelValue m * (d21 x y) = kernelValue (a_d21 m) :=
  conjugate_product kernelValue (d3 x y) (d12 x y) a_d3 a_d12 conjugate_d3 conjugate_d12 m
private def a_d22 (m : ℕ) : ℕ := a_d14 (a_d7 m)
private theorem conjugate_d22 (m : ℕ) :
    (d22 x y)⁻¹ * kernelValue m * (d22 x y) = kernelValue (a_d22 m) :=
  conjugate_product kernelValue (d7 x y) (d14 x y) a_d7 a_d14 conjugate_d7 conjugate_d14 m
private def a_d23 (m : ℕ) : ℕ := a_d8 (a_d8 m)
private theorem conjugate_d23 (m : ℕ) :
    (d23 x y)⁻¹ * kernelValue m * (d23 x y) = kernelValue (a_d23 m) :=
  conjugate_product kernelValue (d8 x y) (d8 x y) a_d8 a_d8 conjugate_d8 conjugate_d8 m
private def a_d24 (m : ℕ) : ℕ := a_d19 (a_d4 m)
private theorem conjugate_d24 (m : ℕ) :
    (d24 x y)⁻¹ * kernelValue m * (d24 x y) = kernelValue (a_d24 m) :=
  conjugate_product kernelValue (d4 x y) (d19 x y) a_d4 a_d19 conjugate_d4 conjugate_d19 m
private def a_d25 (m : ℕ) : ℕ := aiy (a_d4 m)
private theorem conjugate_d25 (m : ℕ) :
    (d25 x y)⁻¹ * kernelValue m * (d25 x y) = kernelValue (a_d25 m) :=
  conjugate_product kernelValue (d4 x y) y⁻¹ a_d4 aiy conjugate_d4 conjugate_iy m
private def a_d26 (m : ℕ) : ℕ := aiy (a_d13 m)
private theorem conjugate_d26 (m : ℕ) :
    (d26 x y)⁻¹ * kernelValue m * (d26 x y) = kernelValue (a_d26 m) :=
  conjugate_product kernelValue (d13 x y) y⁻¹ a_d13 aiy conjugate_d13 conjugate_iy m
private def a_d27 (m : ℕ) : ℕ := a_d16 (a_d11 m)
private theorem conjugate_d27 (m : ℕ) :
    (d27 x y)⁻¹ * kernelValue m * (d27 x y) = kernelValue (a_d27 m) :=
  conjugate_product kernelValue (d11 x y) (d16 x y) a_d11 a_d16 conjugate_d11 conjugate_d16 m
private def a_d28 (m : ℕ) : ℕ := a_d8 (a_d9 m)
private theorem conjugate_d28 (m : ℕ) :
    (d28 x y)⁻¹ * kernelValue m * (d28 x y) = kernelValue (a_d28 m) :=
  conjugate_product kernelValue (d9 x y) (d8 x y) a_d9 a_d8 conjugate_d9 conjugate_d8 m
private def a_d29 (m : ℕ) : ℕ := a_d10 (a_d7 m)
private theorem conjugate_d29 (m : ℕ) :
    (d29 x y)⁻¹ * kernelValue m * (d29 x y) = kernelValue (a_d29 m) :=
  conjugate_product kernelValue (d7 x y) (d10 x y) a_d7 a_d10 conjugate_d7 conjugate_d10 m
private def a_d30 (m : ℕ) : ℕ := ax (a_d4 m)
private theorem conjugate_d30 (m : ℕ) :
    (d30 x y)⁻¹ * kernelValue m * (d30 x y) = kernelValue (a_d30 m) :=
  conjugate_product kernelValue (d4 x y) x a_d4 ax conjugate_d4 conjugate_x m
private def a_d31 (m : ℕ) : ℕ := a_d21 (a_d11 m)
private theorem conjugate_d31 (m : ℕ) :
    (d31 x y)⁻¹ * kernelValue m * (d31 x y) = kernelValue (a_d31 m) :=
  conjugate_product kernelValue (d11 x y) (d21 x y) a_d11 a_d21 conjugate_d11 conjugate_d21 m
private def a_d32 (m : ℕ) : ℕ := a_d27 (a_d12 m)
private theorem conjugate_d32 (m : ℕ) :
    (d32 x y)⁻¹ * kernelValue m * (d32 x y) = kernelValue (a_d32 m) :=
  conjugate_product kernelValue (d12 x y) (d27 x y) a_d12 a_d27 conjugate_d12 conjugate_d27 m
private def a_d33 (m : ℕ) : ℕ := a_d3 (a_d32 m)
private theorem conjugate_d33 (m : ℕ) :
    (d33 x y)⁻¹ * kernelValue m * (d33 x y) = kernelValue (a_d33 m) :=
  conjugate_product kernelValue (d32 x y) (d3 x y) a_d32 a_d3 conjugate_d32 conjugate_d3 m
private def a_d34 (m : ℕ) : ℕ := a_d13 (a_d33 m)
private theorem conjugate_d34 (m : ℕ) :
    (d34 x y)⁻¹ * kernelValue m * (d34 x y) = kernelValue (a_d34 m) :=
  conjugate_product kernelValue (d33 x y) (d13 x y) a_d33 a_d13 conjugate_d33 conjugate_d13 m
private def a_d35 (m : ℕ) : ℕ := a_d26 (a_d34 m)
private theorem conjugate_d35 (m : ℕ) :
    (d35 x y)⁻¹ * kernelValue m * (d35 x y) = kernelValue (a_d35 m) :=
  conjugate_product kernelValue (d34 x y) (d26 x y) a_d34 a_d26 conjugate_d34 conjugate_d26 m
private def a_d36 (m : ℕ) : ℕ := a_d21 (a_d35 m)
private theorem conjugate_d36 (m : ℕ) :
    (d36 x y)⁻¹ * kernelValue m * (d36 x y) = kernelValue (a_d36 m) :=
  conjugate_product kernelValue (d35 x y) (d21 x y) a_d35 a_d21 conjugate_d35 conjugate_d21 m
private def a_d37 (m : ℕ) : ℕ := a_d11 (a_d36 m)
private theorem conjugate_d37 (m : ℕ) :
    (d37 x y)⁻¹ * kernelValue m * (d37 x y) = kernelValue (a_d37 m) :=
  conjugate_product kernelValue (d36 x y) (d11 x y) a_d36 a_d11 conjugate_d36 conjugate_d11 m
private def a_d38 (m : ℕ) : ℕ := ay (a_d8 m)
private theorem conjugate_d38 (m : ℕ) :
    (d38 x y)⁻¹ * kernelValue m * (d38 x y) = kernelValue (a_d38 m) :=
  conjugate_product kernelValue (d8 x y) y a_d8 ay conjugate_d8 conjugate_y m
private def a_d39 (m : ℕ) : ℕ := a_d12 (a_d7 m)
private theorem conjugate_d39 (m : ℕ) :
    (d39 x y)⁻¹ * kernelValue m * (d39 x y) = kernelValue (a_d39 m) :=
  conjugate_product kernelValue (d7 x y) (d12 x y) a_d7 a_d12 conjugate_d7 conjugate_d12 m
private def a_d40 (m : ℕ) : ℕ := ax (a_d3 m)
private theorem conjugate_d40 (m : ℕ) :
    (d40 x y)⁻¹ * kernelValue m * (d40 x y) = kernelValue (a_d40 m) :=
  conjugate_product kernelValue (d3 x y) x a_d3 ax conjugate_d3 conjugate_x m
private def a_d41 (m : ℕ) : ℕ := a_d11 (a_d22 m)
private theorem conjugate_d41 (m : ℕ) :
    (d41 x y)⁻¹ * kernelValue m * (d41 x y) = kernelValue (a_d41 m) :=
  conjugate_product kernelValue (d22 x y) (d11 x y) a_d22 a_d11 conjugate_d22 conjugate_d11 m
private def a_d42 (m : ℕ) : ℕ := a_d15 (a_d17 m)
private theorem conjugate_d42 (m : ℕ) :
    (d42 x y)⁻¹ * kernelValue m * (d42 x y) = kernelValue (a_d42 m) :=
  conjugate_product kernelValue (d17 x y) (d15 x y) a_d17 a_d15 conjugate_d17 conjugate_d15 m
private def a_d43 (m : ℕ) : ℕ := a_d6 (a_d9 m)
private theorem conjugate_d43 (m : ℕ) :
    (d43 x y)⁻¹ * kernelValue m * (d43 x y) = kernelValue (a_d43 m) :=
  conjugate_product kernelValue (d9 x y) (d6 x y) a_d9 a_d6 conjugate_d9 conjugate_d6 m
private def a_d44 (m : ℕ) : ℕ := a_d10 (a_d18 m)
private theorem conjugate_d44 (m : ℕ) :
    (d44 x y)⁻¹ * kernelValue m * (d44 x y) = kernelValue (a_d44 m) :=
  conjugate_product kernelValue (d18 x y) (d10 x y) a_d18 a_d10 conjugate_d18 conjugate_d10 m
private def a_d45 (m : ℕ) : ℕ := a_d14 (a_d16 m)
private theorem conjugate_d45 (m : ℕ) :
    (d45 x y)⁻¹ * kernelValue m * (d45 x y) = kernelValue (a_d45 m) :=
  conjugate_product kernelValue (d16 x y) (d14 x y) a_d16 a_d14 conjugate_d16 conjugate_d14 m
private def a_p0_0 (m : ℕ) : ℕ := a_d6 (a_d23 m)
private theorem conjugate_p0_0 (m : ℕ) :
    (p0_0 x y)⁻¹ * kernelValue m * (p0_0 x y) = kernelValue (a_p0_0 m) :=
  conjugate_product kernelValue (d23 x y) (d6 x y) a_d23 a_d6 conjugate_d23 conjugate_d6 m
private def a_p0_1 (m : ℕ) : ℕ := a_d13 (a_p0_0 m)
private theorem conjugate_p0_1 (m : ℕ) :
    (p0_1 x y)⁻¹ * kernelValue m * (p0_1 x y) = kernelValue (a_p0_1 m) :=
  conjugate_product kernelValue (p0_0 x y) (d13 x y) a_p0_0 a_d13 conjugate_p0_0 conjugate_d13 m
private def a_p0_2 (m : ℕ) : ℕ := a_d15 (a_p0_1 m)
private theorem conjugate_p0_2 (m : ℕ) :
    (p0_2 x y)⁻¹ * kernelValue m * (p0_2 x y) = kernelValue (a_p0_2 m) :=
  conjugate_product kernelValue (p0_1 x y) (d15 x y) a_p0_1 a_d15 conjugate_p0_1 conjugate_d15 m
private def a_p0_3 (m : ℕ) : ℕ := a_d13 (a_p0_2 m)
private theorem conjugate_p0_3 (m : ℕ) :
    (p0_3 x y)⁻¹ * kernelValue m * (p0_3 x y) = kernelValue (a_p0_3 m) :=
  conjugate_product kernelValue (p0_2 x y) (d13 x y) a_p0_2 a_d13 conjugate_p0_2 conjugate_d13 m
private def a_p0_4 (m : ℕ) : ℕ := a_d12 (a_p0_3 m)
private theorem conjugate_p0_4 (m : ℕ) :
    (p0_4 x y)⁻¹ * kernelValue m * (p0_4 x y) = kernelValue (a_p0_4 m) :=
  conjugate_product kernelValue (p0_3 x y) (d12 x y) a_p0_3 a_d12 conjugate_p0_3 conjugate_d12 m
private def a_p0_5 (m : ℕ) : ℕ := a_d29 (a_p0_4 m)
private theorem conjugate_p0_5 (m : ℕ) :
    (p0_5 x y)⁻¹ * kernelValue m * (p0_5 x y) = kernelValue (a_p0_5 m) :=
  conjugate_product kernelValue (p0_4 x y) (d29 x y) a_p0_4 a_d29 conjugate_p0_4 conjugate_d29 m
private def a_p0_6 (m : ℕ) : ℕ := a_d18 (a_p0_5 m)
private theorem conjugate_p0_6 (m : ℕ) :
    (p0_6 x y)⁻¹ * kernelValue m * (p0_6 x y) = kernelValue (a_p0_6 m) :=
  conjugate_product kernelValue (p0_5 x y) (d18 x y) a_p0_5 a_d18 conjugate_p0_5 conjugate_d18 m
private def a_p0_7 (m : ℕ) : ℕ := a_d3 (a_p0_6 m)
private theorem conjugate_p0_7 (m : ℕ) :
    (p0_7 x y)⁻¹ * kernelValue m * (p0_7 x y) = kernelValue (a_p0_7 m) :=
  conjugate_product kernelValue (p0_6 x y) (d3 x y) a_p0_6 a_d3 conjugate_p0_6 conjugate_d3 m
private def a_p0_8 (m : ℕ) : ℕ := a_d10 (a_p0_7 m)
private theorem conjugate_p0_8 (m : ℕ) :
    (p0_8 x y)⁻¹ * kernelValue m * (p0_8 x y) = kernelValue (a_p0_8 m) :=
  conjugate_product kernelValue (p0_7 x y) (d10 x y) a_p0_7 a_d10 conjugate_p0_7 conjugate_d10 m
private def a_p0_9 (m : ℕ) : ℕ := a_d11 (a_p0_8 m)
private theorem conjugate_p0_9 (m : ℕ) :
    (p0_9 x y)⁻¹ * kernelValue m * (p0_9 x y) = kernelValue (a_p0_9 m) :=
  conjugate_product kernelValue (p0_8 x y) (d11 x y) a_p0_8 a_d11 conjugate_p0_8 conjugate_d11 m
private def a_p0_10 (m : ℕ) : ℕ := a_d7 (a_p0_9 m)
private theorem conjugate_p0_10 (m : ℕ) :
    (p0_10 x y)⁻¹ * kernelValue m * (p0_10 x y) = kernelValue (a_p0_10 m) :=
  conjugate_product kernelValue (p0_9 x y) (d7 x y) a_p0_9 a_d7 conjugate_p0_9 conjugate_d7 m
private def a_p0_11 (m : ℕ) : ℕ := a_d19 (a_p0_10 m)
private theorem conjugate_p0_11 (m : ℕ) :
    (p0_11 x y)⁻¹ * kernelValue m * (p0_11 x y) = kernelValue (a_p0_11 m) :=
  conjugate_product kernelValue (p0_10 x y) (d19 x y) a_p0_10 a_d19 conjugate_p0_10 conjugate_d19 m
private def a_p0_12 (m : ℕ) : ℕ := a_d19 (a_p0_11 m)
private theorem conjugate_p0_12 (m : ℕ) :
    (p0_12 x y)⁻¹ * kernelValue m * (p0_12 x y) = kernelValue (a_p0_12 m) :=
  conjugate_product kernelValue (p0_11 x y) (d19 x y) a_p0_11 a_d19 conjugate_p0_11 conjugate_d19 m
private def a_p0_13 (m : ℕ) : ℕ := a_d30 (a_p0_12 m)
private theorem conjugate_p0_13 (m : ℕ) :
    (p0_13 x y)⁻¹ * kernelValue m * (p0_13 x y) = kernelValue (a_p0_13 m) :=
  conjugate_product kernelValue (p0_12 x y) (d30 x y) a_p0_12 a_d30 conjugate_p0_12 conjugate_d30 m
private def a_p0_14 (m : ℕ) : ℕ := a_d16 (a_p0_13 m)
private theorem conjugate_p0_14 (m : ℕ) :
    (p0_14 x y)⁻¹ * kernelValue m * (p0_14 x y) = kernelValue (a_p0_14 m) :=
  conjugate_product kernelValue (p0_13 x y) (d16 x y) a_p0_13 a_d16 conjugate_p0_13 conjugate_d16 m
private def a_p0_15 (m : ℕ) : ℕ := a_d31 (a_p0_14 m)
private theorem conjugate_p0_15 (m : ℕ) :
    (p0_15 x y)⁻¹ * kernelValue m * (p0_15 x y) = kernelValue (a_p0_15 m) :=
  conjugate_product kernelValue (p0_14 x y) (d31 x y) a_p0_14 a_d31 conjugate_p0_14 conjugate_d31 m
private def a_p0_16 (m : ℕ) : ℕ := a_d24 (a_p0_15 m)
private theorem conjugate_p0_16 (m : ℕ) :
    (p0_16 x y)⁻¹ * kernelValue m * (p0_16 x y) = kernelValue (a_p0_16 m) :=
  conjugate_product kernelValue (p0_15 x y) (d24 x y) a_p0_15 a_d24 conjugate_p0_15 conjugate_d24 m
private def a_p0_17 (m : ℕ) : ℕ := a_d25 (a_p0_16 m)
private theorem conjugate_p0_17 (m : ℕ) :
    (p0_17 x y)⁻¹ * kernelValue m * (p0_17 x y) = kernelValue (a_p0_17 m) :=
  conjugate_product kernelValue (p0_16 x y) (d25 x y) a_p0_16 a_d25 conjugate_p0_16 conjugate_d25 m
private def a_p0_18 (m : ℕ) : ℕ := a_d17 (a_p0_17 m)
private theorem conjugate_p0_18 (m : ℕ) :
    (p0_18 x y)⁻¹ * kernelValue m * (p0_18 x y) = kernelValue (a_p0_18 m) :=
  conjugate_product kernelValue (p0_17 x y) (d17 x y) a_p0_17 a_d17 conjugate_p0_17 conjugate_d17 m
private def a_p0_19 (m : ℕ) : ℕ := a_d26 (a_p0_18 m)
private theorem conjugate_p0_19 (m : ℕ) :
    (p0_19 x y)⁻¹ * kernelValue m * (p0_19 x y) = kernelValue (a_p0_19 m) :=
  conjugate_product kernelValue (p0_18 x y) (d26 x y) a_p0_18 a_d26 conjugate_p0_18 conjugate_d26 m
private def a_p0_20 (m : ℕ) : ℕ := a_d27 (a_p0_19 m)
private theorem conjugate_p0_20 (m : ℕ) :
    (p0_20 x y)⁻¹ * kernelValue m * (p0_20 x y) = kernelValue (a_p0_20 m) :=
  conjugate_product kernelValue (p0_19 x y) (d27 x y) a_p0_19 a_d27 conjugate_p0_19 conjugate_d27 m
private def a_p0_21 (m : ℕ) : ℕ := a_d10 (a_p0_20 m)
private theorem conjugate_p0_21 (m : ℕ) :
    (p0_21 x y)⁻¹ * kernelValue m * (p0_21 x y) = kernelValue (a_p0_21 m) :=
  conjugate_product kernelValue (p0_20 x y) (d10 x y) a_p0_20 a_d10 conjugate_p0_20 conjugate_d10 m
private def a_p0_22 (m : ℕ) : ℕ := a_d37 (a_p0_21 m)
private theorem conjugate_p0_22 (m : ℕ) :
    (p0_22 x y)⁻¹ * kernelValue m * (p0_22 x y) = kernelValue (a_p0_22 m) :=
  conjugate_product kernelValue (p0_21 x y) (d37 x y) a_p0_21 a_d37 conjugate_p0_21 conjugate_d37 m
private def a_p1_0 (m : ℕ) : ℕ := a_d38 (a_d23 m)
private theorem conjugate_p1_0 (m : ℕ) :
    (p1_0 x y)⁻¹ * kernelValue m * (p1_0 x y) = kernelValue (a_p1_0 m) :=
  conjugate_product kernelValue (d23 x y) (d38 x y) a_d23 a_d38 conjugate_d23 conjugate_d38 m
private def a_p1_1 (m : ℕ) : ℕ := a_d7 (a_p1_0 m)
private theorem conjugate_p1_1 (m : ℕ) :
    (p1_1 x y)⁻¹ * kernelValue m * (p1_1 x y) = kernelValue (a_p1_1 m) :=
  conjugate_product kernelValue (p1_0 x y) (d7 x y) a_p1_0 a_d7 conjugate_p1_0 conjugate_d7 m
private def a_p1_2 (m : ℕ) : ℕ := a_d39 (a_p1_1 m)
private theorem conjugate_p1_2 (m : ℕ) :
    (p1_2 x y)⁻¹ * kernelValue m * (p1_2 x y) = kernelValue (a_p1_2 m) :=
  conjugate_product kernelValue (p1_1 x y) (d39 x y) a_p1_1 a_d39 conjugate_p1_1 conjugate_d39 m
private def a_p1_3 (m : ℕ) : ℕ := a_d40 (a_p1_2 m)
private theorem conjugate_p1_3 (m : ℕ) :
    (p1_3 x y)⁻¹ * kernelValue m * (p1_3 x y) = kernelValue (a_p1_3 m) :=
  conjugate_product kernelValue (p1_2 x y) (d40 x y) a_p1_2 a_d40 conjugate_p1_2 conjugate_d40 m
private def a_p1_4 (m : ℕ) : ℕ := a_d7 (a_p1_3 m)
private theorem conjugate_p1_4 (m : ℕ) :
    (p1_4 x y)⁻¹ * kernelValue m * (p1_4 x y) = kernelValue (a_p1_4 m) :=
  conjugate_product kernelValue (p1_3 x y) (d7 x y) a_p1_3 a_d7 conjugate_p1_3 conjugate_d7 m
private def a_p1_5 (m : ℕ) : ℕ := a_d41 (a_p1_4 m)
private theorem conjugate_p1_5 (m : ℕ) :
    (p1_5 x y)⁻¹ * kernelValue m * (p1_5 x y) = kernelValue (a_p1_5 m) :=
  conjugate_product kernelValue (p1_4 x y) (d41 x y) a_p1_4 a_d41 conjugate_p1_4 conjugate_d41 m
private def a_p1_6 (m : ℕ) : ℕ := ax (a_p1_5 m)
private theorem conjugate_p1_6 (m : ℕ) :
    (p1_6 x y)⁻¹ * kernelValue m * (p1_6 x y) = kernelValue (a_p1_6 m) :=
  conjugate_product kernelValue (p1_5 x y) x a_p1_5 ax conjugate_p1_5 conjugate_x m
private def a_p1_7 (m : ℕ) : ℕ := a_d4 (a_p1_6 m)
private theorem conjugate_p1_7 (m : ℕ) :
    (p1_7 x y)⁻¹ * kernelValue m * (p1_7 x y) = kernelValue (a_p1_7 m) :=
  conjugate_product kernelValue (p1_6 x y) (d4 x y) a_p1_6 a_d4 conjugate_p1_6 conjugate_d4 m
private def a_p1_8 (m : ℕ) : ℕ := a_d24 (a_p1_7 m)
private theorem conjugate_p1_8 (m : ℕ) :
    (p1_8 x y)⁻¹ * kernelValue m * (p1_8 x y) = kernelValue (a_p1_8 m) :=
  conjugate_product kernelValue (p1_7 x y) (d24 x y) a_p1_7 a_d24 conjugate_p1_7 conjugate_d24 m
private def a_p1_9 (m : ℕ) : ℕ := ay (a_p1_8 m)
private theorem conjugate_p1_9 (m : ℕ) :
    (p1_9 x y)⁻¹ * kernelValue m * (p1_9 x y) = kernelValue (a_p1_9 m) :=
  conjugate_product kernelValue (p1_8 x y) y a_p1_8 ay conjugate_p1_8 conjugate_y m
private def a_p1_10 (m : ℕ) : ℕ := a_d15 (a_p1_9 m)
private theorem conjugate_p1_10 (m : ℕ) :
    (p1_10 x y)⁻¹ * kernelValue m * (p1_10 x y) = kernelValue (a_p1_10 m) :=
  conjugate_product kernelValue (p1_9 x y) (d15 x y) a_p1_9 a_d15 conjugate_p1_9 conjugate_d15 m
private def a_p1_11 (m : ℕ) : ℕ := a_d28 (a_p1_10 m)
private theorem conjugate_p1_11 (m : ℕ) :
    (p1_11 x y)⁻¹ * kernelValue m * (p1_11 x y) = kernelValue (a_p1_11 m) :=
  conjugate_product kernelValue (p1_10 x y) (d28 x y) a_p1_10 a_d28 conjugate_p1_10 conjugate_d28 m
private def a_p1_12 (m : ℕ) : ℕ := a_d9 (a_p1_11 m)
private theorem conjugate_p1_12 (m : ℕ) :
    (p1_12 x y)⁻¹ * kernelValue m * (p1_12 x y) = kernelValue (a_p1_12 m) :=
  conjugate_product kernelValue (p1_11 x y) (d9 x y) a_p1_11 a_d9 conjugate_p1_11 conjugate_d9 m
private def a_p1_13 (m : ℕ) : ℕ := a_d15 (a_p1_12 m)
private theorem conjugate_p1_13 (m : ℕ) :
    (p1_13 x y)⁻¹ * kernelValue m * (p1_13 x y) = kernelValue (a_p1_13 m) :=
  conjugate_product kernelValue (p1_12 x y) (d15 x y) a_p1_12 a_d15 conjugate_p1_12 conjugate_d15 m
private def a_p1_14 (m : ℕ) : ℕ := a_d5 (a_p1_13 m)
private theorem conjugate_p1_14 (m : ℕ) :
    (p1_14 x y)⁻¹ * kernelValue m * (p1_14 x y) = kernelValue (a_p1_14 m) :=
  conjugate_product kernelValue (p1_13 x y) (d5 x y) a_p1_13 a_d5 conjugate_p1_13 conjugate_d5 m
private def a_p1_15 (m : ℕ) : ℕ := a_d14 (a_p1_14 m)
private theorem conjugate_p1_15 (m : ℕ) :
    (p1_15 x y)⁻¹ * kernelValue m * (p1_15 x y) = kernelValue (a_p1_15 m) :=
  conjugate_product kernelValue (p1_14 x y) (d14 x y) a_p1_14 a_d14 conjugate_p1_14 conjugate_d14 m
private def a_p1_16 (m : ℕ) : ℕ := a_d25 (a_p1_15 m)
private theorem conjugate_p1_16 (m : ℕ) :
    (p1_16 x y)⁻¹ * kernelValue m * (p1_16 x y) = kernelValue (a_p1_16 m) :=
  conjugate_product kernelValue (p1_15 x y) (d25 x y) a_p1_15 a_d25 conjugate_p1_15 conjugate_d25 m
private def a_p1_17 (m : ℕ) : ℕ := a_d20 (a_p1_16 m)
private theorem conjugate_p1_17 (m : ℕ) :
    (p1_17 x y)⁻¹ * kernelValue m * (p1_17 x y) = kernelValue (a_p1_17 m) :=
  conjugate_product kernelValue (p1_16 x y) (d20 x y) a_p1_16 a_d20 conjugate_p1_16 conjugate_d20 m
private def a_p1_18 (m : ℕ) : ℕ := a_d6 (a_p1_17 m)
private theorem conjugate_p1_18 (m : ℕ) :
    (p1_18 x y)⁻¹ * kernelValue m * (p1_18 x y) = kernelValue (a_p1_18 m) :=
  conjugate_product kernelValue (p1_17 x y) (d6 x y) a_p1_17 a_d6 conjugate_p1_17 conjugate_d6 m
private def a_p1_19 (m : ℕ) : ℕ := a_d5 (a_p1_18 m)
private theorem conjugate_p1_19 (m : ℕ) :
    (p1_19 x y)⁻¹ * kernelValue m * (p1_19 x y) = kernelValue (a_p1_19 m) :=
  conjugate_product kernelValue (p1_18 x y) (d5 x y) a_p1_18 a_d5 conjugate_p1_18 conjugate_d5 m
private def a_p1_20 (m : ℕ) : ℕ := a_d31 (a_p1_19 m)
private theorem conjugate_p1_20 (m : ℕ) :
    (p1_20 x y)⁻¹ * kernelValue m * (p1_20 x y) = kernelValue (a_p1_20 m) :=
  conjugate_product kernelValue (p1_19 x y) (d31 x y) a_p1_19 a_d31 conjugate_p1_19 conjugate_d31 m
private def a_p1_21 (m : ℕ) : ℕ := a_d3 (a_p1_20 m)
private theorem conjugate_p1_21 (m : ℕ) :
    (p1_21 x y)⁻¹ * kernelValue m * (p1_21 x y) = kernelValue (a_p1_21 m) :=
  conjugate_product kernelValue (p1_20 x y) (d3 x y) a_p1_20 a_d3 conjugate_p1_20 conjugate_d3 m
private def a_p1_22 (m : ℕ) : ℕ := a_d25 (a_p1_21 m)
private theorem conjugate_p1_22 (m : ℕ) :
    (p1_22 x y)⁻¹ * kernelValue m * (p1_22 x y) = kernelValue (a_p1_22 m) :=
  conjugate_product kernelValue (p1_21 x y) (d25 x y) a_p1_21 a_d25 conjugate_p1_21 conjugate_d25 m
private def a_p1_23 (m : ℕ) : ℕ := a_d9 (a_p1_22 m)
private theorem conjugate_p1_23 (m : ℕ) :
    (p1_23 x y)⁻¹ * kernelValue m * (p1_23 x y) = kernelValue (a_p1_23 m) :=
  conjugate_product kernelValue (p1_22 x y) (d9 x y) a_p1_22 a_d9 conjugate_p1_22 conjugate_d9 m
private def a_p1_24 (m : ℕ) : ℕ := a_d42 (a_p1_23 m)
private theorem conjugate_p1_24 (m : ℕ) :
    (p1_24 x y)⁻¹ * kernelValue m * (p1_24 x y) = kernelValue (a_p1_24 m) :=
  conjugate_product kernelValue (p1_23 x y) (d42 x y) a_p1_23 a_d42 conjugate_p1_23 conjugate_d42 m
private def a_p1_25 (m : ℕ) : ℕ := a_d20 (a_p1_24 m)
private theorem conjugate_p1_25 (m : ℕ) :
    (p1_25 x y)⁻¹ * kernelValue m * (p1_25 x y) = kernelValue (a_p1_25 m) :=
  conjugate_product kernelValue (p1_24 x y) (d20 x y) a_p1_24 a_d20 conjugate_p1_24 conjugate_d20 m
private def a_p1_26 (m : ℕ) : ℕ := a_d13 (a_p1_25 m)
private theorem conjugate_p1_26 (m : ℕ) :
    (p1_26 x y)⁻¹ * kernelValue m * (p1_26 x y) = kernelValue (a_p1_26 m) :=
  conjugate_product kernelValue (p1_25 x y) (d13 x y) a_p1_25 a_d13 conjugate_p1_25 conjugate_d13 m
private def a_p1_27 (m : ℕ) : ℕ := a_d5 (a_p1_26 m)
private theorem conjugate_p1_27 (m : ℕ) :
    (p1_27 x y)⁻¹ * kernelValue m * (p1_27 x y) = kernelValue (a_p1_27 m) :=
  conjugate_product kernelValue (p1_26 x y) (d5 x y) a_p1_26 a_d5 conjugate_p1_26 conjugate_d5 m
private def a_p1_28 (m : ℕ) : ℕ := ay (a_p1_27 m)
private theorem conjugate_p1_28 (m : ℕ) :
    (p1_28 x y)⁻¹ * kernelValue m * (p1_28 x y) = kernelValue (a_p1_28 m) :=
  conjugate_product kernelValue (p1_27 x y) y a_p1_27 ay conjugate_p1_27 conjugate_y m
private def a_p1_29 (m : ℕ) : ℕ := a_d7 (a_p1_28 m)
private theorem conjugate_p1_29 (m : ℕ) :
    (p1_29 x y)⁻¹ * kernelValue m * (p1_29 x y) = kernelValue (a_p1_29 m) :=
  conjugate_product kernelValue (p1_28 x y) (d7 x y) a_p1_28 a_d7 conjugate_p1_28 conjugate_d7 m
private def a_p1_30 (m : ℕ) : ℕ := a_d4 (a_p1_29 m)
private theorem conjugate_p1_30 (m : ℕ) :
    (p1_30 x y)⁻¹ * kernelValue m * (p1_30 x y) = kernelValue (a_p1_30 m) :=
  conjugate_product kernelValue (p1_29 x y) (d4 x y) a_p1_29 a_d4 conjugate_p1_29 conjugate_d4 m
private def a_p1_31 (m : ℕ) : ℕ := a_d4 (a_p1_30 m)
private theorem conjugate_p1_31 (m : ℕ) :
    (p1_31 x y)⁻¹ * kernelValue m * (p1_31 x y) = kernelValue (a_p1_31 m) :=
  conjugate_product kernelValue (p1_30 x y) (d4 x y) a_p1_30 a_d4 conjugate_p1_30 conjugate_d4 m
private def a_p1_32 (m : ℕ) : ℕ := a_d43 (a_p1_31 m)
private theorem conjugate_p1_32 (m : ℕ) :
    (p1_32 x y)⁻¹ * kernelValue m * (p1_32 x y) = kernelValue (a_p1_32 m) :=
  conjugate_product kernelValue (p1_31 x y) (d43 x y) a_p1_31 a_d43 conjugate_p1_31 conjugate_d43 m
private def a_p1_33 (m : ℕ) : ℕ := a_d15 (a_p1_32 m)
private theorem conjugate_p1_33 (m : ℕ) :
    (p1_33 x y)⁻¹ * kernelValue m * (p1_33 x y) = kernelValue (a_p1_33 m) :=
  conjugate_product kernelValue (p1_32 x y) (d15 x y) a_p1_32 a_d15 conjugate_p1_32 conjugate_d15 m
private def a_p1_34 (m : ℕ) : ℕ := a_d20 (a_p1_33 m)
private theorem conjugate_p1_34 (m : ℕ) :
    (p1_34 x y)⁻¹ * kernelValue m * (p1_34 x y) = kernelValue (a_p1_34 m) :=
  conjugate_product kernelValue (p1_33 x y) (d20 x y) a_p1_33 a_d20 conjugate_p1_33 conjugate_d20 m
private def a_p1_35 (m : ℕ) : ℕ := a_d17 (a_p1_34 m)
private theorem conjugate_p1_35 (m : ℕ) :
    (p1_35 x y)⁻¹ * kernelValue m * (p1_35 x y) = kernelValue (a_p1_35 m) :=
  conjugate_product kernelValue (p1_34 x y) (d17 x y) a_p1_34 a_d17 conjugate_p1_34 conjugate_d17 m
private def a_p2_0 (m : ℕ) : ℕ := a_d6 (a_d8 m)
private theorem conjugate_p2_0 (m : ℕ) :
    (p2_0 x y)⁻¹ * kernelValue m * (p2_0 x y) = kernelValue (a_p2_0 m) :=
  conjugate_product kernelValue (d8 x y) (d6 x y) a_d8 a_d6 conjugate_d8 conjugate_d6 m
private def a_p2_1 (m : ℕ) : ℕ := a_d42 (a_p2_0 m)
private theorem conjugate_p2_1 (m : ℕ) :
    (p2_1 x y)⁻¹ * kernelValue m * (p2_1 x y) = kernelValue (a_p2_1 m) :=
  conjugate_product kernelValue (p2_0 x y) (d42 x y) a_p2_0 a_d42 conjugate_p2_0 conjugate_d42 m
private def a_p2_2 (m : ℕ) : ℕ := a_d8 (a_p2_1 m)
private theorem conjugate_p2_2 (m : ℕ) :
    (p2_2 x y)⁻¹ * kernelValue m * (p2_2 x y) = kernelValue (a_p2_2 m) :=
  conjugate_product kernelValue (p2_1 x y) (d8 x y) a_p2_1 a_d8 conjugate_p2_1 conjugate_d8 m
private def a_p2_3 (m : ℕ) : ℕ := a_d7 (a_p2_2 m)
private theorem conjugate_p2_3 (m : ℕ) :
    (p2_3 x y)⁻¹ * kernelValue m * (p2_3 x y) = kernelValue (a_p2_3 m) :=
  conjugate_product kernelValue (p2_2 x y) (d7 x y) a_p2_2 a_d7 conjugate_p2_2 conjugate_d7 m
private def a_p2_4 (m : ℕ) : ℕ := a_d44 (a_p2_3 m)
private theorem conjugate_p2_4 (m : ℕ) :
    (p2_4 x y)⁻¹ * kernelValue m * (p2_4 x y) = kernelValue (a_p2_4 m) :=
  conjugate_product kernelValue (p2_3 x y) (d44 x y) a_p2_3 a_d44 conjugate_p2_3 conjugate_d44 m
private def a_p2_5 (m : ℕ) : ℕ := a_d3 (a_p2_4 m)
private theorem conjugate_p2_5 (m : ℕ) :
    (p2_5 x y)⁻¹ * kernelValue m * (p2_5 x y) = kernelValue (a_p2_5 m) :=
  conjugate_product kernelValue (p2_4 x y) (d3 x y) a_p2_4 a_d3 conjugate_p2_4 conjugate_d3 m
private def a_p2_6 (m : ℕ) : ℕ := a_d30 (a_p2_5 m)
private theorem conjugate_p2_6 (m : ℕ) :
    (p2_6 x y)⁻¹ * kernelValue m * (p2_6 x y) = kernelValue (a_p2_6 m) :=
  conjugate_product kernelValue (p2_5 x y) (d30 x y) a_p2_5 a_d30 conjugate_p2_5 conjugate_d30 m
private def a_p2_7 (m : ℕ) : ℕ := a_d22 (a_p2_6 m)
private theorem conjugate_p2_7 (m : ℕ) :
    (p2_7 x y)⁻¹ * kernelValue m * (p2_7 x y) = kernelValue (a_p2_7 m) :=
  conjugate_product kernelValue (p2_6 x y) (d22 x y) a_p2_6 a_d22 conjugate_p2_6 conjugate_d22 m
private def a_p2_8 (m : ℕ) : ℕ := a_d45 (a_p2_7 m)
private theorem conjugate_p2_8 (m : ℕ) :
    (p2_8 x y)⁻¹ * kernelValue m * (p2_8 x y) = kernelValue (a_p2_8 m) :=
  conjugate_product kernelValue (p2_7 x y) (d45 x y) a_p2_7 a_d45 conjugate_p2_7 conjugate_d45 m
private def a_p2_9 (m : ℕ) : ℕ := a_d7 (a_p2_8 m)
private theorem conjugate_p2_9 (m : ℕ) :
    (p2_9 x y)⁻¹ * kernelValue m * (p2_9 x y) = kernelValue (a_p2_9 m) :=
  conjugate_product kernelValue (p2_8 x y) (d7 x y) a_p2_8 a_d7 conjugate_p2_8 conjugate_d7 m
private def a_p2_10 (m : ℕ) : ℕ := a_d24 (a_p2_9 m)
private theorem conjugate_p2_10 (m : ℕ) :
    (p2_10 x y)⁻¹ * kernelValue m * (p2_10 x y) = kernelValue (a_p2_10 m) :=
  conjugate_product kernelValue (p2_9 x y) (d24 x y) a_p2_9 a_d24 conjugate_p2_9 conjugate_d24 m
private def a_p2_11 (m : ℕ) : ℕ := a_d9 (a_p2_10 m)
private theorem conjugate_p2_11 (m : ℕ) :
    (p2_11 x y)⁻¹ * kernelValue m * (p2_11 x y) = kernelValue (a_p2_11 m) :=
  conjugate_product kernelValue (p2_10 x y) (d9 x y) a_p2_10 a_d9 conjugate_p2_10 conjugate_d9 m
private def a_p2_12 (m : ℕ) : ℕ := a_d9 (a_p2_11 m)
private theorem conjugate_p2_12 (m : ℕ) :
    (p2_12 x y)⁻¹ * kernelValue m * (p2_12 x y) = kernelValue (a_p2_12 m) :=
  conjugate_product kernelValue (p2_11 x y) (d9 x y) a_p2_11 a_d9 conjugate_p2_11 conjugate_d9 m
private def a_p2_13 (m : ℕ) : ℕ := a_d9 (a_p2_12 m)
private theorem conjugate_p2_13 (m : ℕ) :
    (p2_13 x y)⁻¹ * kernelValue m * (p2_13 x y) = kernelValue (a_p2_13 m) :=
  conjugate_product kernelValue (p2_12 x y) (d9 x y) a_p2_12 a_d9 conjugate_p2_12 conjugate_d9 m
private def a_p2_14 (m : ℕ) : ℕ := aiy (a_p2_13 m)
private theorem conjugate_p2_14 (m : ℕ) :
    (p2_14 x y)⁻¹ * kernelValue m * (p2_14 x y) = kernelValue (a_p2_14 m) :=
  conjugate_product kernelValue (p2_13 x y) y⁻¹ a_p2_13 aiy conjugate_p2_13 conjugate_iy m
private def a_p2_15 (m : ℕ) : ℕ := a_d17 (a_p2_14 m)
private theorem conjugate_p2_15 (m : ℕ) :
    (p2_15 x y)⁻¹ * kernelValue m * (p2_15 x y) = kernelValue (a_p2_15 m) :=
  conjugate_product kernelValue (p2_14 x y) (d17 x y) a_p2_14 a_d17 conjugate_p2_14 conjugate_d17 m
private def a_p2_16 (m : ℕ) : ℕ := a_d20 (a_p2_15 m)
private theorem conjugate_p2_16 (m : ℕ) :
    (p2_16 x y)⁻¹ * kernelValue m * (p2_16 x y) = kernelValue (a_p2_16 m) :=
  conjugate_product kernelValue (p2_15 x y) (d20 x y) a_p2_15 a_d20 conjugate_p2_15 conjugate_d20 m
private def a_p2_17 (m : ℕ) : ℕ := a_d38 (a_p2_16 m)
private theorem conjugate_p2_17 (m : ℕ) :
    (p2_17 x y)⁻¹ * kernelValue m * (p2_17 x y) = kernelValue (a_p2_17 m) :=
  conjugate_product kernelValue (p2_16 x y) (d38 x y) a_p2_16 a_d38 conjugate_p2_16 conjugate_d38 m
private def a_p2_18 (m : ℕ) : ℕ := a_d12 (a_p2_17 m)
private theorem conjugate_p2_18 (m : ℕ) :
    (p2_18 x y)⁻¹ * kernelValue m * (p2_18 x y) = kernelValue (a_p2_18 m) :=
  conjugate_product kernelValue (p2_17 x y) (d12 x y) a_p2_17 a_d12 conjugate_p2_17 conjugate_d12 m
private def a_p2_19 (m : ℕ) : ℕ := a_d9 (a_p2_18 m)
private theorem conjugate_p2_19 (m : ℕ) :
    (p2_19 x y)⁻¹ * kernelValue m * (p2_19 x y) = kernelValue (a_p2_19 m) :=
  conjugate_product kernelValue (p2_18 x y) (d9 x y) a_p2_18 a_d9 conjugate_p2_18 conjugate_d9 m
private def a_p2_20 (m : ℕ) : ℕ := a_d28 (a_p2_19 m)
private theorem conjugate_p2_20 (m : ℕ) :
    (p2_20 x y)⁻¹ * kernelValue m * (p2_20 x y) = kernelValue (a_p2_20 m) :=
  conjugate_product kernelValue (p2_19 x y) (d28 x y) a_p2_19 a_d28 conjugate_p2_19 conjugate_d28 m
private def a_p2_21 (m : ℕ) : ℕ := a_d6 (a_p2_20 m)
private theorem conjugate_p2_21 (m : ℕ) :
    (p2_21 x y)⁻¹ * kernelValue m * (p2_21 x y) = kernelValue (a_p2_21 m) :=
  conjugate_product kernelValue (p2_20 x y) (d6 x y) a_p2_20 a_d6 conjugate_p2_20 conjugate_d6 m
private def a_p2_22 (m : ℕ) : ℕ := a_d15 (a_p2_21 m)
private theorem conjugate_p2_22 (m : ℕ) :
    (p2_22 x y)⁻¹ * kernelValue m * (p2_22 x y) = kernelValue (a_p2_22 m) :=
  conjugate_product kernelValue (p2_21 x y) (d15 x y) a_p2_21 a_d15 conjugate_p2_21 conjugate_d15 m
private def a_p2_23 (m : ℕ) : ℕ := a_d43 (a_p2_22 m)
private theorem conjugate_p2_23 (m : ℕ) :
    (p2_23 x y)⁻¹ * kernelValue m * (p2_23 x y) = kernelValue (a_p2_23 m) :=
  conjugate_product kernelValue (p2_22 x y) (d43 x y) a_p2_22 a_d43 conjugate_p2_22 conjugate_d43 m
private def a_p3_0 (m : ℕ) : ℕ := a_d11 (aiy m)
private theorem conjugate_p3_0 (m : ℕ) :
    (p3_0 x y)⁻¹ * kernelValue m * (p3_0 x y) = kernelValue (a_p3_0 m) :=
  conjugate_product kernelValue y⁻¹ (d11 x y) aiy a_d11 conjugate_iy conjugate_d11 m
private def a_p3_1 (m : ℕ) : ℕ := a_d18 (a_p3_0 m)
private theorem conjugate_p3_1 (m : ℕ) :
    (p3_1 x y)⁻¹ * kernelValue m * (p3_1 x y) = kernelValue (a_p3_1 m) :=
  conjugate_product kernelValue (p3_0 x y) (d18 x y) a_p3_0 a_d18 conjugate_p3_0 conjugate_d18 m
private def a_p3_2 (m : ℕ) : ℕ := a_d6 (a_p3_1 m)
private theorem conjugate_p3_2 (m : ℕ) :
    (p3_2 x y)⁻¹ * kernelValue m * (p3_2 x y) = kernelValue (a_p3_2 m) :=
  conjugate_product kernelValue (p3_1 x y) (d6 x y) a_p3_1 a_d6 conjugate_p3_1 conjugate_d6 m
private def a_p3_3 (m : ℕ) : ℕ := a_d11 (a_p3_2 m)
private theorem conjugate_p3_3 (m : ℕ) :
    (p3_3 x y)⁻¹ * kernelValue m * (p3_3 x y) = kernelValue (a_p3_3 m) :=
  conjugate_product kernelValue (p3_2 x y) (d11 x y) a_p3_2 a_d11 conjugate_p3_2 conjugate_d11 m
private def a_p3_4 (m : ℕ) : ℕ := a_d11 (a_p3_3 m)
private theorem conjugate_p3_4 (m : ℕ) :
    (p3_4 x y)⁻¹ * kernelValue m * (p3_4 x y) = kernelValue (a_p3_4 m) :=
  conjugate_product kernelValue (p3_3 x y) (d11 x y) a_p3_3 a_d11 conjugate_p3_3 conjugate_d11 m
private def a_p3_5 (m : ℕ) : ℕ := a_d10 (a_p3_4 m)
private theorem conjugate_p3_5 (m : ℕ) :
    (p3_5 x y)⁻¹ * kernelValue m * (p3_5 x y) = kernelValue (a_p3_5 m) :=
  conjugate_product kernelValue (p3_4 x y) (d10 x y) a_p3_4 a_d10 conjugate_p3_4 conjugate_d10 m
private def a_p3_6 (m : ℕ) : ℕ := a_d18 (a_p3_5 m)
private theorem conjugate_p3_6 (m : ℕ) :
    (p3_6 x y)⁻¹ * kernelValue m * (p3_6 x y) = kernelValue (a_p3_6 m) :=
  conjugate_product kernelValue (p3_5 x y) (d18 x y) a_p3_5 a_d18 conjugate_p3_5 conjugate_d18 m
private def a_p3_7 (m : ℕ) : ℕ := a_d44 (a_p3_6 m)
private theorem conjugate_p3_7 (m : ℕ) :
    (p3_7 x y)⁻¹ * kernelValue m * (p3_7 x y) = kernelValue (a_p3_7 m) :=
  conjugate_product kernelValue (p3_6 x y) (d44 x y) a_p3_6 a_d44 conjugate_p3_6 conjugate_d44 m
private def a_p3_8 (m : ℕ) : ℕ := a_d40 (a_p3_7 m)
private theorem conjugate_p3_8 (m : ℕ) :
    (p3_8 x y)⁻¹ * kernelValue m * (p3_8 x y) = kernelValue (a_p3_8 m) :=
  conjugate_product kernelValue (p3_7 x y) (d40 x y) a_p3_7 a_d40 conjugate_p3_7 conjugate_d40 m
private def a_p3_9 (m : ℕ) : ℕ := a_d45 (a_p3_8 m)
private theorem conjugate_p3_9 (m : ℕ) :
    (p3_9 x y)⁻¹ * kernelValue m * (p3_9 x y) = kernelValue (a_p3_9 m) :=
  conjugate_product kernelValue (p3_8 x y) (d45 x y) a_p3_8 a_d45 conjugate_p3_8 conjugate_d45 m
private def a_p3_10 (m : ℕ) : ℕ := a_d39 (a_p3_9 m)
private theorem conjugate_p3_10 (m : ℕ) :
    (p3_10 x y)⁻¹ * kernelValue m * (p3_10 x y) = kernelValue (a_p3_10 m) :=
  conjugate_product kernelValue (p3_9 x y) (d39 x y) a_p3_9 a_d39 conjugate_p3_9 conjugate_d39 m
private def a_p3_11 (m : ℕ) : ℕ := a_d41 (a_p3_10 m)
private theorem conjugate_p3_11 (m : ℕ) :
    (p3_11 x y)⁻¹ * kernelValue m * (p3_11 x y) = kernelValue (a_p3_11 m) :=
  conjugate_product kernelValue (p3_10 x y) (d41 x y) a_p3_10 a_d41 conjugate_p3_10 conjugate_d41 m
private def a_p3_12 (m : ℕ) : ℕ := a_d4 (a_p3_11 m)
private theorem conjugate_p3_12 (m : ℕ) :
    (p3_12 x y)⁻¹ * kernelValue m * (p3_12 x y) = kernelValue (a_p3_12 m) :=
  conjugate_product kernelValue (p3_11 x y) (d4 x y) a_p3_11 a_d4 conjugate_p3_11 conjugate_d4 m
private def a_p3_13 (m : ℕ) : ℕ := a_d15 (a_p3_12 m)
private theorem conjugate_p3_13 (m : ℕ) :
    (p3_13 x y)⁻¹ * kernelValue m * (p3_13 x y) = kernelValue (a_p3_13 m) :=
  conjugate_product kernelValue (p3_12 x y) (d15 x y) a_p3_12 a_d15 conjugate_p3_12 conjugate_d15 m
private def a_p3_14 (m : ℕ) : ℕ := a_d8 (a_p3_13 m)
private theorem conjugate_p3_14 (m : ℕ) :
    (p3_14 x y)⁻¹ * kernelValue m * (p3_14 x y) = kernelValue (a_p3_14 m) :=
  conjugate_product kernelValue (p3_13 x y) (d8 x y) a_p3_13 a_d8 conjugate_p3_13 conjugate_d8 m
private def a_p3_15 (m : ℕ) : ℕ := a_d9 (a_p3_14 m)
private theorem conjugate_p3_15 (m : ℕ) :
    (p3_15 x y)⁻¹ * kernelValue m * (p3_15 x y) = kernelValue (a_p3_15 m) :=
  conjugate_product kernelValue (p3_14 x y) (d9 x y) a_p3_14 a_d9 conjugate_p3_14 conjugate_d9 m
private def a_p3_16 (m : ℕ) : ℕ := a_d20 (a_p3_15 m)
private theorem conjugate_p3_16 (m : ℕ) :
    (p3_16 x y)⁻¹ * kernelValue m * (p3_16 x y) = kernelValue (a_p3_16 m) :=
  conjugate_product kernelValue (p3_15 x y) (d20 x y) a_p3_15 a_d20 conjugate_p3_15 conjugate_d20 m
private def a_p3_17 (m : ℕ) : ℕ := a_d28 (a_p3_16 m)
private theorem conjugate_p3_17 (m : ℕ) :
    (p3_17 x y)⁻¹ * kernelValue m * (p3_17 x y) = kernelValue (a_p3_17 m) :=
  conjugate_product kernelValue (p3_16 x y) (d28 x y) a_p3_16 a_d28 conjugate_p3_16 conjugate_d28 m
private def a_p3_18 (m : ℕ) : ℕ := a_d17 (a_p3_17 m)
private theorem conjugate_p3_18 (m : ℕ) :
    (p3_18 x y)⁻¹ * kernelValue m * (p3_18 x y) = kernelValue (a_p3_18 m) :=
  conjugate_product kernelValue (p3_17 x y) (d17 x y) a_p3_17 a_d17 conjugate_p3_17 conjugate_d17 m
private def a_p3_19 (m : ℕ) : ℕ := a_d22 (a_p3_18 m)
private theorem conjugate_p3_19 (m : ℕ) :
    (p3_19 x y)⁻¹ * kernelValue m * (p3_19 x y) = kernelValue (a_p3_19 m) :=
  conjugate_product kernelValue (p3_18 x y) (d22 x y) a_p3_18 a_d22 conjugate_p3_18 conjugate_d22 m
private def a_p3_20 (m : ℕ) : ℕ := a_d29 (a_p3_19 m)
private theorem conjugate_p3_20 (m : ℕ) :
    (p3_20 x y)⁻¹ * kernelValue m * (p3_20 x y) = kernelValue (a_p3_20 m) :=
  conjugate_product kernelValue (p3_19 x y) (d29 x y) a_p3_19 a_d29 conjugate_p3_19 conjugate_d29 m
private def a_p3_21 (m : ℕ) : ℕ := a_d37 (a_p3_20 m)
private theorem conjugate_p3_21 (m : ℕ) :
    (p3_21 x y)⁻¹ * kernelValue m * (p3_21 x y) = kernelValue (a_p3_21 m) :=
  conjugate_product kernelValue (p3_20 x y) (d37 x y) a_p3_20 a_d37 conjugate_p3_20 conjugate_d37 m
private def liftAction : Fin 4 → ℕ → ℕ := ![a_p0_22, a_p1_35, a_p2_23, a_p3_21]
private theorem conjugate_liftWord (i : Fin 4) (m : ℕ) :
    (NativeWords.lifts x y i)⁻¹ * kernelValue m * (NativeWords.lifts x y i) =
      kernelValue (liftAction i m) := by
  fin_cases i
  · exact conjugate_p0_22 m
  · exact conjugate_p1_35 m
  · exact conjugate_p2_23 m
  · exact conjugate_p3_21 m
private theorem liftAction_fixes :
    ∀ (i : Fin 4) (j : Fin 6), liftAction i (kernelMasks j) = kernelMasks j := by
  decide +kernel

theorem kernelGenerator_commute_lift (j : Fin 6) (i : Fin 4) :
    Commute (kernelGenerator j) (lift i) := by
  have hc : Commute (kernelGenerator j) (NativeWords.lifts x y i) := by
    have h := conjugate_liftWord i (kernelMasks j)
    rw [liftAction_fixes] at h
    change Commute (kernelValue (kernelMasks j)) (NativeWords.lifts x y i)
    change kernelValue (kernelMasks j) * NativeWords.lifts x y i =
      NativeWords.lifts x y i * kernelValue (kernelMasks j)
    calc
      _ = NativeWords.lifts x y i *
          ((NativeWords.lifts x y i)⁻¹ * kernelValue (kernelMasks j) *
            NativeWords.lifts x y i) := by group
      _ = _ := by rw [h]
  exact hc.mul_right (kernelValue_commute (kernelMasks j) (correctionMasks i))


/-- The right-conjugation matrices of the four native lifts on the actual
 eleven-dimensional kernel, with column masks in the existing kernel basis. -/
@[expose] def liftKernelMasks : Fin 4 → Fin 11 → ℕ :=
  ![![55, 1625, 50, 1686, 89, 1540, 1768, 1576, 2017, 1133, 1151],
    ![313, 1253, 1838, 926, 1271, 280, 750, 1084, 1865, 2015, 479],
    ![1570, 2, 124, 1173, 1271, 740, 766, 1125, 1881, 1059, 1732],
    ![180, 1183, 116, 1173, 1020, 2020, 1128, 1133, 1732, 1576, 1881]]

private theorem liftAction_on_basis : ∀ (i : Fin 4) (j : Fin 11),
    liftAction i (2^j.val) = liftKernelMasks i j := by decide +kernel

private theorem conjugate_lift (i : Fin 4) (m : ℕ) :
    (lift i)⁻¹ * kernelValue m * lift i = kernelValue (liftAction i m) := by
  calc
    _ = (kernelValue (correctionMasks i))⁻¹ *
        ((NativeWords.lifts x y i)⁻¹ * kernelValue m * NativeWords.lifts x y i) *
        kernelValue (correctionMasks i) := by unfold lift; group
    _ = (kernelValue (correctionMasks i))⁻¹ * kernelValue (liftAction i m) *
        kernelValue (correctionMasks i) := by rw [conjugate_liftWord]
    _ = _ := by
      rw [mul_assoc, ← (kernelValue_commute (correctionMasks i) (liftAction i m)).eq,
        inv_mul_cancel_left]

/-- Literal right conjugation by each corrected native lift, for every kernel mask. -/
theorem lift_conjugates_kernel (i : Fin 4) (m : ℕ) :
    (lift i)⁻¹ * kernelValue m * lift i = kernelValue (maskImage (liftKernelMasks i) m) := by
  have hb (j : Fin 11) :
      (lift i)⁻¹ * basis matrixA_mul_self matrixB_pow_four j * lift i =
        kernelValue (liftKernelMasks i j) := by
    rw [← maskValue_basis matrixA_mul_self matrixB_pow_four j, conjugate_lift,
      liftAction_on_basis]
  rw [show kernelValue (maskImage (liftKernelMasks i) m) = _ from
    maskValue_maskImage matrixA_mul_self matrixB_pow_four (liftKernelMasks i) m]
  have h := map_binaryProduct (MulAut.conj (lift i)⁻¹).toMonoidHom
    (basis matrixA_mul_self matrixB_pow_four) (fun j => m.testBit j.val)
  change (lift i)⁻¹ * binaryProduct _ _ * ((lift i)⁻¹)⁻¹ =
    binaryProduct (fun j => (lift i)⁻¹ * basis matrixA_mul_self matrixB_pow_four j *
      ((lift i)⁻¹)⁻¹) (fun j => m.testBit j.val) at h
  simpa only [inv_inv, hb, kernelValue, maskValue, coordinates_val] using h

end Janko4.LocalStructure.LinearFive
