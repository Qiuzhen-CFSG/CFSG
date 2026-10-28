module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.WordCertificates.Arithmetic12
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Presentation

/-!
# Checked binary E8 root words

The matrices use 8 Cartan coordinates followed by the 240 roots in the
source coordinate order. The eight generators are folded signed roots
at nodes 3, 2, {1,4}, {0,5}, in this order. Packed row products are verified
by Lean's kernel using `Thompson.BinaryMatrix.decode_mul`.

The source Levi producer compares these tables with the literal integral
Chevalley root operators. The seven words are the full ATLAS S62G1-P1.M
presentation; the source application is Aschbacher–Smith A.2.18, p.40.
-/

@[expose] public section
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.WordCertificates
open Checked
open Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover

private theorem generator_square (i : Fin 8) :
    Thompson.BinaryMatrix.decode 248 (generatorRows i) *
      Thompson.BinaryMatrix.decode 248 (generatorRows i) = 1 := by
  fin_cases i
  · exact Checked.product0
  · exact Checked.product1
  · exact Checked.product2
  · exact Checked.product3
  · exact Checked.product4
  · exact Checked.product5
  · exact Checked.product6
  · exact Checked.product7

/-- The eight actual units, each certified to be an involution. -/
def generator (i : Fin 8) : Matˣ where
  val := Thompson.BinaryMatrix.decode 248 (generatorRows i)
  inv := Thompson.BinaryMatrix.decode 248 (generatorRows i)
  val_inv := by exact generator_square i
  inv_val := by exact generator_square i

theorem generator_val (i : Fin 8) : (generator i).val =
    Thompson.BinaryMatrix.decode 248 (generatorRows i) := rfl

theorem generator_inv_val (i : Fin 8) : ((generator i)⁻¹).val =
    Thompson.BinaryMatrix.decode 248 (generatorRows i) := rfl

/-- The marked second Atlas generator in the selected C₃ root generators. -/
def bWord : List (Fin 8) := [6, 4, 2, 7, 5, 3, 4, 5, 6, 7, 3, 4, 2, 3, 5, 4, 3, 2, 3]

/-- The simple Weyl word carrying the first root to the highest root. -/
def wWord : List (Fin 8) := [0, 1, 0, 2, 3, 2, 4, 5, 4, 6, 7, 6, 2, 3, 2, 4, 5, 4, 2, 3, 2]

def a : Matˣ := generator 2
def b : Matˣ := (bWord.map generator).prod
def w : Matˣ := (wWord.map generator).prod
def z : Matˣ := w * generator 0 * w⁻¹

private theorem a_val : a.val = Thompson.BinaryMatrix.decode 248 (generatorRows 2) := rfl
private theorem a_inv_val : (a⁻¹).val = Thompson.BinaryMatrix.decode 248 (generatorRows 2) := rfl

private theorem b_val : b.val = Thompson.BinaryMatrix.decode 248 rows17 := by
  simp only [b, bWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Units.val_mul,
    generator_val, product8, product9, product10, product11, product12, product13, product14, product15, product16,
    product17, product18, product19, product20, product21, product22, product23, product24, product25]

private theorem w_val : w.val = Thompson.BinaryMatrix.decode 248 rows34 := by
  simp only [w, wWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Units.val_mul,
    generator_val, product26, product27, product10, product11, product30, product31, product32, product33, product34,
    product35, product36, product37, product38, product39, product40, product41, product42, product43, product44,
    product45]

private theorem inv_val_of_product (u : Matˣ) (r : Mat) (h : u.val * r = 1) :
    (u⁻¹).val = r := by
  calc
    (u⁻¹).val = (u⁻¹).val * 1 := (mul_one _).symm
    _ = (u⁻¹).val * (u.val * r) := congrArg ((u⁻¹).val * ·) h.symm
    _ = r := by
      change u.inv * (u.val * r) = r
      rw [← mul_assoc, u.inv_val, one_mul]

private theorem b_inv_val : (b⁻¹).val = Thompson.BinaryMatrix.decode 248 rows35 := by
  apply inv_val_of_product
  rw [b_val]
  exact Checked.product46

private theorem w_inv_val : (w⁻¹).val = Thompson.BinaryMatrix.decode 248 rows36 := by
  apply inv_val_of_product
  rw [w_val]
  exact Checked.product47

private theorem z_val : z.val = Thompson.BinaryMatrix.decode 248 rows38 := by
  simp only [z, Units.val_mul, w_val, generator_val, product48, w_inv_val, product49]

private def c : Matˣ := b * a * b * a * b

private theorem c_val : c.val = Thompson.BinaryMatrix.decode 248 rows42 := by
  simp only [c, Units.val_mul, b_val, a_val, product50, product51, product52, product53]

private theorem c_inv_val : (c⁻¹).val = Thompson.BinaryMatrix.decode 248 rows43 := by
  apply inv_val_of_product
  rw [c_val]
  exact Checked.product54

/-- All seven sourced relations hold in the literal binary matrix units. -/
theorem relators (i : Fin 7) : KernelPresentation.word a b i = 1 := by
  fin_cases i
  · change a ^ 2 = 1
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, a_val, product2, Units.val_one]
  · change b ^ 7 = 1
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, b_val, product55, product59, product60, product61,
    product62, product63, Units.val_one]
  · change (a * b) ^ 9 = 1
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, a_val, b_val, product64, product65, product66,
    product67, product68, product69, product70, product71, product72, Units.val_one]
  · change (a * b ^ 2) ^ 12 = 1
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, a_val, b_val, product55, product73, product74,
    product75, product76, product77, product78, product79, product80, product81, product82, product83, product84,
    Units.val_one]
  · change KernelPresentation.sourceCommutator a c ^ 2 = 1
    apply Units.ext
    simp only [KernelPresentation.sourceCommutator, pow_succ, pow_zero, one_mul, Units.val_mul, a_inv_val, c_inv_val, product85, a_val, product86, c_val, product87, product88, Units.val_one]
  · change KernelPresentation.sourceCommutator a b ^ 3 = 1
    apply Units.ext
    simp only [KernelPresentation.sourceCommutator, pow_succ, pow_zero, one_mul, Units.val_mul, a_inv_val,
    b_inv_val, product89, a_val, product90, b_val, product91, product92, product93, Units.val_one]
  · change KernelPresentation.sourceCommutator a (b ^ 2) ^ 2 = 1
    apply Units.ext
    simp only [KernelPresentation.sourceCommutator, pow_succ, pow_zero, one_mul, mul_inv_rev, Units.val_mul, a_inv_val, b_inv_val, product56, product94, a_val, product95, b_val, product55, product96, product97, Units.val_one]

/-- The marked generator centralizes the specified highest-root involution. -/
theorem commute_a_z : Commute a z := by
  change a * z = z * a
  apply Units.ext
  simp only [Units.val_mul, a_val, z_val, product98, product99]

/-- The marked generator centralizes the specified highest-root involution. -/
theorem commute_b_z : Commute b z := by
  change b * z = z * b
  apply Units.ext
  simp only [Units.val_mul, b_val, z_val, product100, product101]

end Theory.SpecificGroups.LieType.SourceLevi.E8.WordCertificates
