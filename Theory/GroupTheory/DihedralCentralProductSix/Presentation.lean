module
public import Theory.GroupTheory.DihedralPresentation
import all Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Marked dihedral maps for hyperbolic involution pairs

This intentional companion to `DihedralPresentation` uses its private normal-form
construction, exposing only the maps and their evaluation specifications. Two
involutions with a central twist of order two give a marked map from D₈.
This is the factor construction for the six-pair central product used in
Aschbacher–Smith 16.1.5(9), p.1172, and GLS3 Table 5.3i.
-/

namespace DihedralCentralProductSix

public noncomputable def involutionMap {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G := rotation z hz

public theorem involutionMap_apply {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1)
    (b : Multiplicative (ZMod 2)) : involutionMap z hz b = z ^ b.toAdd.val := by rfl

@[simp] public theorem involutionMap_generator {G : Type*} [Group G]
    (z : G) (hz : z ^ 2 = 1) : involutionMap z hz (.ofAdd 1) = z :=
  rotation_one z hz

public theorem pair_square {G : Type*} [Group G] (a b z : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ht : a * b = b * a * z) :
    (a * b) ^ 2 = z := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb)
  have hi : b * a = (a * b)⁻¹ := by simp [mul_inv_rev, hai, hbi]
  calc
    (a * b) ^ 2 = (a * b) * (b * a * z) := by rw [pow_two]; exact congrArg ((a * b) * ·) ht
    _ = z := by rw [hi, ← mul_assoc, mul_inv_cancel, one_mul]

public noncomputable def pairMap {G : Type*} [Group G] (a b z : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hz : z ^ 2 = 1)
    (ht : a * b = b * a * z) : DihedralGroup 4 →* G :=
  presentationHom (a * b) a
    (by rw [show 4 = 2 * 2 from rfl, pow_mul, pair_square a b z ha hb ht, hz]) ha
    (by
      have haa : a * a = 1 := by simpa [pow_two] using ha
      have hbb : b * b = 1 := by simpa [pow_two] using hb
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
      have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
      simp only [mul_inv_rev, hai, hbi, ← mul_assoc, haa, one_mul])

variable {G : Type*} [Group G] (a b z : G)
  (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hz : z ^ 2 = 1)
  (ht : a * b = b * a * z)

public theorem pairMap_r (k : ZMod 4) :
    pairMap a b z ha hb hz ht (.r k) = (a * b) ^ k.val := by rfl

public theorem pairMap_sr (k : ZMod 4) :
    pairMap a b z ha hb hz ht (.sr k) = a * (a * b) ^ k.val := by rfl

@[simp] public theorem pairMap_r_one :
    pairMap a b z ha hb hz ht (.r 1) = a * b := by rw [pairMap_r]; exact pow_one _

@[simp] public theorem pairMap_sr_zero :
    pairMap a b z ha hb hz ht (.sr 0) = a := by rw [pairMap_sr]; simp

@[simp] public theorem pairMap_r_two :
    pairMap a b z ha hb hz ht (.r 2) = z := by
  rw [pairMap_r]; exact pair_square a b z ha hb ht

public theorem pairMap_commute (a' b' : G)
    (ha' : a' ^ 2 = 1) (hb' : b' ^ 2 = 1) (ht' : a' * b' = b' * a' * z)
    (haa' : Commute a a') (hab' : Commute a b')
    (hba' : Commute b a') (hbb' : Commute b b')
    (x y : DihedralGroup 4) :
    Commute (pairMap a b z ha hb hz ht x) (pairMap a' b' z ha' hb' hz ht' y) := by
  have hc := (haa'.mul_left hba').mul_right (hab'.mul_left hbb')
  cases x <;> cases y <;> simp only [pairMap_r, pairMap_sr]
  · exact hc.pow_pow _ _
  · exact ((haa'.mul_left hba').pow_left _).mul_right (hc.pow_pow _ _)
  · exact ((haa'.mul_right hab').pow_right _).mul_left (hc.pow_pow _ _)
  · exact (haa'.mul_right ((haa'.mul_right hab').pow_right _)).mul_left
      (((haa'.mul_left hba').pow_left _).mul_right (hc.pow_pow _ _))

end DihedralCentralProductSix
