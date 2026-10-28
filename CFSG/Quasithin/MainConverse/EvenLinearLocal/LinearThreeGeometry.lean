module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.Reduction
public import Theory.SpecificGroups.PSL3.UnipotentFixedSpaceNormalizer
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Local geometry of the even degree-three linear groups

The full point and line parabolics in PSL₃(F) are two-local and have
self-centralizing two-cores. These statements are proved for every finite
field of characteristic two, and hence for the arbitrary field witness in
PSL₃(2^f).

For every positive f with |F| = 2^f, every two-local is conjugate into one
of these parabolics, and every maximal two-local is conjugate to one of
them. The common fixed space of a nontrivial subgroup of UT₃ is a point or
line preserved by its normalizer. The determinant-one change of coordinates
and the projective normalizer lifting discharge the geometric premise of
the accompanying reduction. Thus every maximal two-local has characteristic
two, whether or not it contains an ambient Sylow two-subgroup.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, repeated as
Theorem 0.1.1(1) on printed p.482. These are the local geometry and condition
E for the PSL₃(2^f) case; the odd-prime rank bounds for QT are separate.
-/

public section
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
namespace CFSG.Quasithin.MainConverse.LinearThreeGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The full stabilizer of the standard projective point is two-local. -/
theorem pointParabolic_twoLocal [CharP F 2] : IsTwoLocal (pointParabolic F) :=
  parabolic_twoLocal F true

/-- The full stabilizer of the standard projective line is two-local. -/
theorem lineParabolic_twoLocal [CharP F 2] : IsTwoLocal (lineParabolic F) :=
  parabolic_twoLocal F false

/-- Characteristic two for the full projective point parabolic. -/
theorem pointParabolic_characteristicTwo [CharP F 2] :
    HasCharacteristicTwo (pointParabolic F) :=
  parabolic_characteristicTwo F true

/-- Characteristic two for the full projective line parabolic. -/
theorem lineParabolic_characteristicTwo [CharP F 2] :
    HasCharacteristicTwo (lineParabolic F) :=
  parabolic_characteristicTwo F false

/-- The full-parabolic results retain the arbitrary finite-field witness. -/
theorem parabolics_of_card {f : ℕ} (hF : Nat.card F = 2^f) :
    IsTwoLocal (pointParabolic F) ∧ IsTwoLocal (lineParabolic F) ∧
      HasCharacteristicTwo (pointParabolic F) ∧ HasCharacteristicTwo (lineParabolic F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨pointParabolic_twoLocal F, lineParabolic_twoLocal F,
    pointParabolic_characteristicTwo F, lineParabolic_characteristicTwo F⟩

/-- Every two-local is conjugate into a full point or line parabolic.
The conjugating element belongs to the actual ambient projective group. -/
theorem twoLocal_conjugate_le {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (M : Subgroup PSL(3,F)) (hM : IsTwoLocal M) :
    ∃ (g : PSL(3,F)) (point : Bool),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic F point := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact twoLocal_conjugate_le_of_normalizer_cover F
    (normalizer_unipotent_subgroup_conjugate_le F) hf hF M hM

/-- All maximal two-locals are ambient conjugates of the full geometric
parabolics, with no Sylow-containment hypothesis. In particular this covers
every field witness of PSL₃(2^f) with f > 1. -/
theorem maximalTwoLocal_conjugate {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (M : Subgroup PSL(3,F)) (hM : IsMaximalTwoLocal M) :
    ∃ g : PSL(3,F), M.map (MulAut.conj g).toMonoidHom = pointParabolic F ∨
      M.map (MulAut.conj g).toMonoidHom = lineParabolic F := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact maximalTwoLocal_conjugate_of_normalizer_cover F
    (normalizer_unipotent_subgroup_conjugate_le F) hf hF M hM

/-- The intrinsic two-core of every maximal two-local is self-centralizing. -/
theorem maximalTwoLocal_characteristicTwo {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2^f) (M : Subgroup PSL(3,F)) (hM : IsMaximalTwoLocal M) :
    HasCharacteristicTwo M := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact maximalTwoLocal_characteristicTwo_of_normalizer_cover F
    (normalizer_unipotent_subgroup_conjugate_le F) hf hF M hM

/-- Condition E for the actual PSL₃ carrier over an arbitrary field of order 2^f. -/
theorem evenCharacteristic {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f) :
    IsEvenCharacteristic PSL(3,F) := by
  intro _ M hM _
  exact maximalTwoLocal_characteristicTwo F hf hF M hM

end CFSG.Quasithin.MainConverse.LinearThreeGeometry
