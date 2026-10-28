module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Recognition of the field-four exceptional action

The order of the actual G₂(4) component excludes the other large-field
rows of B.4.2 and determines the field in its surviving G₂ action.
These order comparisons feed the literal omega-center action in the
Sylow MS branch; they assert no MS classification.
Source: Aschbacher--Smith B.4.2; MS93 (3.2)(vii), pp.865--866.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

private theorem triple_mono (a b c : ℕ) {q r : ℕ} (h : q ≤ r) :
    q ^ a * (q ^ b - 1) * (q ^ c - 1) ≤
      r ^ a * (r ^ b - 1) * (r ^ c - 1) := by
  gcongr

private theorem linear_two_mono {q r : ℕ} (h : q ≤ r) :
    q * (q ^ 2 - 1) ≤ r * (r ^ 2 - 1) := by
  gcongr

/-- The SL₂ row cannot have the order of G₂(4). -/
theorem card_sl_two_ne_g2_four (F : Type*) [Field F] [Finite F] :
    Nat.card SL(2,F) ≠ 251596800 := by
  rw [Atlas.card_sl_two]
  intro hc
  by_cases hq : Nat.card F ≤ 631
  · have hb := linear_two_mono hq
    norm_num at hb
    omega
  · have hb := linear_two_mono (show 632 ≤ Nat.card F by omega)
    norm_num at hb
    omega

private theorem card_sl_three (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F

/-- The SL₃ row cannot have the order of G₂(4). -/
theorem card_sl_three_ne_g2_four (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) ≠ 251596800 := by
  rw [card_sl_three]
  intro hc
  by_cases hq : Nat.card F ≤ 11
  · have hb := triple_mono 3 3 2 hq
    norm_num at hb
    omega
  · have hb := triple_mono 3 3 2 (show 12 ≤ Nat.card F by omega)
    norm_num at hb
    omega

/-- The symplectic row cannot have the order of G₂(4). -/
theorem card_sp_ne_g2_four (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ 251596800 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp]
  intro hc
  by_cases hq : Nat.card F ≤ 6
  · have hb := triple_mono 4 2 4 hq
    norm_num at hb
    omega
  · have hb := triple_mono 4 2 4 (show 7 ≤ Nat.card F by omega)
    norm_num at hb
    omega

/-- The order of the actual exceptional group determines its field size. -/
theorem card_eq_four_of_card_g2 (F : Type*) [Field F] [Finite F]
    (hc : Nat.card (Atlas.G2.Model F) = 251596800) :
    Nat.card F = 4 := by
  rw [Atlas.G2.card_Model] at hc
  have hlo : 4 ≤ Nat.card F := by
    by_contra hq
    have hb := triple_mono 6 6 2 (show Nat.card F ≤ 3 by omega)
    norm_num at hb
    omega
  have hhi : Nat.card F ≤ 4 := by
    by_contra hq
    have hb := triple_mono 6 6 2 (show 5 ≤ Nat.card F by omega)
    norm_num at hb
    omega
  omega

/-- The binary field in the surviving G₂ row has degree two. -/
theorem degree_eq_two_of_card_g2 (F : ChapterB.QuasisimpleSource.BinaryField)
    (hc : Nat.card (Atlas.G2.Model F.Carrier) = 251596800) :
    F.degree = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  change 2 ^ F.degree = 2 ^ 2
  rw [← F.card_eq, card_eq_four_of_card_g2 F.Carrier hc]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
