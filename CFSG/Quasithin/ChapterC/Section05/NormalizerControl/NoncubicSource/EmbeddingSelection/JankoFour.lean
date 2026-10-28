module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# The J₄ row contradicts the faithful full-Sylow budget

The certified 2¹¹ subgroup already shows 16 divides the order of J₄.
A full Sylow acting faithfully on the original PSL₂(4) image has order
dividing eight. Sylow divisibility excludes J₄ without its full order
calculation or any representation classification.
Source: Aschbacher–Smith A.3.12(17) in C.5.13, printed pp.48,162–163.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection

/-- A certified elementary subgroup suffices for the Sylow-order obstruction;
the full order of J₄ is not required. -/
theorem sixteen_dvd_jankoFour : 16 ∣ Nat.card Janko4.Model := by
  let K := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hc : Nat.card K = 2048 := Janko4.Cardinality.localKernel_card _ _
  have hd : Nat.card K ∣ Nat.card Janko4.Model :=
    K.card_subgroup_dvd_card.trans (Janko4.Cardinality.max1Subgroup _ _).card_subgroup_dvd_card
  exact (show 16 ∣ 2048 by decide).trans (hc ▸ hd)

theorem not_jankoFour_of_faithful_binary_four_sylow {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (B L : Subgroup G)
    (hB : ClassicalGroup.IsPSL B 2 (2^2))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    ¬ Nonempty (L ≃* Janko4.Model) := by
  rintro ⟨e⟩
  have hd : 2^4 ∣ Nat.card G := by
    have hL : 16 ∣ Nat.card L := by rw [Nat.card_congr e.toEquiv]; exact sixteen_dvd_jankoFour
    exact hL.trans L.card_subgroup_dvd_card
  have hT := T.pow_dvd_card_of_pow_dvd_card hd
  have hb := binary_normalizer_card_dvd T B (by decide : 0 < 2) hB hTB hfaith
  have hh := hT.trans hb
  norm_num at hh
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
