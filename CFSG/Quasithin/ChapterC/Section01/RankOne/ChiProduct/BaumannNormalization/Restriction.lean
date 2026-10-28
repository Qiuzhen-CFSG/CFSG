module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BaumannNormalization.FixedWitness
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Restriction to the normalizer of one moved block

The identity K=[K,J(R)] puts J(R) in N_R(K). Thompson heredity preserves
J under this restriction. The actual Sylow intersection R∩K then makes
N_R(K) Sylow in K N_R(K). Source: C.1.16(2) and C.5.4(1), pp.125--126,155.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
variable {G : Type*} [Group G] [Finite G]

theorem thompson_normalizer_intersection (R K : Subgroup G)
    (hm : K = ⁅K,elementaryAbelianMaxJ R⁆) :
    elementaryAbelianMaxJ (R ⊓ normalizer K : Subgroup G) = elementaryAbelianMaxJ R := by
  have hj : elementaryAbelianMaxJ R ≤ R ⊓ normalizer K :=
    le_inf (sSup_le fun _ hA => hA.1) (normalizes_of_moved R K hm)
  obtain ⟨h₁,hj₁⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_eq (R ⊓ normalizer K) R inf_le_left
  obtain ⟨h₂,hj₂⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R (R ⊓ normalizer K) hj
  exact le_antisymm (hj₁ (le_antisymm h₁ h₂)) (hj₂ (le_antisymm h₂ h₁))

theorem normalizer_intersection_sylow (R K : Subgroup G)
    (hR : IsPGroup 2 R) (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = R ⊓ K) :
    ∃ S : Sylow 2 (K ⊔ (R ⊓ normalizer K) : Subgroup G),
      (S : Subgroup (K ⊔ (R ⊓ normalizer K) : Subgroup G)).map
        (K ⊔ (R ⊓ normalizer K)).subtype = R ⊓ normalizer K := by
  apply IsPGroup.exists_sylow_sup_of_coprime_index K (R ⊓ normalizer K)
    (hR.to_le inf_le_left) inf_le_right (P : Subgroup K) P.not_dvd_index
  rw [hP]
  exact inf_le_inf_left R K.le_normalizer
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
