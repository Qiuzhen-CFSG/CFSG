module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import Theory.GroupTheory.Commutator.CentralCoprimeIndexTransfer
public import Theory.GroupTheory.Commutator.PerfectQuotient

/-!
# Perfectness of the HS covering normalizer

The actual normalizer has the same odd index as its model. Transfer in the
perfect ambient cover puts the central kernel inside the normalizer's derived
subgroup. Surjectivity onto the perfect model then proves that M is perfect.
The model perfectness and odd-index facts are supplied by ModelGeometry.

Source: Aschbacher–Smith I.2.2(i) and the final HS paragraph of I.2.2(5),
printed pp.410 and 412 / PDF pp.421 and 423.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
variable {K : Type*} [Group K] [Finite K]

theorem M_isPerfect [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hperfect : Group.IsPerfect baseNormalizer)
    (hindex : ¬ 2 ∣ baseNormalizer.index) : Group.IsPerfect (M e) := by
  let : Group.IsPerfect baseNormalizer := hperfect
  have hi : (M e).index = baseNormalizer.index :=
    baseNormalizer.index_comap_of_surjective
      (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
  have hz : center K ≤ (_root_.commutator (M e)).map (M e).subtype :=
    central_le_mapped_commutator_of_coprime_index (M e) (center K) le_rfl
      (center_le_M e) (by rw [hZ, hi]; exact Nat.prime_two.coprime_iff_not_dvd.mpr hindex)
  have hk : (localMap e).ker ≤ _root_.commutator (M e) := by
    intro x hx
    rw [localMap_ker] at hx
    obtain ⟨y, hy, he⟩ := hz hx
    exact (Subtype.ext he : y = x) ▸ hy
  exact ⟨by
    rw [← sup_of_le_right hk]
    exact CentralExtension.ker_sup_commutator_eq_top_of_surjective
      (localMap e) (localMap_surjective e)⟩
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
