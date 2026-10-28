module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.TwoPerfect
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.Quasithin.Rank
/-!
# Placement through a normal two-core quotient

If a normal subgroup has symmetric-three-square quotient modulo its two-core,
rank-two placement in the actual ambient two-core quotient puts every
two-perfect {2,3}-actor in that normal subgroup. The final lift absorbs the
normal two-group kernel by two-perfectness.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
variable {A : Type*} [Group A] [Finite A]
theorem le_normal_of_quotient_pair
    (N : Subgroup A) [N.Normal]
    (e : (N ⧸ pCore 2 N) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (B : Subgroup A) (hB : IsPPerfect 2 B) (hrank : primeRank 3 A ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n) : B ≤ N := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let C := N.map q
  let D := B.map q
  let : C.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let ec : C ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    (Normal.isSubnormal (inferInstance : N.Normal)).quotientCoreImageEquiv 2 |>.symm.trans e
  have hD : IsPPerfect 2 D := hB.of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  have hr : primeRank 3 (A ⧸ pCore 2 A) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrank
  have ho : ∃ m n : ℕ, Nat.card D ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨m,n,hh⟩ := horder
    exact ⟨m,n,(card_map_dvd B q).trans hh⟩
  have hd := le_pair_of_twoPerfect C ec D hD hr ho
  have hBN : B ≤ N ⊔ pCore 2 A := by
    have hb := map_le_iff_le_comap.mp hd
    simpa only [C, comap_map_eq, q, QuotientGroup.ker_mk'] using hb
  exact le_of_isPPerfect_of_le_sup_of_normalizes B N (pCore 2 A) hB pCore_isPGroup
    (by rw [normalizer_eq_top]; exact le_top) hBN
end Theory.GroupTheory.NormalSymmetricThreePairRank
