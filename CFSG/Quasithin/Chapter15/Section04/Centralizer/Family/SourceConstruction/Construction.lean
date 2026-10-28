module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Lifting
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Normalizers

/-!
# The normal order-three branch of the family construction

A nontrivial normal quotient factor lifts to a nontrivial normal residual
subgroup of M. Characteristic two gives its nontrivial two-core, which remains
normal in the join with T. This discharges the H(T) condition in the lowercase
Xi definition. Thus a normal order-three quotient factor with full Thompson
commutator constructs an actual source Y-member, with no assumed H-membership.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the split case in the proof of 15.4.12, printed p.1161.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource
open LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

/-- Normal quotient factors give relative normality of the residual lifts. -/
theorem lift_normal (M : Subgroup G) (A : Subgroup (CoreQuotient M)) (hn : A.Normal) :
    ((lift M A).subgroupOf M).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (lift_le M A)).mpr
  apply lift_normalized M M le_rfl A
  rw [normalizer_eq_top_iff.mpr hn]
  exact le_top

/-- A normal nontrivial two-perfect quotient factor supplies the genuine
H(T) condition for its residual lift. -/
theorem normal_lift_join_mem_HOver (T M : Subgroup G) (hTM : T ≤ M)
    (hEC : HasCharacteristicTwo M) (A : Subgroup (CoreQuotient M))
    (hp : IsPPerfect 2 A) (hne : A ≠ ⊥) (hn : A.Normal) :
    lift M A ⊔ T ∈ Chapter1.HOver G (T : Set G) := by
  have hLne : lift M A ≠ ⊥ := by
    intro h
    apply hne
    rw [← image_lift M A hp, h]
    simp only [image, bot_subgroupOf, Subgroup.map_bot]
  have hLN := lift_normal M A hn
  have hLM : M ≤ normalizer (lift M A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (lift_le M A)).mp hLN
  have hCne := coreIn_ne_bot_of_normal hEC hLne (lift_le M A) hLN
  have hCnorm : M ≤ normalizer ((lift M A).pCoreIn 2 : Set G) :=
    hLM.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (lift M A)))
  have hCjoin : (lift M A).pCoreIn 2 ≤ (lift M A ⊔ T).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((pCoreIn_le 2 _).trans le_sup_left)
      ((sup_le (lift_le M A) hTM).trans hCnorm)
  refine ⟨?_, show T ≤ lift M A ⊔ T from le_sup_right⟩
  intro hbot
  exact hCne (le_bot_iff.mp (hbot ▸ hCjoin))

/-- A normal cubic quotient factor with full Thompson commutator constructs
a source Y-member. All the local-family membership conditions are proved. -/
theorem normal_prime_lift_mem_Y (T M : Subgroup G) (hTM : T ≤ M)
    (hEC : HasCharacteristicTwo M) (A : Subgroup (CoreQuotient M))
    (hA : Nat.card A = 3) (hn : A.Normal)
    (hc : ⁅A, image M (elementaryAbelianMaxJ T)⁆ = A) : lift M A ∈ Y T := by
  have hne : A ≠ ⊥ := by
    intro h
    have hh := hA
    rw [h, card_bot] at hh
    omega
  apply prime_lift_mem_Y T M hTM A hA
  · rw [normalizer_eq_top_iff.mpr hn]
    exact le_top
  · exact hc
  · exact normal_lift_join_mem_HOver T M hTM hEC A (three_isPPerfect A hA) hne hn

end CFSG.Quasithin.Chapter15.Section04.FamilySource
