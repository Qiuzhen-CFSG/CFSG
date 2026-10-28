module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.InvolutionPairs
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.LocalInvolutionSums
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.ThreeRegular
public import Theory.Character.InvolutionSum

/-!
# The ambient order identity from the original involution pair counts

The local pairing is eighteen. Its induction equals the ambient pairing,
whose coefficient at an irreducible is determined by the single involution
class. The signed five-character identity gives the exact group-order
relation with consecutive degrees and consecutive involution values.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
open Subgroup Theory.GroupTheory Theory.Character
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour LocalCharacters
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- Evaluation of an original induced-row identity at a three-regular
involution gives the consecutive character values. -/
theorem localAlpha_identity_involution
    (i : Fin 4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ψ μ : ClassFunction G)
    (hid : inducedClassFunction c.H (localAlpha c i) = 1 + (ε : ℂ) • (ψ - μ))
    (t : G) (ht : orderOf t = 2) : μ t = ψ t + (ε : ℂ) := by
  have h := congrFun hid t
  rw [induced_localAlpha_three_regular c i t (by rw [ht]; decide)] at h
  change 0 = 1 + (ε : ℂ) * (ψ t - μ t) at h
  rcases hε with rfl | rfl
  · norm_num at h ⊢
    linear_combination h
  · norm_num at h ⊢
    linear_combination -h

/-- Evaluation at the identity gives consecutive degrees. -/
theorem localAlpha_identity_degree
    (i : Fin 4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ψ μ : ClassFunction G)
    (hid : inducedClassFunction c.H (localAlpha c i) = 1 + (ε : ℂ) • (ψ - μ)) :
    μ 1 = ψ 1 + (ε : ℂ) := by
  have h := congrFun hid 1
  rw [induced_localAlpha_three_regular c i 1 (by simp)] at h
  change 0 = 1 + (ε : ℂ) * (ψ 1 - μ 1) at h
  rcases hε with rfl | rfl
  · norm_num at h ⊢
    linear_combination h
  · norm_num at h ⊢
    linear_combination -h

/-- The original configuration and actual signed induction identity imply
the order equation used by the finite character arithmetic. -/
theorem original_character_order_identity
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G)
    (i : Fin 4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ψ μ : ClassFunction G) (hψ : IsIrreducibleCharacter ψ)
    (hμ : IsIrreducibleCharacter μ)
    (hid : inducedClassFunction c.H (localAlpha c i) = 1 + (ε : ℂ) • (ψ - μ))
    (t : G) (ht : orderOf t = 2) :
    (Nat.card G : ℂ) * (ψ 1 - ψ t) ^ 2 = 5971968 * (ψ 1 * (ψ 1 + (ε : ℂ))) := by
  have hdegree := localAlpha_identity_degree c i ε hε ψ μ hid
  have hvalue := localAlpha_identity_involution c i ε hε ψ μ hid t ht
  let F : ClassFunction G := fun a => (involutionPairCount a : ℂ)
  have hpair : scalarProduct G (inducedClassFunction c.H (localAlpha c i)) F = 18 :=
    (three_singular_induction_involutionPairCount c hsmall (localAlpha c i)
      (localAlpha_supported c i)).trans (by
        convert localAlpha_involutionPairCount c i using 1
        congr 1
        exact Subsingleton.elim _ _)
  have hcoeff (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
      scalarProduct G χ F = (Nat.card G : ℂ) / 576 ^ 2 * χ t ^ 2 / χ 1 := by
    have h := scalarProduct_irreducible_involutionPairCount_of_fusion t ht
      (fun u hu => involutions_conjugate c u t hu ht) χ hχ
    rwa [involution_centralizer_card c t ht] at h
  rw [hid, scalarProduct_add_left, scalarProduct_smul_left, scalarProduct_sub_left,
    hcoeff _ isIrreducibleCharacter_one, hcoeff ψ hψ, hcoeff μ hμ,
    hdegree, hvalue] at hpair
  have hψ0 : ψ 1 ≠ 0 := by rw [hψ.degree_eq]; exact_mod_cast hψ.degree_pos.ne'
  have hμ0 : ψ 1 + (ε : ℂ) ≠ 0 := by
    rw [←hdegree, hμ.degree_eq]
    exact_mod_cast hμ.degree_pos.ne'
  rcases hε with rfl | rfl
  · norm_num only [Int.cast_one, Pi.one_apply, one_pow, div_one] at hpair hμ0 ⊢
    field_simp [hψ0, hμ0] at hpair
    linear_combination hpair
  · norm_num only [Int.cast_neg, Int.cast_one, Pi.one_apply, one_pow, div_one] at hpair hμ0 ⊢
    field_simp [hψ0, hμ0] at hpair
    linear_combination hpair

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
