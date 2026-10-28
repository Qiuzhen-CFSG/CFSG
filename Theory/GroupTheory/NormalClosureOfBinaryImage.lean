module
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.InvertedThreeLift
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# A symmetric-three normal closure of a binary image

An order-two subgroup, whose image is nontrivial in S₃, normally generates
a copy of S₃ when the binary action kernel normalizes it. An inverted cubic
lift supplies a subgroup of order six containing the seed, and the image
cover lemma contains the entire normal closure there.

This is the quotient step in the first endpoint of Goldschmidt (6.9),
printed p.401. The actual source quotient is assembled separately.
-/

public section
open Subgroup
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

/-- An order-two subgroup normalized by the binary kernel normally generates
an actual symmetric-three subgroup. Used modulo the order-sixteen core in
the first endpoint of Goldschmidt (6.9). -/
theorem conjugateSpan_equiv_symmetricThree_of_two_kernel
    (f : A →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (D : Subgroup A) (hD : Nat.card D = 2)
    (hDf : Nat.card (D.map f) = 2) (hN : f.ker ≤ normalizer (D : Set A)) :
    Nonempty (conjugateSpanBy D ⊤ ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨y,hy,_⟩ := (Nat.card_eq_two_iff' (1 : D.map f)).mp hDf
  obtain ⟨t,ht,hty⟩ := y.property
  have hft : f t ≠ 1 := by
    intro he
    exact hy (Subtype.ext (hty.symm.trans he))
  have ht2 : t ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨t,ht⟩ : D))
    rw [hD] at hh
    exact congrArg Subtype.val hh
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 (fun he => hft (he ▸ f.map_one))
  have htD : zpowers t = D := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
    rw [Nat.card_zpowers, hto, hD]
  obtain ⟨X,hX,_,hXf,htX,_⟩ := exists_inverted_three_lift_of_two_kernel f hf hk t ht2 hft
  have htx : t ∉ X := by
    intro ht'
    have hh := X.orderOf_dvd_natCard ht'
    rw [hto,hX] at hh
    norm_num at hh
  let J := X ⊔ D
  have hJ : Nat.card J = 6 := by
    change Nat.card (X ⊔ D : Subgroup A) = 6
    rw [← htD, card_sup_zpowers_of_normalizing_involution X t ht2 htx htX, hX]
  have hJf : J.map f = ⊤ := permThree_join_image_eq_top f X D hXf hDf
  let S := conjugateSpanBy D ⊤
  have hSJ : S ≤ J := conjugateSpan_le_of_image_cover f D J le_sup_right
    (by rw [hJf]; exact le_top) hN
  have hSf : S.map f = ⊤ := by
    change (conjugateSpanBy D ⊤).map f = ⊤
    rw [map_conjugateSpanBy, ← MonoidHom.range_eq_map, f.range_eq_top_of_surjective hf]
    exact permThree_conjugateSpan_eq_top _ hDf
  let fS : S →* Equiv.Perm (Fin 3) := f.comp S.subtype
  have hs : Function.Surjective fS := by
    intro x
    obtain ⟨a,ha,he⟩ := (show x ∈ S.map f from hSf ▸ mem_top x)
    exact ⟨⟨a,ha⟩,he⟩
  have hcard : Nat.card S ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    have hh := Nat.card_le_card_of_injective (inclusion hSJ) (inclusion_injective hSJ)
    rw [hJ] at hh
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hh ⊢
    exact hh
  exact ⟨MulEquiv.ofBijective fS (hs.bijective_of_nat_card_le hcard)⟩

end Subgroup
