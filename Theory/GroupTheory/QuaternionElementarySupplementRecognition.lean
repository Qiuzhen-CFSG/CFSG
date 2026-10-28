module

public import Theory.GroupTheory.QuaternionElementaryProduct
public import Theory.GroupTheory.PGroup.ExponentFourRankOne

/-!
# Quaternion subgroups in a quaternion–elementary central product

An order-eight subgroup of Q₈U meeting the central elementary factor U
in order two is quaternion. Every fourth power is trivial, and every
involution lies in U. Thus no elementary four-subgroup exists. The
exponent-four rank-one classification leaves Q₈ or a cyclic group; order
eight excludes the cyclic case.

Source application: Aschbacher–Smith J.2.7(5), printed p.435.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem quaternion_of_eight_in_quaternion_elementary_product
    (B U C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    [IsElementaryAbelian 2 U]
    (hBU : Nat.card (B ⊓ U : Subgroup G) = 2)
    (hcomm : B ≤ centralizer (U : Set G))
    (hC : C ≤ B ⊔ U) (hcard : Nat.card C = 8)
    (hCU : Nat.card (C ⊓ U : Subgroup G) = 2) :
    Nonempty (C ≃* QuaternionGroup 2) := by
  have hp : IsPGroup 2 C := IsPGroup.of_card (n := 3) hcard
  have hpow (x : C) : x ^ 4 = 1 := by
    have hm : (x:G) ∈ (B : Set G) * (U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B U
        (hcomm.trans (centralizer_le_normalizer _))]
      exact hC x.property
    obtain ⟨b,hb,u,hu,he⟩ := hm
    obtain ⟨e⟩ := hB
    have hb4 : b ^ 4 = 1 := by
      have hq : ∀ y : QuaternionGroup 2, y^4=1 := by decide +kernel
      have he4 : (⟨b,hb⟩ : B)^4=1 := e.injective (by rw [map_pow,hq,map_one])
      exact congrArg Subtype.val he4
    have hu4 : u ^ 4 = 1 := by
      have h2 := elemPow_eq_one_of_isElementaryAbelian u hu (p := 2)
      rw [show (4 : ℕ)=2*2 from rfl,pow_mul,h2,one_pow]
    apply Subtype.ext
    change (x:G)^4=1
    rw [← he, (show Commute b u from (hcomm hb u hu).symm).mul_pow,hb4,hu4,one_mul]
  have hfour (E : Subgroup C) (hE : IsElementaryAbelian 2 E) : Nat.card E ≠ 4 := by
    let : IsElementaryAbelian 2 E := hE
    have heU : E.map C.subtype ≤ U := by
      rw [← omegaOne_eq_of_quaternion_elementary_product B U hB hBU hcomm]
      rintro x ⟨y,hy,rfl⟩
      apply (omegaOneAmbient_le_iff _ _).mp le_rfl
      · exact hC y.property
      · exact congrArg (fun z : E => ((z:C):G))
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨y,hy⟩)
    have hle : E.map C.subtype ≤ C ⊓ U := le_inf (map_subtype_le _) heU
    have hc := card_le_of_le hle
    rw [card_map_of_injective C.subtype_injective,hCU] at hc
    omega
  rcases hp.isCyclic_or_quaternion_two_of_no_elementary_four hpow hfour with hcyc | hq
  · let : IsCyclic C := hcyc
    obtain ⟨x,hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hd := orderOf_dvd_of_pow_eq_one (hpow x)
    rw [hx,hcard] at hd
    norm_num at hd
  · exact hq

end Subgroup
