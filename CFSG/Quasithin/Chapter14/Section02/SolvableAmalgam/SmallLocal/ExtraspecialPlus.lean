module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductPointStabilizer
public import Theory.GroupTheory.QuaternionCentralProductEnlargementOrder

/-!
# The extraspecial-plus branch of Lemma 14.2.21

The intrinsic factor data retain the two embedded quaternion groups and
their common central involution. The imported geometry proves extraspeciality,
the elementary central quotient, and invariance of its square map.

For the enlarged group of order 576, a Sylow three-subgroup supplies
independent cubic actions on the factors. Together with the local order-64
normalizing subgroup these give exactly the S₄ stabilizer of the specified
central involution on the elementary eight. This is equality of the actual
conjugation image, with its centralizer kernel.

The full orthogonal outer-action identification and recognition of the
enlarged odd residual remain separate prerequisites of the source argument.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialPlus

open Subgroup

/-- The larger local group acts as the full S₄ point stabilizer on its
elementary eight. All factors, the point, and the normalizer action are actual
subgroups and elements of the larger group. -/
public theorem normalizer_stabilizer_of_order576
    {G : Type*} [Group G] [Finite G] (B C E S : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [(B ⊔ C : Subgroup G).Normal]
    (hself : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hG : Nat.card G = 576)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (hEQ : E ≤ B ⊔ C)
    (hS : Nat.card S = 64) (hSN : S ≤ normalizer (E : Set G))
    (hcentral : S ⊓ centralizer (E : Set G) = E)
    (z : E) (hz : z ≠ 1)
    (hzQ : (z : G) ∈ (center (B ⊔ C : Subgroup G)).map (B ⊔ C).subtype) :
    E.normalizerMonoidHom.range = MulAction.stabilizer (MulAut E) z ∧
      Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)) ∧
      E.normalizerMonoidHom.ker =
        (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) := by
  have hN : Nat.card (normalizer ((B ⊔ C : Subgroup G) : Set G)) = 576 := by
    rw [normalizer_eq_top, Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv]
    exact hG
  obtain ⟨actors⟩ := exists_independent_cubics_of_quaternion_central_product
    B C hB hC hinter hcomm hself hN
  obtain ⟨himage, hS4⟩ := actors.normalizer_eq_stabilizer hB hC hinter hcomm
    E S hE hEQ hS hSN hcentral z hz hzQ
  exact ⟨himage, hS4, normalizerMonoidHom_ker E⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialPlus
