module

public import Theory.GroupTheory.QuaternionCentralProductEightPoint
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Full point stabilizers above a quaternion central product

Independent cubic actors supply an element of order three on every elementary
eight in the quaternion product. An order-64 normalizing subgroup with
centralizer equal to the eight supplies an automizer of order eight. Together
these force order 24. Normality of the quaternion product fixes its common
central involution, so the image is exactly its S₄ stabilizer.

The order-64 overgroup is essential here: the odd residual central product
SL₂(3) * SL₂(3) alone has no subgroup of order 64. The theorem therefore retains
this local witness in the larger group, and retains the conjugation map.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005.
-/

namespace Subgroup

/-- A central distinguished point, a Sylow-sized two-action, and a cubic
actor force the actual normalizer image to be the full point stabilizer. -/
public theorem elementaryEight_normalizer_eq_stabilizer_of_cubic
    {G : Type*} [Group G] [Finite G] (E S : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (hS : Nat.card S = 64)
    (hSN : S ≤ normalizer (E : Set G))
    (hcentral : S ⊓ centralizer (E : Set G) = E)
    (z : E) (hz : z ≠ 1) (hzG : (z : G) ∈ center G)
    (g : normalizer (E : Set G)) (hg : orderOf (E.normalizerMonoidHom g) = 3) :
    E.normalizerMonoidHom.range = MulAction.stabilizer (MulAut E) z ∧
      Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)) := by
  let R := E.normalizerMonoidHom.range
  let T := MulAction.stabilizer (MulAut E) z
  have hfix (n : normalizer (E : Set G)) : E.normalizerMonoidHom n z = z := by
    apply Subtype.ext
    change (n : G) * z * (n : G)⁻¹ = z
    rw [mem_center_iff.mp hzG, mul_inv_cancel_right]
  have hRT : R ≤ T := by
    rintro a ⟨n, rfl⟩
    exact hfix n
  let f := E.normalizerMonoidHom.comp (inclusion hSN)
  have hES : E ≤ S := hcentral ▸ inf_le_left
  have hker : f.ker = E.subgroupOf S := by
    ext s
    change inclusion hSN s ∈ E.normalizerMonoidHom.ker ↔ (s : G) ∈ E
    rw [normalizerMonoidHom_ker]
    change (s : G) ∈ centralizer (E : Set G) ↔ (s : G) ∈ E
    conv_rhs => rw [← hcentral]
    simp only [mem_inf, s.property, true_and]
  have hfcard : Nat.card f.range = 8 := by
    have h := f.ker.index_mul_card
    rw [index_ker, hker, Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv,
      hE, hS] at h
    omega
  have hd8 : 8 ∣ Nat.card R := by
    rw [← hfcard]
    apply card_dvd_of_le
    rintro a ⟨s, rfl⟩
    exact ⟨inclusion hSN s, rfl⟩
  have hd3 : 3 ∣ Nat.card R := by
    let a : R := ⟨E.normalizerMonoidHom g, ⟨g, rfl⟩⟩
    have h := _root_.orderOf_dvd_natCard a
    rw [← orderOf_coe] at h
    simpa only [a, hg] using h
  have h24 : 24 ∣ Nat.card R :=
    (show Nat.Coprime 8 3 by decide).mul_dvd_of_dvd_of_dvd hd8 hd3
  have hTc : Nat.card T ∣ 24 :=
    elementaryEight_fixed_point_image_card_dvd_twentyfour hE z hz T
      (fun a => a.property)
  have hRc : Nat.card R = 24 := Nat.dvd_antisymm
    ((card_dvd_of_le hRT).trans hTc) h24
  have heq : R = T := eq_of_le_of_card_ge hRT (by
    rw [hRc]
    exact Nat.le_of_dvd (by decide) hTc)
  refine ⟨heq, ?_⟩
  apply elementaryEight_fixed_point_order24_equiv_S4 hE z hz T
    (by rw [← heq]; exact hRc)
  exact fun a => a.property

/-- Independent cubic actions on a normal quaternion central product give
the full S₄ stabilizer of its specified common central involution. -/
public theorem QuaternionIndependentCubics.normalizer_eq_stabilizer
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [(B ⊔ C : Subgroup G).Normal]
    (E S : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hEQ : E ≤ B ⊔ C)
    (hS : Nat.card S = 64) (hSN : S ≤ normalizer (E : Set G))
    (hcentral : S ⊓ centralizer (E : Set G) = E)
    (z : E) (hz : z ≠ 1)
    (hzQ : (z : G) ∈ (center (B ⊔ C : Subgroup G)).map (B ⊔ C).subtype) :
    E.normalizerMonoidHom.range = MulAction.stabilizer (MulAut E) z ∧
      Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)) := by
  let Z := (center (B ⊔ C : Subgroup G)).map (B ⊔ C).subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective (B ⊔ C).subtype_injective]
    exact quaternion_central_product_center_card B C hB hC hinter hcomm
  have hzG : (z : G) ∈ center G := central_of_normal_card_two Z hZcard hzQ
  obtain ⟨a, ha, haE⟩ := actors.exists_nontrivial_normalizing hB hC hinter hcomm E hE hEQ
  exact elementaryEight_normalizer_eq_stabilizer_of_cubic E S hE hS hSN hcentral z hz hzG
    ⟨a, haE⟩ (actors.orderOf_restriction_eq_three E hB hC hinter hcomm hE hEQ a ha haE)

end Subgroup
