module
public import Theory.GroupTheory.QuaternionFixedEight
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.QuaternionSwapCommutator

/-!
# An involution's fixed elementary eight is its commutator

Let two commuting quaternion subgroups have intersection of order two and
join of order32. If an involution normalizes their join and has elementary
fixed subgroup of order eight, that fixed subgroup equals the commutator
of the join with the involution's cyclic group.

Quaternion factors are intrinsic, so the actor either preserves both or
interchanges them. Preservation would make both restrictions inner by the
fixed-eight theorem. Each inner conjugator is itself fixed, hence has
square one and is central in its quaternion factor. Both restrictions
would therefore be trivial, contradicting fixed subgroup order eight.
The actor interchanges the factors, and the quaternion swap commutator
theorem gives the equality, including the shared central involution.

This intrinsic calculation supports the final intersection identity in
Stellmacher (9.1), Journal of Algebra190 (1997), p.47, source(8).
It uses no graph context or subsequent core equality.
-/

namespace Subgroup
open scoped commutatorElement

private theorem fixed_quaternion_restriction
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hcard : Nat.card (B ⊔ C : Subgroup G)=32)
    (s : G)
    (hBn : s ∈ normalizer B) (hCn : s ∈ normalizer C)
    (hAcard : Nat.card ((B ⊔ C) ⊓ centralizer ({s} : Set G) : Subgroup G)=8)
    (hAexp : ∀ a ∈ (B ⊔ C) ⊓ centralizer ({s} : Set G), a^2=1) :
    B ≤ centralizer ({s} : Set G) := by
  let A := (B ⊔ C) ⊓ centralizer ({s} : Set G)
  obtain ⟨b,hb,hact⟩ := factor_inner_of_fixed_eight B C A hB hC hcomm
    hcard inf_le_left hAcard hAexp s hBn hCn (by
      intro a ha
      exact (mem_centralizer_singleton_iff.mp ha.2).symm)
  have hbfix : b ∈ centralizer ({s} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hh := hact b hb
    have hconj : s*b*s⁻¹=b := by simpa using hh
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hb2 : b^2=1 := hAexp b ⟨mem_sup_left hb,hbfix⟩
  obtain ⟨model⟩ := hB
  have hbc : ∀ x ∈ B, b*x=x*b := by
    intro x hx
    have hh : ∀ a x : QuaternionGroup 2, a^2=1 → a*x=x*a := by decide
    have hbm : (model ⟨b,hb⟩)^2=1 := by
      rw [← map_pow]
      have h : (⟨b,hb⟩ : B)^2=1 := Subtype.ext hb2
      rw [h,map_one]
    have hm := hh (model ⟨b,hb⟩) (model ⟨x,hx⟩) hbm
    have he : (⟨b,hb⟩ : B)*⟨x,hx⟩=⟨x,hx⟩*⟨b,hb⟩ := by
      apply model.injective
      simpa only [map_mul] using hm
    exact congrArg Subtype.val he
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have hh := hact x hx
  rw [hbc x hx, mul_inv_cancel_right] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem swap_of_fixed_eight
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G)=2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hcard : Nat.card (B ⊔ C : Subgroup G)=32)
    (s : G) (hn : s ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hAcard : Nat.card ((B ⊔ C) ⊓ centralizer ({s} : Set G) : Subgroup G)=8)
    (hAexp : ∀ a ∈ (B ⊔ C) ⊓ centralizer ({s} : Set G), a^2=1) :
    B.map (MulAut.conj s).toMonoidHom = C := by
  let e := MulAut.conj s
  have hjoin : (B ⊔ C).map e.toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have him (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hle : D ≤ B ⊔ C) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
    · obtain ⟨model⟩ := hD
      exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans model⟩
    · exact (map_mono hle).trans_eq hjoin
  rcases him B hB le_sup_left with hBB | hBC
  · have hCC : C.map e.toMonoidHom = C := by
      rcases him C hC le_sup_right with hCB | hCC
      · have hEq : B=C := map_injective e.injective (hBB.trans hCB.symm)
        have hBc : Nat.card B=8 := by
          obtain ⟨model⟩ := hB
          rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
        rw [← hEq, inf_idem, hBc] at hinter
        omega
      · exact hCC
    have hBn : s ∈ normalizer B := mem_normalizer_iff_map_conj_eq.mpr hBB
    have hCn : s ∈ normalizer C := mem_normalizer_iff_map_conj_eq.mpr hCC
    have hBfix := fixed_quaternion_restriction B C hB hC hcomm hcard s hBn hCn hAcard hAexp
    have hCfix := fixed_quaternion_restriction C B hC hB
      (fun c hc b hb => (hcomm b hb c hc).symm)
      (by simpa only [sup_comm] using hcard) s hCn hBn
      (by simpa only [sup_comm] using hAcard) (by simpa only [sup_comm] using hAexp)
    have hfixed : (B ⊔ C) ⊓ centralizer ({s} : Set G) = B ⊔ C :=
      inf_eq_left.mpr (sup_le hBfix hCfix)
    rw [hfixed, hcard] at hAcard
    omega
  · exact hBC
/-- An involution whose fixed subgroup in a quaternion central product is
an elementary eight has that exact subgroup as its commutator. -/
public theorem commutator_zpowers_eq_fixed_eight
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G)=2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hcard : Nat.card (B ⊔ C : Subgroup G)=32)
    (s : G) (hs : s^2=1)
    (hn : s ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hAcard : Nat.card ((B ⊔ C) ⊓ centralizer ({s} : Set G) : Subgroup G)=8)
    (hAelem : IsElementaryAbelian 2 ((B ⊔ C) ⊓ centralizer ({s} : Set G) : Subgroup G)) :
    ⁅B ⊔ C, zpowers s⁆ = (B ⊔ C) ⊓ centralizer ({s} : Set G) := by
  have hAexp : ∀ a ∈ (B ⊔ C) ⊓ centralizer ({s} : Set G), a^2=1 := by
    let _ := hAelem
    exact fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hswap := swap_of_fixed_eight B C hB hC hinter hcomm hcard s hn hAcard hAexp
  exact commutator_zpowers_eq_fixed_of_quaternion_swap B C hB hinter hcomm s hs hswap
end Subgroup
