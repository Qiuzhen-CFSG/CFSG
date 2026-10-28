module
public import Theory.GroupTheory.QuaternionFixedEight
public import Theory.GroupTheory.QuaternionCentralProductFactors

/-!
# Elementary eights force interchange of the quaternion factors

An outside actor centralizing an elementary eight in a self-centralizing
quaternion central product interchanges its two intrinsic factors. If it
preserved the factors, the fixed-eight restriction theorem would make both
restrictions inner. Multiplying the two conjugators would then place the
actor in the central product.

Source: Aschbacher–Smith, §5.3.7, printed p.661 (PDF p.678), the `a₂` action.
-/

namespace Subgroup

/-- An actor outside a self-centralizing quaternion central product which
centralizes an elementary eight interchanges the two quaternion factors. -/
public theorem quaternion_factors_swapped_of_fixed_elementary_eight
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hcard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (hself : centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hU : U ≤ B ⊔ C) (hUcard : Nat.card U = 8)
    (hUexp : ∀ u ∈ U, u ^ 2 = 1)
    (s : G) (hn : s ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hout : s ∉ B ⊔ C) (hfix : ∀ u ∈ U, Commute s u) :
    B.map (MulAut.conj s).toMonoidHom = C ∧
      C.map (MulAut.conj s).toMonoidHom = B := by
  let e := MulAut.conj s
  have hjoin : (B ⊔ C).map e.toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have him (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hle : D ≤ B ⊔ C) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C :=
    quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
      ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans hD.some⟩
      ((map_mono hle).trans_eq hjoin)
  have hne : B ≠ C := by
    intro hh
    have hc : Nat.card B = 8 := by
      rw [Nat.card_congr hB.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← hh, inf_idem, hc] at hinter
    omega
  have hBC : B.map e.toMonoidHom = C := by
    rcases him B hB le_sup_left with hBB | hBC
    · have hCC : C.map e.toMonoidHom = C :=
        (him C hC le_sup_right).resolve_left
          (fun hCB => hne (map_injective e.injective (hBB.trans hCB.symm)))
      have hBn := mem_normalizer_iff_map_conj_eq.mpr hBB
      have hCn := mem_normalizer_iff_map_conj_eq.mpr hCC
      obtain ⟨b, hb, hactB⟩ := factor_inner_of_fixed_eight B C U hB hC hcomm
        hcard hU hUcard hUexp s hBn hCn hfix
      obtain ⟨c, hc, hactC⟩ := factor_inner_of_fixed_eight C B U hC hB
        (fun c hc b hb => (hcomm b hb c hc).symm)
        (by simpa only [sup_comm] using hcard) (by simpa only [sup_comm] using hU)
        hUcard hUexp s hCn hBn hfix
      let d := b * c
      have hact : ∀ x ∈ B ⊔ C, s * x * s⁻¹ = d * x * d⁻¹ := by
        apply (show B ⊔ C ≤ e.toMonoidHom.eqLocus (MulAut.conj d).toMonoidHom from ?_)
        apply sup_le
        · intro x hx
          change s * x * s⁻¹ = (b*c) * x * (b*c)⁻¹
          rw [hactB x hx]
          have hcx := hcomm x hx c hc
          calc
            _ = b * (c * x * c⁻¹) * b⁻¹ := by rw [← hcx, mul_inv_cancel_right]
            _ = _ := by group
        · intro x hx
          change s * x * s⁻¹ = (b*c) * x * (b*c)⁻¹
          rw [hactC x hx, hcomm b hb c hc]
          have hbx := hcomm b hb x hx
          calc
            _ = c * (b * x * b⁻¹) * c⁻¹ := by rw [hbx, mul_inv_cancel_right]
            _ = _ := by group
      have hz : d⁻¹ * s ∈ centralizer ((B ⊔ C : Subgroup G) : Set G) := by
        intro x hx
        apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
        calc
          (d⁻¹*s)*x*(d⁻¹*s)⁻¹ = d⁻¹*(s*x*s⁻¹)*d := by group
          _ = x := by rw [hact x hx]; group
      apply False.elim
      apply hout
      have hd : d ∈ B ⊔ C := (B ⊔ C).mul_mem (mem_sup_left hb) (mem_sup_right hc)
      simpa only [mul_inv_cancel_left] using (B ⊔ C).mul_mem hd (hself hz)
    · exact hBC
  exact ⟨hBC, (him C hC le_sup_right).resolve_right
    (fun hCC => hne (map_injective e.injective (hBC.trans hCC.symm)))⟩

end Subgroup
