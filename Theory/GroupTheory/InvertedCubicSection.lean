module
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.GroupTheory.SylowIndexThreeQuotient
/-!
# A cubic extension of an index-two two-subgroup

Let C be normal and have index two in a two-subgroup R. An involution in
R outside C which inverts a cubic element x makes R a nonnormal Sylow
subgroup of index three in the literal join R⟨x⟩. Consequently that join
has symmetric-three quotient by its own two-core.

The dihedral subgroup ⟨x,t⟩ bounds the join order by 3|R|; coprime order
counting gives equality. Inversion excludes normality of R. This is the
finite section used in Goldschmidt, *Automorphisms of trivalent graphs*
(1980), (4.4), printed p.393.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A]
/-- The actual cubic join has the supplied two-subgroup as Sylow and an
S₃ quotient, preserving both subgroup maps. -/
theorem sylow_and_quotient_of_index_two_inverted_cubic (C R : Subgroup A) [C.Normal] (hCR : C ≤ R) (hR : IsPGroup 2 R)
    (hi : C.relIndex R = 2) (t x : A) (htR : t ∈ R) (ht2 : t ^ 2 = 1)
    (htC : t ∉ C) (hx3 : orderOf x = 3) (hinv : t * x * t⁻¹ = x⁻¹) :
    ∃ P : Sylow 2 (R ⊔ zpowers x : Subgroup A),
      (P : Subgroup (R ⊔ zpowers x : Subgroup A)).map (R ⊔ zpowers x).subtype = R ∧
      Nonempty (((R ⊔ zpowers x : Subgroup A) ⧸
        pCore 2 (R ⊔ zpowers x : Subgroup A)) ≃* Equiv.Perm (Fin 3)) := by
  let H := R ⊔ zpowers x
  have hxR : x ∉ R := by
    intro hx
    have ho := hR.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x, hx⟩ : R)
    rw [Subgroup.orderOf_mk, hx3] at ho
    norm_num at ho
  have hRgen : C ⊔ zpowers t = R := sup_zpowers_eq_of_relIndex_prime hCR Nat.prime_two hi htR htC
  have htX : t ∉ zpowers x := by
    intro ht
    have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hx3, pow_one])
    have ht1 : t = 1 := disjoint_def.mp (hR.disjoint_of_coprime hp (by decide)) htR ht
    exact htC (ht1 ▸ C.one_mem)
  have hDcard := (DihedralGroup.sup_zpowers_equiv_of_inversion (by decide : 0 < 3)
    x t hx3 ht2 htX hinv).1
  have hH : H = C ⊔ (zpowers x ⊔ zpowers t) := by
    dsimp [H]
    rw [← hRgen]
    ac_rfl
  have hCi : C.relIndex H ≤ 6 := by
    rw [hH, relIndex_sup_left]
    have hd := C.relIndex_dvd_card (zpowers x ⊔ zpowers t)
    rw [hDcard] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hcount := relIndex_mul_card_of_le (hCR.trans (show R ≤ H from le_sup_left))
  have hRcount := relIndex_mul_card_of_le hCR
  rw [hi] at hRcount
  have hbound : Nat.card H ≤ 3 * Nat.card R := by nlinarith
  have hiRH : R.relIndex H = 3 := by
    have he := relIndex_mul_card_of_le (show R ≤ H from le_sup_left)
    have hd3 : 3 ∣ Nat.card H := by
      have hx : x ∈ H := mem_sup_right (mem_zpowers x)
      simpa only [Subgroup.orderOf_mk, hx3] using orderOf_dvd_natCard (⟨x, hx⟩ : H)
    have hcop : Nat.Coprime 3 (Nat.card R) := by
      obtain ⟨n, hn⟩ := hR.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have hd : 3 ∣ R.relIndex H := hcop.dvd_of_dvd_mul_right (he.symm ▸ hd3)
    have hpos : 0 < R.relIndex H := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hle : R.relIndex H ≤ 3 := by nlinarith
    exact le_antisymm hle (Nat.le_of_dvd hpos hd)
  let P : Sylow 2 H := hR.comap_subtype.toSylow (by change ¬ 2 ∣ R.relIndex H; rw [hiRH]; decide)
  have hn : ¬ (R.subgroupOf H).Normal := by
    intro hn
    let : (R.subgroupOf H).Normal := hn
    have hxH : x ∈ H := mem_sup_right (mem_zpowers x)
    have htH : t ∈ H := mem_sup_left htR
    have hh := hn.conj_mem (⟨t, htH⟩ : H) htR (⟨x, hxH⟩ : H)
    have hd : x ^ 2 ∈ R := by
      have he := congrArg Inv.inv hinv
      simp only [mul_inv_rev, inv_inv, ← mul_assoc] at he
      have hm := R.mul_mem hh (R.inv_mem htR)
      have he' : x * t * x⁻¹ * t⁻¹ = x ^ 2 := by
        calc
          _ = x * (t * x⁻¹ * t⁻¹) := by group
          _ = x * x := by rw [he]
          _ = x ^ 2 := (pow_two x).symm
      change x * t * x⁻¹ * t⁻¹ ∈ R at hm
      rwa [he'] at hm
    have hp : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
    have he : x ^ 2 * x ^ 2 = x := by
      calc
        _ = x ^ 3 * x := by group
        _ = x := by rw [hp, one_mul]
    exact hxR (he ▸ R.mul_mem hd hd)
  have hproper : pCore 2 H < (P : Subgroup H) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    apply hn
    change (P : Subgroup H).Normal
    rw [← he]
    infer_instance
  exact ⟨P, map_subgroupOf_eq_of_le le_sup_left,
    sylow_index_three_core_quotient P hiRH hproper⟩
end Theory.GroupTheory
