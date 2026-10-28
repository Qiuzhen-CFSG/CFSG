module
public import Theory.GroupTheory.QuaternionInvertingDiagonal
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Mathlib.GroupTheory.Sylow

/-!
# Elementary eights in a quaternion extension with an S₃ quotient

A self-centralizing normal Q₈*Q₈ core with quotient S₃ and an elementary
subgroup of order16 admits actual cubic and swapping involution actors.
The elementary subgroup meets the core in order8. Its outside involution
therefore swaps the intrinsic factors; a cubic acts nontrivially on a factor
because the core is self-centralizing. The quotient gives the inversion
relation, so the two quaternion diagonals have full point-stabilizer images.

Source application: Aschbacher--Smith, 15.1.11, printed p.1089. The quotient
is that of the original marked pair I, not its full H-star overgroup.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem dihedral_cubic_inversion :
    ∀ a b : DihedralGroup 3, a ^ 3 = 1 → b ^ 2 = 1 → b ≠ 1 → b*a*b⁻¹*a=1 := by
  decide +kernel

/-- Original marked S3 actors in a self-centralizing quaternion core extension. -/
theorem quaternion_dihedral_marked_actors
    (P V B C : Subgroup G) [P.Normal] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hP : Nat.card P = 32)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hjoin : B ⊔ C = P)
    (hself : centralizer (P : Set G) ≤ P)
    (hbound : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≤ 8)
    (e : (G ⧸ P) ≃* DihedralGroup 3) :
    ∃ g s : G, g^3=1 ∧ s^2=1 ∧ s∈V ∧ s∉P ∧
      g∈normalizer (B : Set G) ∧ g∈normalizer (C : Set G) ∧
      ((∃ b : B, g*(b:G)*g⁻¹≠b) ∨ (∃ c : C, g*(c:G)*g⁻¹≠c)) ∧
      B.conjBy s=C ∧ C.conjBy s=B ∧ s*g*s⁻¹*g∈P ∧ P⊔zpowers s=P⊔V := by
  have hnot : ¬V≤P := by
    intro hVP
    have hb := hbound (V.subgroupOf P) (IsElementaryAbelian.subgroupOf hVP)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv,hV] at hb
    omega
  have hidx : P.index=6 := by
    change Nat.card (G ⧸ P)=6
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hrel : P.relIndex V=2 := by
    have hr : P.relIndex V ∣ 2 := by
      simpa [hidx,hV] using Nat.dvd_gcd
        (relIndex_dvd_index_of_normal (H:=P) (K:=V)) (relIndex_dvd_card P V)
    have hn : P.relIndex V ≠ 1 := fun h => hnot (relIndex_eq_one.mp h)
    exact ((Nat.dvd_prime Nat.prime_two).mp hr).resolve_left hn
  have hA : Nat.card (P⊓V : Subgroup G)=8 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (V⊓P) V bot_le inf_le_left
    simp only [relIndex_bot_left,inf_relIndex_left,hrel,hV] at hh
    rw [inf_comm] at hh
    omega
  obtain ⟨s,hsV,hsP,hscover⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hsV
  have hswap := quaternion_factors_swapped_of_fixed_elementary_eight B C (P⊓V)
    hB hC hi hc (hjoin ▸ hP) (hjoin ▸ hself) (hjoin ▸ inf_le_left) hA
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx.2) s
    (by rw [hjoin,normalizer_eq_top]; trivial) (hjoin ▸ hsP)
    (fun x hx => setLike_mul_comm hsV hx.2)
  have hGcard : Nat.card G=192 := by
    have hh := P.card_mul_index
    rw [hP,hidx] at hh
    omega
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G:=G) 3 (by rw [hGcard]; decide)
  have hg3 : g^3=1 := hg ▸ pow_orderOf_eq_one g
  have hgP : g∉P := by
    intro h
    have hd := _root_.orderOf_dvd_natCard (⟨g,h⟩ : P)
    rw [←orderOf_submonoid (⟨g,h⟩ : P), hg,hP] at hd
    norm_num at hd
  have hgN := quaternion_factors_invariant_of_cube_eq_one B C hB hC hi hc
    (MulAut.conj g) (by rw [hjoin]; exact normal_iff_map_conj_eq.mp (inferInstance : P.Normal) g) (by
      intro x
      change g*(g*(g*x*g⁻¹)*g⁻¹)*g⁻¹=x
      calc
        _ = g^3*x*(g^3)⁻¹ := by simp only [pow_succ,pow_zero]; group
        _ = x := by rw [hg3]; simp)
  have hmove : (∃ b : B, g*(b:G)*g⁻¹≠b) ∨ (∃ c : C, g*(c:G)*g⁻¹≠c) := by
    by_contra! h
    have hfix : P ≤ (MulAut.conj g).toMonoidHom.eqLocus (MonoidHom.id G) := by
      rw [←hjoin]
      exact sup_le (fun b hb => h.1 ⟨b,hb⟩) (fun c hc => h.2 ⟨c,hc⟩)
    apply hgP
    apply hself
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hfix hx)).symm
  have hsg : s*g*s⁻¹*g∈P := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    rw [map_one]
    change (e.toMonoidHom.comp (QuotientGroup.mk' P)) (s*g*s⁻¹*g) = 1
    simp only [map_mul,map_inv]
    apply dihedral_cubic_inversion
    · rw [← map_pow,hg3,map_one]
    · rw [← map_pow,hs2,map_one]
    · intro he
      apply hsP
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (he.trans e.map_one.symm)
  have hsup : P⊔zpowers s=P⊔V := by
    apply le_antisymm
    · exact sup_le le_sup_left ((zpowers_le.mpr hsV).trans le_sup_right)
    · apply sup_le le_sup_left
      intro v hv
      rcases hscover v hv with hvs | hvp
      · have hs : s∈P⊔zpowers s := mem_sup_right (mem_zpowers s)
        have hh := (P⊔zpowers s).mul_mem (mem_sup_left hvs) ((P⊔zpowers s).inv_mem hs)
        simpa only [mul_inv_cancel_right] using hh
      · exact mem_sup_left hvp
  exact ⟨g,s,hg3,hs2,hsV,hsP,mem_normalizer_iff_map_conj_eq.mpr hgN.1,
    mem_normalizer_iff_map_conj_eq.mpr hgN.2,hmove,hswap.1,hswap.2,hsg,hsup⟩
/-- The marked S3 extension produces two distinct self-centralizing eights. -/
theorem quaternion_dihedral_two_eights_of_factors
    (P V B C : Subgroup G) [P.Normal] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hP : Nat.card P = 32)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hjoin : B ⊔ C = P)
    (hself : centralizer (P : Set G) ≤ P)
    (hbound : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≤ 8)
    (e : (G ⧸ P) ≃* DihedralGroup 3) :
    ∃ E F : Subgroup G, E≠F ∧
      ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
        U≤P ∧ P⊔V≤normalizer (U : Set G) ∧
        (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U) := by
  obtain ⟨g,s,hg3,hs2,_,_,hgB,hgC,hmove,hsB,hsC,hsg,hprod⟩ :=
    quaternion_dihedral_marked_actors P V B C hV hP hB hC hi hc hjoin hself hbound e
  have finish (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
      (hC : Nonempty (C ≃* QuaternionGroup 2))
      (hi : Nat.card (B⊓C : Subgroup G)=2) (hc : ∀b∈B,∀c∈C,b*c=c*b)
      (hjoin : B⊔C=P) (hgB : g∈normalizer (B : Set G))
      (hgC : g∈normalizer (C : Set G))
      (hm : ∃b:B,g*(b:G)*g⁻¹≠b) (hsB : B.conjBy s=C) :
      ∃ E F : Subgroup G, E≠F ∧
        ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
          U≤P ∧ P⊔V≤normalizer (U : Set G) ∧
          (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U) := by
    obtain ⟨model⟩ := hB
    obtain ⟨E,F,hne,hu⟩ := exists_two_quaternion_eights_point_image_of_inverting_swap
      B C model hi hc g s hg3 hs2 hgB hgC hm hsB (hjoin ▸ hsg)
    refine ⟨E,F,hne,?_⟩
    intro U hU
    obtain ⟨he,hcard,hle,hn,hgU,hpoint⟩ := hu U hU
    let := he
    have hgeom := quaternion_eight_geometry_of_inverting_swap B C U model hC hi hc
      hcard hle (le_sup_left.trans hn) g s hg3 hs2 hgB hgC hm hsB (hjoin ▸ hsg)
      hgU (hn (mem_sup_right (mem_zpowers s)))
    rw [hjoin,hprod] at hn hgeom
    exact ⟨he,hcard,hjoin ▸ hle,hn,hgeom.1,hpoint⟩
  rcases hmove with hm | hm
  · exact finish B C hB hC hi hc hjoin hgB hgC hm hsB
  · exact finish C B hC hB (by simpa only [inf_comm] using hi)
      (fun c hc' b hb => (hc b hb c hc').symm) (by rw [sup_comm,hjoin]) hgC hgB hm hsC

/-- The intrinsic quaternion presentation suffices for the marked S3 construction. -/
theorem QuaternionCentralProductData.two_eights_of_dihedral_quotient
    (P V : Subgroup G) [P.Normal] [IsElementaryAbelian 2 V]
    (d : QuaternionCentralProductData P) (hV : Nat.card V=16)
    (hself : centralizer (P : Set G) ≤ P) (e : (G ⧸ P) ≃* DihedralGroup 3) :
    ∃ E F : Subgroup G, E≠F ∧
      ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
        U≤P ∧ P⊔V≤normalizer (U : Set G) ∧
        (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U) := by
  let B := d.left.map P.subtype
  let C := d.right.map P.subtype
  have hB : Nonempty (B ≃* QuaternionGroup 2) := d.left_model.map
    (fun e => (d.left.equivMapOfInjective P.subtype P.subtype_injective).symm.trans e)
  have hC : Nonempty (C ≃* QuaternionGroup 2) := d.right_model.map
    (fun e => (d.right.equivMapOfInjective P.subtype P.subtype_injective).symm.trans e)
  have hi : Nat.card (B⊓C : Subgroup G)=2 := by
    rw [←map_inf _ _ _ P.subtype_injective,card_map_of_injective P.subtype_injective]
    exact d.intersection_card
  have hc : ∀b∈B,∀c∈C,b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  have hjoin : B⊔C=P := by
    rw [←map_sup,d.span,←MonoidHom.range_eq_map,range_subtype]
  exact quaternion_dihedral_two_eights_of_factors P V B C hV d.card hB hC hi hc hjoin
    hself d.elementary_card_le_eight e

end Subgroup
