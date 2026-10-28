module
public import Theory.GroupTheory.QuaternionCentralProductEnlargementOrder
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
import all Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction

/-!
# Independent cubics above an order384 quaternion local group

A normal quaternion subgroup of order32 lies in the ambient two-core.
When that core lies in the source order64 envelope, restriction across
index at most two makes its centralizer a two-group. The envelope center
then forces self-centralization of the quaternion subgroup itself.

The automorphism bound makes the ambient order divide2304. A proper
order384 subgroup sharing a full Sylow has odd index three, so the ambient
order is1152. Its order-nine Sylow subgroup acts faithfully on the two
quaternion factors. Restriction supplies a cubic acting on only the first
factor, without choosing coordinates for that action.

The proof reuses the private restriction calculations of IndependentCubics
through a narrow public theorem; their original public interfaces are unchanged.
Source: Aschbacher–Smith, proof of14.2.21, printed p.988 (PDF p.1005).
-/

public noncomputable section
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem centralizer_le_of_index_two_center_le
    (E : Subgroup D) (hi : E.index = 2) (hz : center D ≤ E) :
    centralizer (E : Set D) ≤ E := by
  intro x hx
  by_contra hxe
  apply hxe
  apply hz
  apply mem_center_iff.mpr
  intro y
  by_cases hy : y ∈ E
  · exact hx y hy
  · have hxy : x*y ∈ E := (E.mul_mem_iff_of_index_two hi).mpr (by simp [hxe,hy])
    have hh := hx (x*y) hxy
    simpa only [mul_assoc, mul_left_cancel_iff] using hh

/-- A normal subgroup of order32 is self-centralizing if its order64 core
envelope has centralizer contained in it and the ambient two-core is
self-centralizing. The ambient core is allowed to be either size. -/
theorem selfCentralizing_of_core_envelope_thirty_two
    (E P : Subgroup D) [E.Normal]
    (hE : Nat.card E = 32) (hP : Nat.card P = 64)
    (hEP : E ≤ P) (hQP : pCore 2 D ≤ P)
    (hz : center P ≤ E.subgroupOf P)
    (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) :
    centralizer (E : Set D) ≤ E := by
  have hEQ : E ≤ pCore 2 D := le_sSup ⟨inferInstance,
    IsPGroup.of_card (n := 5) (by rw [hE]; rfl)⟩
  have hcard (U : Subgroup D) (hEU : E ≤ U) : Nat.card (E.subgroupOf U) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv).trans hE
  have hiP : (E.subgroupOf P).index = 2 := by
    have hh := (E.subgroupOf P).card_mul_index
    rw [hcard P hEP,hP] at hh
    omega
  have hiQ : (E.subgroupOf (pCore 2 D)).index ≤ 2 := by
    have hh := (E.subgroupOf (pCore 2 D)).card_mul_index
    rw [hcard _ hEQ] at hh
    have hle := card_le_of_le hQP
    rw [hP] at hle
    omega
  have hCQ : centralizer (E : Set D) ≤ pCore 2 D := by
    by_cases hi : (E.subgroupOf (pCore 2 D)).index = 1
    · have heq : E = pCore 2 D := le_antisymm hEQ (relIndex_eq_one.mp hi)
      rwa [heq]
    · have hpos : (E.subgroupOf (pCore 2 D)).index ≠ 0 := index_ne_zero_of_finite
      have htwo : (E.subgroupOf (pCore 2 D)).index = 2 := by omega
      exact le_sSup ⟨inferInstance,centralizer_isPGroup_of_index_two_in_core hc E htwo⟩
  intro x hx
  have hxP : x ∈ P := hQP (hCQ hx)
  exact show (⟨x,hxP⟩ : P) ∈ E.subgroupOf P from
    centralizer_le_of_index_two_center_le _ hiP hz (fun y hy =>
      Subtype.ext (hx y hy))

/-- A proper order384 local overgroup sharing a full Sylow has index three
above a normal self-centralizing quaternion product. -/
theorem card_eq_1152_of_quaternion_product_enlargement
    (Q : Subgroup D) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set D) ≤ Q)
    (H : Subgroup D) (hH : Nat.card H = 384) (hproper : H ≠ ⊤)
    (S : Sylow 2 D) (hSH : (S : Subgroup D) ≤ H) : Nat.card D = 1152 := by
  have hd := card_dvd_of_selfCentralizing_quaternion_factors Q hcentral d.center_card
    d.left d.right d.left_model d.right_model d.intersection_card d.commute d.span
  have hcount := H.card_mul_index
  rw [hH] at hcount
  rw [← hcount] at hd
  have hindex : H.index ∣ 6 :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 384) hd
  have hodd : ¬ 2 ∣ H.index :=
    fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSH))
  have hne : H.index ≠ 1 := fun h => hproper (index_eq_one.mp h)
  have hbound : H.index ≤ 6 := Nat.le_of_dvd (by decide) hindex
  have hi : H.index = 3 := by interval_cases h : H.index <;> norm_num at *
  rw [hi] at hcount
  exact hcount.symm

/-- The order-nine Sylow supplies an actual cubic acting only on the first
of the original quaternion factors. No chosen cyclic action is imposed. -/
theorem exists_left_cubic_of_quaternion_product_card_1152
    (B C : Subgroup D)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup D) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    [(B ⊔ C).Normal]
    (hcentral : centralizer ((B ⊔ C : Subgroup D) : Set D) ≤ B ⊔ C)
    (hD : Nat.card D = 1152) :
    ∃ u : D, orderOf u = 3 ∧ u ∈ normalizer (B : Set D) ∧
      u ∈ centralizer (C : Set D) ∧ u ∉ centralizer (B : Set D) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 D := Classical.choice inferInstance
  let A : Subgroup D := P
  have hA : Nat.card A = 9 := by
    rw [P.card_eq_multiplicity,hD]
    decide +kernel
  have hnorm := nine_subgroup_normalizes_quaternion_factors B C A hB hC hinter hcomm hA
    (by rw [normalizer_eq_top]; exact le_top)
  let f : A →* MulAut B := B.normalizerMonoidHom.comp (inclusion hnorm.1)
  let g : A →* MulAut C := C.normalizerMonoidHom.comp (inclusion hnorm.2)
  have hf (a : A) (b : B) : (f a b : D) = a*b*(a:D)⁻¹ := rfl
  have hg (a : A) (c : C) : (g a c : D) = a*c*(a:D)⁻¹ := rfl
  have hinj := faithful_quaternion_restrictions B C A hB hC hinter hcomm hcentral hA f g hf hg
  have hBaut : Nat.card (MulAut B) = 24 := by
    rw [Nat.card_congr (MulAut.congr hB.some).toEquiv, QuaternionGroup.card_mulAut_two]
  have hCaut : Nat.card (MulAut C) = 24 := by
    rw [Nat.card_congr (MulAut.congr hC.some).toEquiv, QuaternionGroup.card_mulAut_two]
  obtain ⟨_,u,_,hu,_,hfu,hgu,_⟩ :=
    independent_cubics_of_faithful_pair hA hBaut hCaut f g hinj
  refine ⟨u,(orderOf_injective A.subtype A.subtype_injective u).trans hu,
    hnorm.1 u.property,?_,?_⟩
  · intro c hc
    have hh := hg u ⟨c,hc⟩
    rw [hgu] at hh
    exact eq_mul_inv_iff_mul_eq.mp hh
  · intro hfix
    apply hfu
    ext b
    change (u:D) * (b:D) * (u:D)⁻¹ = b
    rw [← hfix b b.property,mul_inv_cancel_right]

end Subgroup
end
