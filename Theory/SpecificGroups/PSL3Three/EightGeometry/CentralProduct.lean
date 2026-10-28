module
public import Theory.SpecificGroups.PSL3Three.EightGeometry.Transport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Elementary sixteens in a central involution product with Aut(PSL₃(3))

Let `H` be the internal direct product of a central involution `t` and an
actual carrier `A` of Aut(PSL₃(3)). Every elementary sixteen in `H` contains
`t` and is the product of its line with the elementary-eight intersection
with `A`. Consequently `A` is transitive on these sixteens by ambient
conjugation.

The inner index-two subgroup and the two-rank bound of PSL₃(3) bound
all elementary subgroups of `A` by eight. The factor `A` has index two in
`H`, giving the bound sixteen there. Adjoining an absent `t` would violate
that bound. Multiplication then gives the splitting, and the existing
elementary-eight conjugacy theorem supplies transitivity.

Source: Aschbacher--Smith, Lemma 2.5.15, printed p.559, the assertion that
the conjugates of `QE = 〈t〉 × F` are all elementary sixteens of `H`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Matrix.PSL3Three.EightGeometry
set_option backward.isDefEq.respectTransparency false

/-- The index-two inner subgroup bounds all elementary two-subgroups by eight. -/
theorem elementary_card_le_eight (B : Subgroup (MulAut PSL))
    (hB : IsElementaryAbelian 2 B) : Nat.card B ≤ 8 := by
  let : IsElementaryAbelian 2 B := hB
  let I := MulAut.innerSubgroup PSL
  let E := B ⊓ I
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  let e : PSL ≃* I := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot GraphWitnesses.EightCentralizers.psl_center_eq_bot)
  let D := E.subgroupOf I
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf inf_le_right
  have hd := (primeRank_le_iff_elementary_card_le PSL).mp
    (Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
      Nat.prime_three (by decide) (by simp))
    (D.map e.symm.toMonoidHom) (IsElementaryAbelian.map _)
  rw [card_map_of_injective e.symm.injective,
    Nat.card_congr (subgroupOfEquivOfLe (show E ≤ I from inf_le_right)).toEquiv] at hd
  have hi : I.relIndex B ≤ 2 := Nat.le_of_dvd (by decide)
    (inner_index_two ▸ I.relIndex_dvd_index_of_normal B)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (MulAut PSL)) E B bot_le inf_le_left
  simp only [relIndex_bot_left, E, inf_relIndex_left] at hh
  calc
    Nat.card B = Nat.card E * I.relIndex B := hh.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hd hi
    _ = 8 := rfl

/-- The elementary bound transported along the actual automorphism marking. -/
theorem elementary_card_le_eight_of_equiv {A : Type*} [Group A]
    (e : A ≃* MulAut PSL) (B : Subgroup A) (hB : IsElementaryAbelian 2 B) :
    Nat.card B ≤ 8 := by
  let : IsElementaryAbelian 2 B := hB
  have h := elementary_card_le_eight (B.map e.toMonoidHom) (IsElementaryAbelian.map _)
  rwa [card_map_of_injective e.injective] at h

variable {G : Type*} [Group G] [Finite G]

private theorem factor_relIndex_two (H A : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hH : H = zpowers t ⊔ A)
    (hd : Disjoint (zpowers t) A) (hc : zpowers t ≤ centralizer (A : Set G)) :
    A.relIndex H = 2 := by
  have hAH : A ≤ H := by rw [hH]; exact le_sup_right
  have he : Nat.card H = 2 * Nat.card A := by
    rw [hH, card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)) hd,
      Nat.card_zpowers, ht]
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) A H bot_le hAH
  simp only [relIndex_bot_left] at hh
  rw [he, Nat.mul_comm 2] at hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A)) hh

private theorem elementary_card_le_sixteen (H A B : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hH : H = zpowers t ⊔ A)
    (hd : Disjoint (zpowers t) A) (hc : zpowers t ≤ centralizer (A : Set G))
    (e : A ≃* MulAut PSL) (hBH : B ≤ H) (hB : IsElementaryAbelian 2 B) :
    Nat.card B ≤ 16 := by
  let : IsElementaryAbelian 2 B := hB
  let E := B ⊓ A
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  let : IsElementaryAbelian 2 (E.subgroupOf A) := IsElementaryAbelian.subgroupOf inf_le_right
  have hE := elementary_card_le_eight_of_equiv e (E.subgroupOf A) inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe (show E ≤ A from inf_le_right)).toEquiv] at hE
  have hAH := factor_relIndex_two H A t ht hH hd hc
  have hi := relIndex_le_of_le_right hBH (show A.relIndex H ≠ 0 by omega)
  rw [hAH] at hi
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) E B bot_le inf_le_left
  simp only [relIndex_bot_left, E, inf_relIndex_left] at hh
  calc
    Nat.card B = Nat.card E * A.relIndex B := hh.symm
    _ ≤ 8 * 2 := Nat.mul_le_mul hE hi
    _ = 16 := rfl

/-- Every elementary sixteen contains the central involution and splits over its
actual elementary-eight intersection with the automorphism factor. -/
theorem sixteen_split (H A B : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hH : H = zpowers t ⊔ A)
    (hd : Disjoint (zpowers t) A) (hc : zpowers t ≤ centralizer (A : Set G))
    (e : A ≃* MulAut PSL) (hBH : B ≤ H) (hB : IsElementaryAbelian 2 B)
    (hBc : Nat.card B = 16) :
    t ∈ B ∧ B = zpowers t ⊔ (B ⊓ A) ∧ Nat.card (B ⊓ A : Subgroup G) = 8 := by
  let : IsElementaryAbelian 2 B := hB
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htC : t ∈ centralizer (H : Set G) := by
    have hz : H ≤ centralizer (zpowers t : Set G) := by
      rw [hH]
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
        (le_centralizer_iff.mp hc)
    exact (le_centralizer_iff.mp hz) (mem_zpowers t)
  have htCB : t ∈ centralizer (B : Set G) := centralizer_le hBH htC
  have htB : t ∈ B := by
    by_contra hn
    let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
    have hJ : IsElementaryAbelian 2 (B ⊔ zpowers t : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htCB)
    have hjH : B ⊔ zpowers t ≤ H := sup_le hBH (by rw [hH]; exact le_sup_left)
    have hbound := elementary_card_le_sixteen H A (B ⊔ zpowers t) t ht hH hd hc e hjH hJ
    rw [card_sup_zpowers_of_normalizing_involution B t ht2 hn
      (centralizer_le_normalizer _ htCB), hBc] at hbound
    omega
  have hzB : zpowers t ≤ B := zpowers_le.mpr htB
  have hsplit : B = zpowers t ⊔ (B ⊓ A) := by
    apply le_antisymm ?_ (sup_le hzB inf_le_left)
    intro b hb
    have hprod : b ∈ (zpowers t : Set G) * (A : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left (zpowers t) A
        ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))]
      rw [← hH]
      exact hBH hb
    obtain ⟨z, hz, a, ha, rfl⟩ := hprod
    have haB : a ∈ B := by
      have hh := B.mul_mem (B.inv_mem (hzB hz)) hb
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem_sup hz ⟨haB, ha⟩
  refine ⟨htB, hsplit, ?_⟩
  have hcard : Nat.card B = 2 * Nat.card (B ⊓ A : Subgroup G) := by
    conv_lhs => rw [hsplit]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((inf_le_right.trans (le_centralizer_iff.mp hc)).trans (centralizer_le_normalizer _))
      (hd.mono_right inf_le_right), Nat.card_zpowers, ht]
  omega

/-- The automorphism factor is transitive on the elementary sixteens of the
central product, using conjugation in the original ambient group. -/
theorem sixteen_conjugate (H A B C : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hH : H = zpowers t ⊔ A)
    (hd : Disjoint (zpowers t) A) (hc : zpowers t ≤ centralizer (A : Set G))
    (e : A ≃* MulAut PSL) (hBH : B ≤ H) (hB : IsElementaryAbelian 2 B)
    (hBc : Nat.card B = 16) (hCH : C ≤ H) (hC : IsElementaryAbelian 2 C)
    (hCc : Nat.card C = 16) :
    ∃ a : A, B.map (MulAut.conj (a : G)).toMonoidHom = C := by
  obtain ⟨_, hBs, hBE⟩ := sixteen_split H A B t ht hH hd hc e hBH hB hBc
  obtain ⟨_, hCs, hCE⟩ := sixteen_split H A C t ht hH hd hc e hCH hC hCc
  let E := B ⊓ A
  let F := C ⊓ A
  let : IsElementaryAbelian 2 B := hB
  let : IsElementaryAbelian 2 C := hC
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_injective
    (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  let : IsElementaryAbelian 2 (E.subgroupOf A) := IsElementaryAbelian.subgroupOf inf_le_right
  let : IsElementaryAbelian 2 (F.subgroupOf A) := IsElementaryAbelian.subgroupOf inf_le_right
  obtain ⟨a, ha⟩ := eight_conjugate_of_equiv e (E.subgroupOf A) (F.subgroupOf A)
    inferInstance (by rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]; exact hBE)
    inferInstance (by rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]; exact hCE)
  have hEF : E.map (MulAut.conj (a : G)).toMonoidHom = F := by
    have hh := congrArg (fun K : Subgroup A => K.map A.subtype) ha
    rw [Subgroup.map_map] at hh
    have he : A.subtype.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (a : G)).toMonoidHom.comp A.subtype := rfl
    rw [he, ← Subgroup.map_map, map_subgroupOf_eq_of_le inf_le_right,
      map_subgroupOf_eq_of_le inf_le_right] at hh
    exact hh
  have hat : (MulAut.conj (a : G)).toMonoidHom t = t := by
    change (a : G) * t * (a : G)⁻¹ = t
    rw [hc (mem_zpowers t) (a : G) a.property, mul_inv_cancel_right]
  refine ⟨a, ?_⟩
  rw [hBs, hCs, Subgroup.map_sup, MonoidHom.map_zpowers, hat]
  exact congrArg (fun K => zpowers t ⊔ K) hEF
end Matrix.PSL3Three.EightGeometry
