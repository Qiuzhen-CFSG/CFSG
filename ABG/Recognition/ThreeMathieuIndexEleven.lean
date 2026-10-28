module

public import ABG.Recognition.ThreeMathieuIndexBounds
public import ABG.Recognition.ThreeMathieuOddClasses
public import Theory.GroupAction.PrimeSylowFaithful
public import Theory.GroupAction.QuaternionEight

/-!
# The index-eleven subgroup in Wong's Mathieu branch

A proper subgroup containing the Sylow-five normalizer and a quaternion
subgroup of order eight has index eleven. The index bound leaves eleven or
sixty-six. In the latter case the subgroup has order 120 and six Sylow-five
subgroups. Their conjugation action is faithful, since the Sylow subgroup
has prime order and is self-centralizing. Restricting this action to the
quaternion subgroup contradicts its minimum faithful degree of eight.

This argument assumes the local subgroups have already been constructed.
Source: Wong (1964), Theorem 6(a), p.108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G]

/-- An order-120 subgroup containing the specified Sylow-five normalizer
cannot contain a quaternion subgroup of order eight. -/
public theorem mathieu_subgroup_card_ne_120
    (P : Sylow 5 G) (hP : Nat.card P = 5)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hN : Nat.card (Subgroup.normalizer (P : Set G)) = 20)
    (Q M : Subgroup G) (e : Q ≃* QuaternionGroup 2) (hQM : Q ≤ M)
    (hNM : Subgroup.normalizer (P : Set G) ≤ M) : Nat.card M ≠ 120 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hM
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  let R : Sylow 5 M := P.subtype hPM
  have hR : Nat.card R = 5 := by
    rw [Sylow.coe_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv]
    exact hP
  have hnorm : Subgroup.normalizer (R : Set M) =
      (Subgroup.normalizer (P : Set G)).subgroupOf M := by
    change Subgroup.normalizer (((P.subtype hPM) : Subgroup M) : Set M) = _
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hPM]
    simp only [Sylow.coe_coe]
  have hnormcard : Nat.card (Subgroup.normalizer (R : Set M)) = 20 := by
    rw [hnorm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, hN]
  have hcent : Subgroup.centralizer (R : Set M) ≤ (R : Subgroup M) := by
    intro x hx
    change (x : G) ∈ (P : Subgroup G)
    rw [← hC]
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have heq := Subgroup.mem_centralizer_iff.mp hx ⟨y, hPM hy⟩
      (show (⟨y, hPM hy⟩ : M) ∈ (R : Subgroup M) from hy)
    exact congrArg Subtype.val heq
  have hproper : Subgroup.normalizer (R : Set M) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hM] at hnormcard
    omega
  have hcount : Nat.card (Sylow 5 M) = 6 := by
    rw [R.card_eq_index_normalizer]
    have hprod := (Subgroup.normalizer (R : Set M)).index_mul_card
    rw [hnormcard, hM] at hprod
    omega
  let ρ := MulAction.toPermHom M (Sylow 5 M)
  have hρ : Function.Injective ρ :=
    R.toPermHom_injective_of_prime_card_self_centralizing hR hcent hproper
  let f : QuaternionGroup 2 →* Equiv.Perm (Sylow 5 M) :=
    ρ.comp ((Subgroup.inclusion hQM).comp e.symm.toMonoidHom)
  have hf : Function.Injective f :=
    hρ.comp ((Subgroup.inclusion_injective hQM).comp e.symm.injective)
  have hbound := QuaternionGroup.eight_le_card_of_injective_permHom f hf
  omega

/-- Wong's quaternion overgroup of the Sylow-five normalizer has index eleven. -/
public theorem ThreeGlobalDegreeData.mathieu_index_eleven [IsSimpleGroup G]
    (c : ThreeGlobalDegreeData G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S) (hG : Nat.card G = 7920)
    (P : Sylow 5 G) (Q M : Subgroup G) (e : Q ≃* QuaternionGroup 2)
    (hQM : Q ≤ M) (hNM : Subgroup.normalizer (P : Set G) ≤ M) (hM : M ≠ ⊤) :
    M.index = 11 := by
  have hN := c.mathieu_sylow_five_normalizer_card S hS hG P
  have hQ : Nat.card Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rcases mathieu_index_eleven_or_sixtysix hG P Q M hQ hQM hN hNM hM with h | h
  · exact h
  · have hcard := M.card_mul_index
    rw [h, hG] at hcard
    exact (mathieu_subgroup_card_ne_120 P (mathieu_sylow_five_card hG P)
      (c.mathieu_sylow_five_self_centralizing S hS hG P) hN Q M e hQM hNM
      (by omega)).elim

end ABG
