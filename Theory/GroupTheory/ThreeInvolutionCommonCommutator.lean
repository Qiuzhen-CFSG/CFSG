module
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A common-commutator core of three involutions

Three involutions with the same nontrivial involutory commutator form the
order-sixteen central product used for the first local 2-core in the
radius-two Goldschmidt branch. The proof factors two generators through a
dihedral group of order eight, then adjoins the third normalizing involution.
-/

public section
open Subgroup
open scoped commutatorElement
namespace ThreeInvolutionCommonCommutator
variable {G : Type*} [Group G]

private theorem dihedral_no_triple : ∀ a b c : DihedralGroup 4,
    a ^ 2 = 1 → b ^ 2 = 1 → c ^ 2 = 1 → ⁅a,b⁆ ≠ 1 →
      ⁅a,c⁆ = ⁅a,b⁆ → ⁅b,c⁆ = ⁅a,b⁆ → False := by decide

/-- Three involutions with the same nonidentity commutator of order two
 generate a group of order sixteen. This is the first core in Gol80 (6.9). -/
theorem card_closure_eq_sixteen (a b c z : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hz : orderOf z = 2)
    (hab : ⁅a,b⁆ = z) (hac : ⁅a,c⁆ = z) (hbc : ⁅b,c⁆ = z) :
    Nat.card (closure ({a,b,c} : Set G)) = 16 := by
  classical
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hc)
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzne : z ≠ 1 := by intro he; simp [he] at hz
  let r := a * b
  have hr2 : r ^ 2 = z := by
    simpa only [commutatorElement_def, hai, hbi, pow_two, mul_assoc, r] using hab
  have hr : orderOf r = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hr2] using hzne
    · simpa only [show 2^(1+1)=2*2 by decide, pow_mul, hr2] using hz2
  have har : a * r * a⁻¹ = r⁻¹ := by
    dsimp [r]
    rw [mul_inv_rev, hbi, ← mul_assoc, ← pow_two, ha, one_mul]
  have haout : a ∉ zpowers r := by
    rintro ⟨k, he⟩
    have hec : Commute a r := he ▸ (Commute.refl r).zpow_left k
    have hri : r⁻¹ = r := har.symm.trans (by rw [hec.eq, mul_inv_cancel_right])
    have hs : r ^ 2 = 1 := by
      calc
        r ^ 2 = r⁻¹ * r := by rw [pow_two, hri]
        _ = 1 := inv_mul_cancel r
    exact hzne (hr2.symm.trans hs)
  obtain ⟨hH, ⟨eH⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion
    (by decide : 0 < 4) r a hr ha haout har
  let H := zpowers r ⊔ zpowers a
  have haH : a ∈ H := mem_sup_right (mem_zpowers a)
  have hrH : r ∈ H := mem_sup_left (mem_zpowers r)
  have hbH : b ∈ H := by
    have hh := H.mul_mem (H.inv_mem haH) hrH
    simpa only [r, inv_mul_cancel_left] using hh
  have hzH : z ∈ H := hr2 ▸ H.pow_mem hrH 2
  have hcnot : c ∉ H := by
    intro hcH
    let aa : H := ⟨a,haH⟩
    let bb : H := ⟨b,hbH⟩
    let cc : H := ⟨c,hcH⟩
    apply dihedral_no_triple (eH aa) (eH bb) (eH cc)
    · rw [← map_pow, show aa ^ 2 = 1 from Subtype.ext ha, map_one]
    · rw [← map_pow, show bb ^ 2 = 1 from Subtype.ext hb, map_one]
    · rw [← map_pow, show cc ^ 2 = 1 from Subtype.ext hc, map_one]
    · intro he
      apply hzne
      have hh : ⁅aa,bb⁆ = (1 : H) := eH.injective (by
        rw [map_commutatorElement, map_one]
        exact he)
      exact hab.symm.trans (congrArg Subtype.val hh)
    · rw [← map_commutatorElement, ← map_commutatorElement]
      exact congrArg eH (Subtype.ext (hac.trans hab.symm))
    · rw [← map_commutatorElement, ← map_commutatorElement]
      exact congrArg eH (Subtype.ext (hbc.trans hab.symm))
  have hpair : H = closure ({a,b} : Set G) := by
    apply le_antisymm
    · apply sup_le
      · exact zpowers_le.mpr (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
      · exact zpowers_le.mpr (subset_closure (by simp))
    · apply (closure_le _).mpr
      intro x hx
      rcases hx with rfl | rfl
      · exact haH
      · exact hbH
  have hcN : c ∈ normalizer H := by
    have hec (w : G) (hw : ⁅w,c⁆ = z) : c * w * c⁻¹ = z⁻¹ * w := by
      have he : w * (c * w⁻¹ * c⁻¹) = z := by
        simpa only [commutatorElement_def, mul_assoc] using hw
      have he' := congrArg Inv.inv he
      simp only [mul_inv_rev, inv_inv, mul_assoc] at he'
      calc
        c * w * c⁻¹ = (c * w * c⁻¹ * w⁻¹) * w := by group
        _ = z⁻¹ * w := by rw [← he']; group
    have hN : zpowers c ≤ normalizer H := by
      rw [hpair]
      apply le_normalizer_closure_iff.mpr
      intro g hg w hw
      have hg' : g = 1 ∨ g = c := by
        have ho : orderOf c = 2 := orderOf_eq_prime hc (fun hh => hcnot (hh ▸ H.one_mem))
        have hfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hc⟩
        rw [hfin.mem_zpowers_iff_mem_range_orderOf, ho] at hg
        obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hg
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i <;> simp_all
      rcases hg' with rfl | rfl
      · simp only [one_mul, inv_one, mul_one]
        exact Subgroup.subset_closure hw
      · rw [← hpair]
        rcases hw with hwa | hwb
        · rw [hwa, hec a hac]
          exact H.mul_mem (H.inv_mem hzH) haH
        · rw [Set.mem_singleton_iff.mp hwb, hec b hbc]
          exact H.mul_mem (H.inv_mem hzH) hbH
    exact hN (mem_zpowers c)
  have htriple : closure ({a,b,c} : Set G) = H ⊔ zpowers c := by
    rw [hpair, zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [htriple, card_sup_zpowers_of_normalizing_involution H c hc hcnot hcN, hH]

end ThreeInvolutionCommonCommutator
