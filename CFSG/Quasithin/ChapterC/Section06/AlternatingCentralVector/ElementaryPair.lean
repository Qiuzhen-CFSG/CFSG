module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.DerivedLine
public import Theory.GroupTheory.PrimeIndexCentralizer
public import Theory.GroupTheory.PGroup.ThompsonPairNormalizer

/-!
# The two maximum elementary subgroups and the normalizer index

Two elementary subgroups of index two covering R cover all involutions:
an involution outside the first must lie in the second. Any elementary
subgroup therefore lies in one of them. This proves the exact maximum
family; C.6.4(II) and its permutation action give |NΛ(R):R|=2.
The application removes the last premise of the C.6.3 structural theorem.

Source: Aschbacher–Smith C.6.4(3)–(5), printed pp.167–168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

omit [Finite G] in
private theorem elementary_pair_cover (P A B U : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hgen : P = B ⊔ A) (hAP : A ≤ P) (hBP : B ≤ P)
    (hbi : B.relIndex P = 2) (hUP : U ≤ P)
    (hA : A = P ⊓ centralizer (U : Set G)) :
    ∀ E : Subgroup G, E ≤ P → IsElementaryAbelian 2 E → E ≤ A ∨ E ≤ B := by
  have hinv (t : G) (ht : t ∈ P) (ht2 : t ^ 2 = 1) : t ∈ A ∨ t ∈ B := by
    by_cases htA : t ∈ A
    · exact Or.inl htA
    right
    have hn : A ≤ normalizer (B : Set G) := by
      let : (B.subgroupOf P).Normal := normal_of_index_eq_two hbi
      exact hAP.trans ((normal_subgroupOf_iff_le_normalizer hBP).mp inferInstance)
    have htin : t ∈ B ⊔ A := hgen ▸ ht
    obtain ⟨b,hb,a,ha,rfl⟩ := (show ∃ b ∈ B, ∃ a ∈ A, b * a = t from by
      change t ∈ ((B ⊔ A : Subgroup G) : Set G) at htin
      rwa [coe_mul_of_right_le_normalizer_left B A hn] at htin)
    have hb2 : b * b = 1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
    have ha2 : a * a = 1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
    have hab : a * b = b * a := by
      have hinv : (b * a)⁻¹ = b * a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
      rw [mul_inv_rev,inv_eq_of_mul_eq_one_left ha2,inv_eq_of_mul_eq_one_left hb2] at hinv
      exact hinv
    have hbA : b ∉ A := fun h => htA (A.mul_mem h ha)
    have haB : a ∈ B := by
      by_contra haB
      have hg : B ⊔ zpowers a = P := sup_zpowers_eq_of_relIndex_prime hBP Nat.prime_two hbi (hAP ha) haB
      have hbc : b ∈ centralizer (P : Set G) := by
        rw [← hg]
        have hsub : B ⊔ zpowers a ≤ centralizer ({b} : Set G) := by
          refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab))
          intro c hc
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hc hb)
        intro p hp
        exact mem_centralizer_singleton_iff.mp (hsub hp)
      exact hbA (hA ▸ ⟨hBP hb,centralizer_le hUP hbc⟩)
    exact B.mul_mem hb haB
  intro E hEP hE
  let := hE
  by_cases hEA : E ≤ A
  · exact Or.inl hEA
  right
  obtain ⟨a,ha,haA⟩ := SetLike.not_le_iff_exists.mp hEA
  have haB := (hinv a (hEP ha) (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)).resolve_left haA
  intro b hb
  by_contra hbB
  have hbA := (hinv b (hEP hb) (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb)).resolve_right hbB
  have habE := E.mul_mem ha hb
  rcases hinv (a*b) (hEP habE) (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a*b) habE) with h | h
  · exact haA ((A.mul_mem_cancel_right hbA).mp h)
  · exact hbB ((B.mul_mem_cancel_left haB).mp h)

theorem Input.exists_maximum_elementary_pair (d : Input K R S Λ) :
    let Q := (K ⊔ S).pCoreIn 2
    ∃ x ∈ Λ ⊓ normalizer (R : Set G),
      elementaryAbelianMaxSubgroups R = {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let Q := (K ⊔ S).pCoreIn 2
  let U := (blockU K).map K.subtype
  obtain ⟨x,hx,_,_,_,_,_,hE,hgen⟩ := d.exists_elementary_factorization
  let B := Q.map (MulAut.conj x⁻¹).toMonoidHom
  let := hE
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hRmap : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx.2)
  have hBR : B ≤ R := (map_mono d.core_le).trans_eq hRmap
  have hqi : Q.relIndex R = 2 := by
    let := d.core_normal_in_R
    let := d.quotient_elementary_rank_one.1
    rw [c6_3_order_of_elementary_quotient, d.quotient_elementary_rank_one.2]
    rfl
  have hbi : B.relIndex R = 2 := by
    rw [← hRmap,relIndex_map_map_of_injective Q R (MulAut.conj x⁻¹).injective,hqi]
  refine ⟨x,hx,maxFamily_eq_pair_of_cover R Q B d.core_le hBR ?_ ?_⟩
  · exact (card_map_of_injective (MulAut.conj x⁻¹).injective).symm
  · intro E hE'
    apply elementary_pair_cover R Q B U
      (hgen.trans (sup_comm Q B)) d.core_le hBR hbi (d.module_le_core.trans d.core_le)
      d.core_eq_centralizer E hE'.1 hE'.2.1

theorem Input.normalizer_index (d : Input K R S Λ) :
    R.relIndex (Λ ⊓ normalizer (R : Set G)) = 2 := by
  obtain ⟨x,_,hpair⟩ := d.exists_maximum_elementary_pair
  have hne : (K ⊔ S).pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hU := d.module_le_core
    rw [hh] at hU
    exact d.block.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      ((bot_unique hU).trans (map_bot K.subtype).symm))
  exact (twoGroup_normalizer_index_two_of_maxFamily_pair Λ R ((K ⊔ S).pCoreIn 2) _
    d.Λ_two d.proper hpair (d.control _ hne d.core_le d.normalizes_core)).1

/-- The source obstruction identifies the overlap S ∩ Λ with R. -/
theorem Input.S_inf_Λ (d : Input K R S Λ) : S ⊓ Λ = R := by
  have hne : (blockU K).map K.subtype ≠ ⊥ := by
    intro he
    exact d.block.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      (he.trans (map_bot K.subtype).symm))
  apply le_antisymm ?_ (le_inf d.R_le_S d.proper.le)
  rw [← d.control _ hne (d.module_le_core.trans d.core_le) d.normalizes_module]
  exact le_inf inf_le_right (inf_le_left.trans (le_sup_right.trans d.normalizes_module))

/-- The complete structural C.6.3 conclusion on the original input, with both
its geometric minimum and normalizer-index premises discharged. -/
theorem Input.source_structural_factorization (d : Input K R S Λ) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ S,
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      R = (U ⊔ U.map (MulAut.conj x⁻¹ : G →* G)) ⊔
        (R ⊓ centralizer ((U ⊔ U.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G)) ∧
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  apply d.structural_factorization_of_index
  rw [d.S_inf_Λ]
  exact d.normalizer_index

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
