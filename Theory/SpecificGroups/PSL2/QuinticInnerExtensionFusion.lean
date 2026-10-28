module

import all Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.ElementaryAbelian.Basic

/-!
# Inner elementary fusion in an actual normal PSL₂ component

An elementary subgroup centralizing a quintic subgroup inside odd PSL₂ is
cyclic. A Klein four in the supplied inner Sylow supplies another involution
which does not centralize the quintic subgroup. Inner involution conjugacy
therefore fuses the whole elementary group. The ambient quintic two-core
centralizes the quintic subgroup, so this conjugate escapes that original
core, even when the Sylow belongs to a larger automorphism extension.

This is the inner row of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem inner_centralizer_fusion
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (X : Subgroup PSL(2,F)) (T : Sylow 2 PSL(2,F)) (hc : Nat.card X = 5)
    (A : Subgroup PSL(2,F)) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAC : A ≤ centralizer (X : Set PSL(2,F))) :
    ∃ g : PSL(2,F), A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup PSL(2,F)) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ centralizer (X : Set PSL(2,F)) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic X := isCyclic_of_prime_card hc
  have hXne : X ≠ ⊥ := by intro hb; simp [hb] at hc
  have hXodd : Odd (Nat.card X) := by rw [hc]; decide
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hAne
  obtain ⟨a, ha, ha1⟩ := A.exists_ne_one_of_nontrivial
  have hpow (a : PSL(2,F)) (ha : a ∈ A) : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩)
  have haI : IsInvolution a := ⟨ha1, hpow a ha⟩
  have hAcyc : A = zpowers a := by
    apply le_antisymm
    · intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      by_cases hba : b = a
      · simp [hba]
      have hab : Commute a b := by
        exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
      obtain ⟨V, hVA, hV, _, _⟩ := exists_kleinFour_of_commuting_involutions_le A a b
        haI ⟨hb1, hpow b hb⟩ (Ne.symm hba) hab ha hb
      exact (psl2_no_kleinFour_centralizes_odd_cyclic F hF X V inferInstance hXne hXodd
        hV (hVA.trans hAC)).elim
    · exact zpowers_le.mpr ha
  obtain ⟨n, hn, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF T
  obtain ⟨V, hVT, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (T : Subgroup PSL(2,F)) hn e
  have hVC : ¬ V ≤ centralizer (X : Set PSL(2,F)) :=
    psl2_no_kleinFour_centralizes_odd_cyclic F hF X V inferInstance hXne hXodd hV
  obtain ⟨b, hb, hbC⟩ := Set.not_subset.mp hVC
  have hb1 : b ≠ 1 := by intro he; apply hbC; simp [he]
  have hb2 : b ^ 2 = 1 := by
    have hh := congrArg Subtype.val (hV.mul_self ⟨b, hb⟩)
    change b * b = 1 at hh
    simpa only [pow_two] using hh
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj a b
    (orderOf_eq_prime_iff.mpr ⟨haI.2, haI.1⟩)
    (orderOf_eq_prime_iff.mpr ⟨hb2, hb1⟩))
  have hmap : A.map (MulAut.conj g).toMonoidHom = zpowers b := by
    rw [hAcyc, MonoidHom.map_zpowers]
    congr 1
  refine ⟨g, ?_, ?_⟩
  · rw [hmap]
    exact zpowers_le.mpr (hVT hb)
  · rw [hmap]
    exact fun hh => hbC (hh (mem_zpowers b))


/-- If the whole elementary subgroup lies in the actual normal component,
one component conjugator returns it to the original Sylow outside O₂(XT). -/
theorem odd_quintic_inner_extension_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hc : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAN : A ≤ N) (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let X' := (X.subgroupOf N).map e.toMonoidHom
  let A' := (A.subgroupOf N).map e.toMonoidHom
  let j : PSL(2,F) →* G := N.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.symm.injective
  have hXmap : X'.map j = X := by
    rw [map_map]
    have he : j.comp e.toMonoidHom = N.subtype := by ext n; simp [j]
    rw [he, map_subgroupOf_eq_of_le hXN]
  have hAmap : A'.map j = A := by
    rw [map_map]
    have he : j.comp e.toMonoidHom = N.subtype := by ext n; simp [j]
    rw [he, map_subgroupOf_eq_of_le hAN]
  have hc' : Nat.card X' = 5 := by
    rw [card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv]
    exact hc
  have hA' : IsElementaryAbelian 2 A' := by
    let : IsElementaryAbelian 2 A := hA
    let : IsElementaryAbelian 2 (A.subgroupOf N) := IsElementaryAbelian.subgroupOf hAN
    exact IsElementaryAbelian.map e.toMonoidHom
  have hAne' : A' ≠ ⊥ := by
    intro he
    apply hAne
    rw [← hAmap, he, Subgroup.map_bot]
  have hSC := quintic_join_core_centralizes X T hc hTX
  have hAC : A' ≤ centralizer (X' : Set PSL(2,F)) := by
    intro a ha x hx
    apply hj
    rw [map_mul, map_mul]
    exact hSC (hAS (hAmap ▸ mem_map_of_mem j ha)) _ (hXmap ▸ mem_map_of_mem j hx)
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal N
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPT : (P : Subgroup PSL(2,F)).map j ≤ (T : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨n, hn, rfl⟩ := hv
    change (e.symm (e n) : G) ∈ (T : Subgroup G)
    rw [e.symm_apply_apply]
    rw [hQ] at hn
    exact hn
  obtain ⟨g, hgP, hgC⟩ := inner_centralizer_fusion hF X' P hc' A' hA' hAne' hAC
  have hmap : (A'.map (MulAut.conj g).toMonoidHom).map j =
      A.map (MulAut.conj (j g)).toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨j w, hAmap ▸ mem_map_of_mem j hw, ?_⟩
      change j g * j w * (j g)⁻¹ = j (g * w * g⁻¹)
      rw [map_mul, map_mul, map_inv]
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ : v ∈ A'.map j := hAmap.symm ▸ hv
      refine ⟨MulAut.conj g w, mem_map_of_mem _ hw, ?_⟩
      change j (g * w * g⁻¹) = j g * j w * (j g)⁻¹
      rw [map_mul, map_mul, map_inv]
  refine ⟨j g, (e.symm g).property, ?_, ?_⟩
  · rw [← hmap]
    exact (map_mono hgP).trans hPT
  · intro hh
    apply hgC
    intro v hv x hx
    apply hj
    rw [map_mul, map_mul]
    exact hSC (hh (hmap ▸ mem_map_of_mem j hv)) _ (hXmap ▸ mem_map_of_mem j hx)

end Theory.PSL2
