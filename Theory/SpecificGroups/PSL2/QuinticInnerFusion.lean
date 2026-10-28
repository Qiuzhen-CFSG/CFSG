module

public import Theory.SpecificGroups.PSL2.QuinticTwoPerfect
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import GorensteinWalter.PSL2KleinFourSelfCentralizer
public import GorensteinWalter.DihedralCore
public import GorensteinWalter.KleinFourOfCommutingInvolutions

/-!
# Whole elementary-subgroup fusion for inner quintic Sylow supplements

Inside odd-field PSL₂, a quintic two-perfect subgroup normalized by a Sylow
two-subgroup has order five. The two-core of their join centralizes that
subgroup. It contains no Klein four, whereas the Sylow subgroup does. Thus
every nontrivial elementary subgroup of that core is cyclic of order two
and can be conjugated, as a whole subgroup, into the original Sylow subgroup
outside the core. The conjugating element lies in the actual PSL₂ group.

This is the inner-action case of the final fusion step in Aschbacher--Smith
6.1.4, printed p.666. Outer field involutions require a further argument.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem quintic_join_core_centralizes
    {G : Type*} [Group G] [Finite G] (X T : Subgroup G)
    (hc : Nat.card X = 5) (hn : T ≤ normalizer X) :
    (X ⊔ T).pCoreIn 2 ≤ centralizer (X : Set G) := by
  let H := X ⊔ T
  let Y := X.subgroupOf H
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  have hYcard : Nat.card Y = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).toEquiv).trans hc
  have hY : IsPGroup 5 Y := IsPGroup.of_card (n := 1) (by simpa using hYcard)
  have hd : Disjoint (pCore 2 H) Y := IsPGroup.disjoint_of_coprime pCore_isPGroup hY (by decide)
  have hz : ⁅pCore 2 H, Y⁆ = ⊥ := commutator_eq_bot_of_disjoint hd
  have hcent := commutator_eq_bot_iff_le_centralizer.mp hz
  rintro s ⟨u, hu, rfl⟩ x hx
  exact congrArg Subtype.val (hcent hu ⟨x, (show X ≤ H from le_sup_left) hx⟩ hx)

/-- Every nontrivial elementary subgroup of the quintic supplement's
actual two-core has a whole-subgroup PSL₂ conjugate in the original Sylow
subgroup which escapes that two-core. -/
theorem odd_quintic_inner_elementary_fusion
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (X : Subgroup PSL(2,F)) (T : Sylow 2 PSL(2,F))
    (hX : IsPPerfect 2 X) (hfive : Nat.card (X ⧸ pCore 2 X) = 5)
    (hTX : (T : Subgroup PSL(2,F)) ≤ normalizer X)
    (A : Subgroup PSL(2,F)) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ (X ⊔ (T : Subgroup PSL(2,F))).pCoreIn 2) :
    ∃ g : PSL(2,F),
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup PSL(2,F)) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤
        (X ⊔ (T : Subgroup PSL(2,F))).pCoreIn 2 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc := (odd_twoPerfect_quintic_subgroup hF X hX hfive).2
  let : IsCyclic X := isCyclic_of_prime_card hc
  have hXne : X ≠ ⊥ := by intro hb; simp [hb] at hc
  have hXodd : Odd (Nat.card X) := by rw [hc]; decide
  let S := (X ⊔ (T : Subgroup PSL(2,F))).pCoreIn 2
  have hSC : S ≤ centralizer (X : Set PSL(2,F)) := quintic_join_core_centralizes X T hc hTX
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
        hV (hVA.trans (hAS.trans hSC))).elim
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
    exact fun hh => hbC (hSC (hh (mem_zpowers b)))

end Theory.PSL2
