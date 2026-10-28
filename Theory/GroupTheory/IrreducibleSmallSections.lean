module
public import Theory.GroupTheory.IrreducibleFourResidual
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Fixed points and movement in small irreducible sections

An element fixed by the actor lies in the denominator of an irreducible
abelian section whenever its order is smaller than the section index:
adjoining it gives an invariant intermediate subgroup of too small an index.
Conversely, a four-group fully moved by a two-perfect actor is irreducible,
since a proper invariant subgroup has order two and would force the whole
action to be trivial.

Source application: the original L₀-fixed subgroup and restricted parabolic
in Aschbacher--Smith, proof of 12.9.4, printed p.860 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A fixed element whose order is smaller than an irreducible abelian
section lies in that section's denominator. -/
theorem fixed_mem_of_irreducible_abelian_section
    (A K R : Subgroup G) [IsMulCommutative A]
    (hKA : K ≤ A) (hRK : R ≤ normalizer (K : Set G))
    (hirr : ∀ J : Subgroup G, K ≤ J → J ≤ A →
      R ≤ normalizer (J : Set G) → J = K ∨ J = A)
    {x : G} (hxA : x ∈ A) (hxR : x ∈ centralizer (R : Set G))
    {m : ℕ} (hm : 0 < m) (hpow : x ^ m = 1) (hindex : m < K.relIndex A) :
    x ∈ K := by
  have hcycA : zpowers x ≤ A := zpowers_le.mpr hxA
  have hRcyc : R ≤ normalizer (zpowers x : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxR r hr)
  have hKcyc : K ≤ normalizer (zpowers x : Set G) :=
    hKA.trans ((le_centralizer_iff.mp
      (hcycA.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hj := hirr (K ⊔ zpowers x) le_sup_left (sup_le hKA hcycA)
    ((le_inf hRK hRcyc).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
  rcases hj with hj | hj
  · exact hj ▸ (mem_sup_right (mem_zpowers x))
  · have hbound : K.relIndex (K ⊔ zpowers x) ≤ m := by
      rw [sup_comm,relIndex_sup_of_normalizes _ _ hKcyc]
      apply (Nat.le_of_dvd (Nat.card_pos) (relIndex_dvd_card K (zpowers x))).trans
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hm (orderOf_dvd_of_pow_eq_one hpow)
    rw [hj] at hbound
    exact False.elim (hindex.not_ge hbound)

/-- A four-group fully moved by a two-perfect actor is irreducible. -/
theorem four_irreducible_of_twoPerfect_moved
    (R D : Subgroup G) (hR : IsPPerfect 2 R) (hD : Nat.card D = 4)
    (hRD : R ≤ normalizer (D : Set G)) (hmove : ⁅D,R⁆ = D) :
    ∀ A : Subgroup G, A ≤ D → R ≤ normalizer (A : Set G) → A = ⊥ ∨ A = D := by
  intro A hAD hRA
  by_cases hb : A = ⊥
  · exact Or.inl hb
  by_cases he : A = D
  · exact Or.inr he
  have hA : Nat.card A = 2 := by
    have hlo := (one_lt_card_iff_ne_bot A).mpr hb
    have hhi : Nat.card A < Nat.card D := lt_of_le_of_ne (card_le_of_le hAD)
      (fun hh => he (eq_of_le_of_card_ge hAD hh.ge))
    have hd := card_dvd_of_le hAD
    rw [hD] at hhi hd
    have hne3 : Nat.card A ≠ 3 := by intro hh; rw [hh] at hd; norm_num at hd
    omega
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
  have hfix : R ≤ centralizer (A : Set G) :=
    hRA.trans (normalizer_le_centralizer_of_card_two A hA)
  have hc := twoPerfect_centralizes_four_of_fixed_point R D hR hD hRD
    ⟨z,hAD z.property⟩ (fun hh => hz (Subtype.ext (congrArg (fun x : D => (x:G)) hh)))
    (by intro r hr; exact mul_inv_eq_iff_eq_mul.mpr (hfix hr z z.property).symm)
  have hzD : D = ⊥ := hmove.symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  rw [hzD,card_bot] at hD
  contradiction
end Subgroup
