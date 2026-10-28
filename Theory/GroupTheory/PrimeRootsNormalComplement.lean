module
public import Theory.GroupTheory.PGroup.OddOmegaAutomorphisms
public import BenderSuzuki.External.Huppert.IV.theorem_5_4
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# Normal complements from central prime roots

For an odd prime p, a finite group whose elements of order p are central
has a normal p-complement. Induct on its order. The minimal non-p-nilpotent
normal-Sylow theorem reduces to a normal Sylow subgroup; a Hall complement
fixes its prime roots, hence acts trivially by odd-omega detection. The
complement is consequently normal.

In ambient p-rank at most two, every element of order p centralizing a
rank-two subgroup belongs to that subgroup, and is therefore central in
its centralizer. This gives the literal normal-complement conclusion used
in Aschbacher--Smith 13.4.7, printed p.901, where the source invokes the
Frobenius normal p-complement theorem. No solvability assumption is needed
for these two general group-theoretic statements.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Central prime roots force a normal complement at an odd prime. -/
theorem hasNormalPComplement_of_prime_roots_central
    (hp : p ≠ 2) (hc : ∀ x : G, x ^ p = 1 → x ∈ center G) :
    HasNormalPComplement p G := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_contra hnot
    have hdiv : p ∣ Nat.card G := by
      by_contra hn
      apply hnot
      refine ⟨⊤,inferInstance,?_,?_⟩
      · simpa using (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn
      · exact IsPGroup.of_card (n := 0) (by simp)
    let P : Sylow p G := default
    have hproper : ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → p ∣ Nat.card H →
        HasNormalPComplement p H := by
      intro H _ hH _
      have hlt : Nat.card H < n := by
        rw [←hcard]
        simpa using natCard_lt_of_subgroup_lt (lt_top_iff_ne_top.mpr hH)
      apply ih (Nat.card H) hlt (G := H) ?_ rfl
      intro x hx
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp (hc x (congrArg Subtype.val hx)) y)
    let : (P : Subgroup G).Normal :=
      BenderSuzuki.External.huppert_IV_5_4_a hproper hnot P hdiv
    obtain ⟨R,hR⟩ := exists_right_complement'_of_coprime (N := (P : Subgroup G))
      P.card_coprime_index
    have hcop : Nat.Coprime p (Nat.card R) := by
      rw [←hR.symm.index_eq_card]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index
    have hRC : R ≤ centralizer (P : Set G) := by
      intro r hr s hs
      let a := (MulAut.conjNormal : G →* MulAut (P : Subgroup G)) r
      have ha : a = 1 := MulAut.eq_one_of_coprime_of_fixes_prime_roots P.isPGroup' hp a
        ((hcop.of_dvd_right (R.orderOf_dvd_natCard hr)).of_dvd_right
          (orderOf_map_dvd (MulAut.conjNormal : G →* MulAut (P : Subgroup G)) r))
        (by
          intro x hx
          apply Subtype.ext
          change r * (x : G) * r⁻¹ = x
          rw [mem_center_iff.mp (hc x (congrArg Subtype.val hx)) r]
          simp [mul_assoc])
      have he := congrArg (fun b : MulAut (P : Subgroup G) => (b ⟨s,hs⟩ : G)) ha
      change r * s * r⁻¹ = s at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    let : R.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [←hR.sup_eq_top]
      exact sup_le ((le_centralizer_iff.mp hRC).trans (Subgroup.centralizer_le_normalizer _))
        le_normalizer))
    exact hnot ⟨R,inferInstance,hcop,P.isPGroup'.of_equiv hR.QuotientMulEquiv.symm⟩

/-- The centralizer of a full rank-two subgroup has a normal p-complement. -/
theorem centralizer_hasNormalPComplement_of_rank_two
    (hp : p ≠ 2) (U : Subgroup G) (hr : primeRank p G ≤ 2)
    (hU : primeRank p U = 2) :
    HasNormalPComplement p (centralizer (U : Set G)) := by
  apply hasNormalPComplement_of_prime_roots_central hp
  intro x hx
  have hm := U.mem_of_prime_pow_eq_one_of_centralizes_rank_two hr hU
    (congrArg Subtype.val hx) x.property
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (y.property x hm).symm
end Theory.GroupTheory
