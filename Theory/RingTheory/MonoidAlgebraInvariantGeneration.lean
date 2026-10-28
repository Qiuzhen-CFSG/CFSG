module

public import Theory.RingTheory.MonoidAlgebraOrbitSums
public import Theory.RingTheory.MonoidAlgebraHighestTerm
public import Mathlib.Tactic
/-!
# Generation of an invariant algebra by highest-term subtraction

Suppose every orbit-maximal weight has nonnegative integer height and
admits a monic invariant replacement in a given subalgebra. Every invariant
Laurent polynomial then lies in that subalgebra. The proof inducts first on
the greatest height and then on the number of terms at that height; subtracting
the replacement eliminates one top term. This remains valid in positive
characteristic, where other coefficients may cancel.

Source: Steinberg (1963), §3.9. The fundamental-orbit-sum application must
construct the replacements from the actual dominant-weight decomposition.
-/

open scoped BigOperators
open Theory.MonoidAlgebraOrbitSums Theory.MonoidAlgebraHighestTerm
public section
namespace Theory.MonoidAlgebraInvariantGeneration
variable {F G L : Type*} [Field F] [Group G] [CommGroup L]
  [MulDistribMulAction G L]

@[expose] def Invariant (p : MonoidAlgebra F L) : Prop :=
  ∀ g : G, algebraAction g p = p

lemma invariant_coeff {p : MonoidAlgebra F L} (hp : Invariant (G := G) p)
    (g : G) (a : L) : p.coeff (g • a) = p.coeff a := by
  have h := congrArg (fun q : MonoidAlgebra F L => q.coeff (g • a)) (hp g)
  change (MonoidAlgebra.domCongr F F (MulDistribMulAction.toMulEquiv L g) p).coeff _ = _ at h
  rw [MonoidAlgebra.coeff_domCongr] at h
  have he : (MulDistribMulAction.toMulEquiv L g).symm (g • a) = a :=
    (MulDistribMulAction.toMulEquiv L g).symm_apply_apply a
  rw [he] at h
  exact h.symm


/-- Highest-term replacement generates every finite invariant polynomial. -/
theorem invariant_mem_of_highest_replacements (d : L → ℤ)
    (A : Subalgebra F (MonoidAlgebra F L))
    (hpos : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) → 0 ≤ d a)
    (hreplace : ∀ a : L, (∀ g : G, d (g • a) ≤ d a) →
      ∃ q ∈ A, Invariant (G := G) q ∧ LeadingAt d q a)
    (p : MonoidAlgebra F L) (hp : Invariant (G := G) p) : p ∈ A := by
  classical
  have main : ∀ n : ℕ, ∀ p : MonoidAlgebra F L,
      Invariant (G := G) p → (∀ a ∈ p.coeff.support, d a ≤ (n : ℤ)) → p ∈ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro p hp hbound
      generalize hcount : (p.coeff.support.filter (fun a => d a = (n : ℤ))).card = k
      induction k using Nat.strong_induction_on generalizing p with
      | h k ihk =>
        by_cases hz : p = 0
        · simp [hz]
        have hne : p.coeff.support.Nonempty := by
          rw [Finsupp.support_nonempty_iff]
          intro h
          apply hz
          exact MonoidAlgebra.coeff_injective h
        obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image p.coeff.support d hne
        have hmaxorbit : ∀ g : G, d (g • a) ≤ d a := by
          intro g
          apply hmax
          rw [Finsupp.mem_support_iff, invariant_coeff hp g]
          exact Finsupp.mem_support_iff.mp ha
        have hdapos := hpos a hmaxorbit
        have hdan := hbound a ha
        by_cases he : d a = (n : ℤ)
        · obtain ⟨q, hqA, hqInv, hqLead⟩ := hreplace a hmaxorbit
          let c := p.coeff a
          let r := p - c • q
          have hrInv : Invariant (G := G) r := by
            intro g
            change algebraAction g (p - c • q) = p - c • q
            have hs : algebraAction g (c • q) = c • algebraAction g q :=
              (algebraAction g).toLinearEquiv.map_smul c q
            rw [map_sub, hs, hp g, hqInv g]
          have hrc (b : L) : r.coeff b = p.coeff b - c * q.coeff b := rfl
          have hrtop : r.coeff.support.filter (fun b => d b = (n : ℤ)) ⊂
              p.coeff.support.filter (fun b => d b = (n : ℤ)) := by
            apply Finset.ssubset_iff_subset_ne.mpr
            constructor
            · intro b hb
              obtain ⟨hbr, hbn⟩ := Finset.mem_filter.mp hb
              refine Finset.mem_filter.mpr ⟨?_, hbn⟩
              by_contra hbp
              have hpz : p.coeff b = 0 := Finsupp.notMem_support_iff.mp hbp
              have hqz : q.coeff b = 0 := by
                by_contra hqb
                have hba := hqLead.2.2 b (Finsupp.mem_support_iff.mpr hqb) (hbn.trans he.symm)
                subst b
                exact hbp ha
              exact (Finsupp.mem_support_iff.mp hbr) (by rw [hrc, hpz, hqz, mul_zero, sub_self])
            · intro hsame
              have hpa : a ∈ p.coeff.support.filter (fun b => d b = (n : ℤ)) :=
                Finset.mem_filter.mpr ⟨ha, he⟩
              have hra := (Finset.mem_filter.mp (hsame.symm ▸ hpa)).1
              exact (Finsupp.mem_support_iff.mp hra) (by rw [hrc, hqLead.1, mul_one]; exact sub_self _)
          have hrbound : ∀ b ∈ r.coeff.support, d b ≤ (n : ℤ) := by
            intro b hb
            by_cases hbp : b ∈ p.coeff.support
            · exact hbound b hbp
            · have hqb : b ∈ q.coeff.support := by
                by_contra hqb
                have hpz := Finsupp.notMem_support_iff.mp hbp
                have hqz := Finsupp.notMem_support_iff.mp hqb
                exact (Finsupp.mem_support_iff.mp hb) (by simp [hrc, hpz, hqz])
              exact (hqLead.2.1 b hqb).trans_eq he
          have hrA := ihk _ (by rw [← hcount]; exact Finset.card_lt_card hrtop)
            r hrInv hrbound rfl
          have hpEq : p = r + c • q := by simp only [r, sub_add_cancel]
          rw [hpEq]
          exact A.add_mem hrA (A.smul_mem hqA c)
        · have hlt : (d a).toNat < n := by omega
          apply ihn (d a).toNat hlt p hp
          intro b hb
          exact (hmax b hb).trans (by omega)
  let n := p.coeff.support.sup (fun a => (d a).toNat)
  apply main n p hp
  intro a ha
  have hn : (d a).toNat ≤ n := by
    change (d a).toNat ≤ p.coeff.support.sup (fun a => (d a).toNat)
    exact Finset.le_sup (f := fun a : L => (d a).toNat) ha
  omega
end Theory.MonoidAlgebraInvariantGeneration
