module

public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Characteristic two of GL₂(3)

An odd normal subgroup has only the identity and the unipotent class
available in the checked conjugacy table. Two explicit conjugates of a
unipotent have a product whose square is −I, excluding the unipotent class.
Thus the odd core is trivial. Solvability and the self-centralizing Fitting
subgroup theorem now give C(O₂(GL₂(3))) ≤ O₂(GL₂(3)).

This is the intrinsic centralizer calculation used for M11 in
Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4. The concrete conjugacy
representatives and solvability proofs retain their own source references.
-/

namespace Matrix.GeneralLinearGroup
open Subgroup
private abbrev G := GL (Fin 2) (ZMod 3)

private theorem three_oddCore_eq_bot : pPrimeCore 2 G = ⊥ := by
  let N := pPrimeCore 2 G
  have hord : ∀ x ∈ N, Nat.Coprime 2 (orderOf x) := by
    intro x hx
    have hd : orderOf x ∣ Nat.card N := by
      rw [Subgroup.orderOf_coe (⟨x, hx⟩ : N)]
      exact orderOf_dvd_natCard (⟨x, hx⟩ : N)
    exact Nat.Coprime.of_dvd_right hd (pPrimeCore_coprime_card (p := 2) (G := G))
  have hnot : threeUnipotent ∉ N := by
    intro hr
    have hr' := (inferInstance : N.Normal).conj_mem threeUnipotent hr threeRotation
    have hprod := N.pow_mem (N.mul_mem hr hr') 2
    have heq : (threeUnipotent *
        (threeRotation * threeUnipotent * threeRotation⁻¹)) ^ 2 = threeCentral := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq] at hprod
    have hbad := hord _ hprod
    have ho : orderOf threeCentral = 2 := three_conjugacy_data.2.1 1
    rw [ho] at hbad
    norm_num at hbad
  apply bot_unique
  intro x hx
  obtain ⟨i, hi, -⟩ := three_conjugacy_data.1 x
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have hmem : threeClassRepr i ∈ N :=
    hg ▸ (inferInstance : N.Normal).conj_mem x hx g
  have hcop := hord _ hmem
  rw [three_conjugacy_data.2.1] at hcop
  fin_cases i <;> norm_num at hcop
  · change x = 1
    have hh : g * x * g⁻¹ = 1 := hg
    simpa [mul_assoc] using (congrArg (fun y => g⁻¹ * y * g) hh)
  · exact False.elim (hnot hmem)

/-- The actual general linear group GL₂(3) has self-centralizing two-core. -/
public theorem three_centralizer_twoCore_le :
    centralizer (pCore 2 (GL (Fin 2) (ZMod 3)) : Set (GL (Fin 2) (ZMod 3))) ≤
      pCore 2 (GL (Fin 2) (ZMod 3)) := by
  have h := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable three_isSolvable
  rwa [Fitting_eq_pcore G 2 three_oddCore_eq_bot] at h
end Matrix.GeneralLinearGroup
