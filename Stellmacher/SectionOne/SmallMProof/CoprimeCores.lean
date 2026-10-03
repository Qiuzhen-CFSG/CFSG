module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction

/-!
# Cores of coprime complements

For a normal odd complement and an elementary abelian Sylow subgroup, centralizer and commutator conditions identify the two-core, odd core and quotient odd core. Coprime commutator idempotence supplies the recursive commutator equality.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

public theorem pCore_eq_of_normal_coprime_complement
    {H : Type u} [Group H] [Finite H]
    (N S A : Subgroup H) [N.Normal] [A.Normal]
    (hcomp : N.IsComplement' S)
    (hSp : IsPGroup 2 S)
    (hNcop : Nat.Coprime 2 (Nat.card N))
    (hAS : A ≤ S)
    (hcent : S ⊓ Subgroup.centralizer (N : Set H) = A) :
    pCore 2 H = A := by
  have hSindex : ¬ 2 ∣ S.index := by
    rw [hcomp.index_eq_card]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 2)).1 hNcop
  let S_syl : Sylow 2 H := hSp.toSylow hSindex
  have hcoreS : pCore 2 H ≤ S := by
    simpa [S_syl] using
      (pCore_isPGroup (G := H) (p := 2)).le_sylow_of_normal S_syl
  obtain ⟨n, hn⟩ := (pCore_isPGroup (G := H) (p := 2)).exists_card_eq
  have hcoreNcop : Nat.Coprime (Nat.card (pCore 2 H)) (Nat.card N) := by
    rw [hn]
    exact hNcop.pow_left n
  have hdisj : Disjoint (pCore 2 H) N :=
    Subgroup.disjoint_of_coprime_natCard hcoreNcop
  have hcoreCentN : pCore 2 H ≤ Subgroup.centralizer (N : Set H) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf
        (H₁ := pCore 2 H) (H₂ := N)).trans (by
          rw [hdisj.eq_bot])
    · exact bot_le
  apply le_antisymm
  · intro x hx
    have hxinf : x ∈ S ⊓ Subgroup.centralizer (N : Set H) :=
      ⟨hcoreS hx, hcoreCentN hx⟩
    rwa [hcent] at hxinf
  · exact le_sSup ⟨inferInstance, hSp.to_le hAS⟩

private theorem pPrimeCore_eq_of_normal_coprime_complement
    {H : Type u} [Group H] [Finite H]
    (N S : Subgroup H) [N.Normal]
    (hcomp : N.IsComplement' S)
    (hSp : IsPGroup 2 S)
    (hNcop : Nat.Coprime 2 (Nat.card N)) :
    pPrimeCore 2 H = N := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hQp : IsPGroup 2 (H ⧸ N) :=
    hSp.of_equiv hcomp.symm.QuotientMulEquiv.symm
  let Kbar : Subgroup (H ⧸ N) := (pPrimeCore 2 H).map q
  have hKbarp : IsPGroup 2 Kbar := hQp.to_subgroup Kbar
  have hKbarcop : Nat.Coprime 2 (Nat.card Kbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := pPrimeCore 2 H) q)
      pPrimeCore_coprime_card
  have hKbarcard : Nat.card Kbar = 1 := by
    rcases hKbarp.card_eq_or_dvd with hcard | hdvd
    · exact hcard
    · exact False.elim
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 2)).1 hKbarcop hdvd)
  have hKbarbot : Kbar = ⊥ := (Subgroup.card_eq_one (H := Kbar)).1 hKbarcard
  apply le_antisymm
  · have hleker : pPrimeCore 2 H ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (f := q) (H := pPrimeCore 2 H)).1
        (by simpa [Kbar] using hKbarbot)
    simpa [q, QuotientGroup.ker_mk'] using hleker
  · exact le_sSup ⟨inferInstance, hNcop⟩

public theorem pPrimeCore_quotient_eq_map_of_normal_coprime_complement
    {H : Type u} [Group H] [Finite H]
    (N S A : Subgroup H) [N.Normal] [A.Normal]
    (hAS : A ≤ S) (hcomp : N.IsComplement' S)
    (hSp : IsPGroup 2 S) (hNcop : Nat.Coprime 2 (Nat.card N)) :
    pPrimeCore 2 (H ⧸ A) = N.map (QuotientGroup.mk' A) := by
  let q : H →* H ⧸ A := QuotientGroup.mk' A
  let Nbar := N.map q
  let Sbar := S.map q
  let : Nbar.Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) q
      (QuotientGroup.mk'_surjective A)
  have hcompbar : Nbar.IsComplement' Sbar := by
    exact (isComplement'_map_mk'_of_le_isComplement' S N A hAS hcomp.symm).symm
  have hSbarp : IsPGroup 2 Sbar := hSp.map q
  have hNbarcop : Nat.Coprime 2 (Nat.card Nbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := N) q) hNcop
  exact pPrimeCore_eq_of_normal_coprime_complement
    Nbar Sbar hcompbar hSbarp hNbarcop

public theorem commutator_idempotent_of_solvable_coprime
    {G : Type u} [Group G] [Finite G] (C S : Subgroup G)
    (hSnormC : S ≤ Subgroup.normalizer (C : Set G))
    (hCsolv : Group.IsSolvable C)
    (hcop : Nat.Coprime (Nat.card S) (Nat.card C)) :
    ⁅⁅C, S⁆, S⁆ = ⁅C, S⁆ := by
  classical
  let : Subgroup.Normalizes S C := ⟨hSnormC⟩
  let D : Subgroup C := commutatorAction (A := S) (G := C)
  have hDmap : D.map C.subtype = ⁅C, S⁆ := by
    exact commutatorAction_subgroup_conj_map_eq_commutator C S hSnormC
  have hidem : commutatorAction₂ (A := S) (G := C) = D :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime hCsolv hcop
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.normalizer_commutator_ge_right C S)
  · have htarget :
        (commutatorAction₂ (A := S) (G := C)).map C.subtype ≤ ⁅⁅C, S⁆, S⁆ := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le (K := (⁅⁅C, S⁆, S⁆).comap C.subtype)).2 ?_
      rintro d ⟨s, c, hcD, rfl⟩
      have hcW : (c : G) ∈ ⁅C, S⁆ := by
        rw [← hDmap]
        exact ⟨c, hcD, rfl⟩
      have hcomm : ⁅(c : G)⁻¹, (s : G)⁆ ∈ ⁅⁅C, S⁆, S⁆ :=
        Subgroup.commutator_mem_commutator
          ((⁅C, S⁆).inv_mem hcW) s.property
      change ((c⁻¹ * s • c : C) : G) ∈ ⁅⁅C, S⁆, S⁆
      simpa [commutatorElement_def,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hcomm
    calc
      ⁅C, S⁆ = D.map C.subtype := hDmap.symm
      _ = (commutatorAction₂ (A := S) (G := C)).map C.subtype := by rw [hidem]
      _ ≤ ⁅⁅C, S⁆, S⁆ := htarget

/- Faithfulness of the action used in the induction step.  The source only
mentions the `P × Q` input: after that input kills the odd part of the
kernel, normality makes the remaining kernel a 2-subgroup, hence it lies in
the chosen Sylow subgroup and `oneAmax` identifies it with `A`. -/

end Stellmacher.SectionOne.SmallMProof
