module
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Prime cores of overgroups of a lower mixed core

In a finite solvable group K, any subgroup V containing the preimage of
O_p'(K/O_p(K)) has the same ambient p-core as K. The containment is in the
lower mixed core O_{p,p'}(K); no Sylow containment is required.

The ambient p-core lies in V and hence in its p-core. For the reverse
inclusion, pass to K/O_p(K), whose p-core is trivial by pulling a normal
p-subgroup back through the quotient. The image of O_p(V) is normalized
by the ambient p'-core, and their commutator lies in both subgroups.
Coprime orders make them centralize one another. The Fitting subgroup of
this quotient lies in its p'-core and is self-centralizing by solvability,
so the p-group image is trivial.

This standard core transfer supplies the final normality step in
Stellmacher (10.1)(a3)(9), Journal of Algebra 190 (1997), printed pp.61–62.
It retains the literal subgroup embedding and applies to every prime.
-/

namespace Subgroup

private theorem fitting_le_pPrimeCore_of_pCore_eq_bot
    {K : Type*} [Group K] [Finite K] (p : ℕ) [Fact p.Prime]
    (hcore : pCore p K = ⊥) : fittingSubgroup K ≤ pPrimeCore p K := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun prime => ?_
  by_cases heq : prime.val.val = p
  · rw [heq, hcore]
    exact bot_le
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨exponent, hcard⟩ :=
      (pCore_isPGroup (p := prime.val.val) (G := K)).exists_card_eq
    rw [hcard]
    exact ((Nat.coprime_primes (Fact.out : p.Prime)
      (Nat.prime_of_mem_primeFactors prime.val.property)).mpr (Ne.symm heq)).pow_right _

/-- Containing the lower mixed core preserves the mapped prime core. -/
public theorem mapped_pCore_eq_of_prime_mixed_core_le
    {K : Type*} [Group K] [Finite K] [Group.IsSolvable K]
    (p : ℕ) [Fact p.Prime] (V : Subgroup K)
    (hmixed : (pPrimeCore p (K ⧸ pCore p K)).comap
      (QuotientGroup.mk' (pCore p K)) ≤ V) :
    (pCore p V).map V.subtype = pCore p K := by
  let R := pCore p K
  let q : K →* K ⧸ R := QuotientGroup.mk' R
  let B := pPrimeCore p (K ⧸ R)
  let L := B.comap q
  let C := (pCore p V).map V.subtype
  have hLV : L ≤ V := hmixed
  have hLmap : L.map q = B :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) B
  have hRV : R ≤ V := by
    apply le_trans ?_ hLV
    intro r hr
    change q r ∈ B
    have heq : q r = 1 := (QuotientGroup.eq_one_iff (N := R) r).mpr hr
    rw [heq]
    exact B.one_mem
  have hCnormalizer : V ≤ normalizer (C : Set K) := by
    have h := (pCore p V).le_normalizer_map V.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have hcomm : ⁅L, C⁆ ≤ C :=
    le_normalizer_iff_commutator_le_right.mp (hLV.trans hCnormalizer)
  have hcommImage : ⁅B, C.map q⁆ ≤ C.map q := by
    have h := map_mono (f := q) hcomm
    rwa [map_commutator, hLmap] at h
  have hCp : IsPGroup p (C.map q) :=
    (pCore_isPGroup.map V.subtype).map q
  have hcoprime : Nat.Coprime (Nat.card (C.map q)) (Nat.card B) := by
    obtain ⟨exponent, hcard⟩ := hCp.exists_card_eq
    rw [hcard]
    exact (pPrimeCore_coprime_card (p := p) (G := K ⧸ R)).pow_left _
  have hdisjoint : Disjoint (C.map q) B := disjoint_of_coprime_natCard hcoprime
  have hcommBot : ⁅B, C.map q⁆ = ⊥ :=
    le_bot_iff.mp ((le_inf hcommImage (commutator_le_left B (C.map q))).trans
      hdisjoint.le_bot)
  have hcentral : C.map q ≤ centralizer (B : Set (K ⧸ R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcommBot)
  have hquotientCore : pCore p (K ⧸ R) = ⊥ := by
    have hkerP : IsPGroup p q.ker := by
      rw [show q.ker = R from QuotientGroup.ker_mk' R]
      exact pCore_isPGroup
    have hpreP : IsPGroup p ((pCore p (K ⧸ R)).comap q) :=
      pCore_isPGroup.comap_of_ker_isPGroup q hkerP
    have hpre : (pCore p (K ⧸ R)).comap q ≤ R :=
      le_sSup ⟨inferInstance, hpreP⟩
    apply bot_unique
    intro point hpoint
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective R point
    exact (QuotientGroup.eq_one_iff (N := R) original).mpr (hpre hpoint)
  have hfit : fittingSubgroup (K ⧸ R) ≤ B :=
    fitting_le_pPrimeCore_of_pCore_eq_bot p hquotientCore
  have hCB : C.map q ≤ B :=
    hcentral.trans ((centralizer_le hfit).trans
      ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
        (inferInstance : Group.IsSolvable (K ⧸ R))).trans hfit))
  have hCbot : C.map q = ⊥ :=
    le_bot_iff.mp ((le_inf le_rfl hCB).trans hdisjoint.le_bot)
  apply le_antisymm
  · have h := (map_eq_bot_iff (f := q) (H := C)).mp hCbot
    exact h.trans_eq (QuotientGroup.ker_mk' R)
  · have hle : R.subgroupOf V ≤ pCore p V :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    change R ≤ C
    rw [← map_subgroupOf_eq_of_le hRV]
    exact map_mono hle

end Subgroup
