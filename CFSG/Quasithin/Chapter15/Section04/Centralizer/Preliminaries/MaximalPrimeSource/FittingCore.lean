module
public import Theory.GroupTheory.Fitting.ResidualNilpotence
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# Fitting-centralizer assembly for the maximal-prime argument

A subgroup centralizing every other prime core, whose action on the
p-core lies in the p-core of the full action, lies in the Fitting subgroup.
Take the normal intersection of those centralizers with the action-core
preimage. Its p-residual centralizes F(G), so it is abelian and prime to p.
Its Sylow factors are central in that intersection, making the intersection
nilpotent. If O₂(G) = 1, literal {2,p} support then puts the subgroup in Oₚ(G).

This is the Fitting-centralizer step of Aschbacher–Smith 15.4.3(2), printed
p.1157, with the automorphism-kernel correction handled by the action lemmas.
The residual calculation follows the checked structural argument in
`Theory.GroupTheory.Fitting.ResidualNilpotence`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

/-- Centralization of all other prime cores, together with a p-core action
on the defining prime core, places the subgroup in the Fitting subgroup. -/
theorem le_fitting_of_other_core_centralization {p : ℕ} [Fact p.Prime]
    (hs : Group.IsSolvable G) (D : Subgroup G)
    (hc : ∀ q : ℕ, q.Prime → q ≠ p → D ≤ centralizer (pCore q G : Set G))
    (ha : D.map (MulAut.conjNormal (H := pCore p G)) ≤
      (pCore p (MulAut.conjNormal (H := pCore p G) : G →* MulAut (pCore p G)).range).map
        (MulAut.conjNormal (H := pCore p G) : G →* MulAut (pCore p G)).range.subtype) :
    D ≤ fittingSubgroup G := by
  let rho : G →* MulAut (pCore p G) := MulAut.conjNormal
  let C : Subgroup G := ⨅ q : {q : ℕ // q.Prime ∧ q ≠ p},
    centralizer (pCore q.val G : Set G)
  let N := (pCore p rho.range).comap rho.rangeRestrict ⊓ C
  let : C.Normal := normal_iInf_normal fun q => inferInstance
  have hNq (q : ℕ) (hq : q.Prime) (hne : q ≠ p) :
      N ≤ centralizer (pCore q G : Set G) :=
    (show N ≤ C from inf_le_right).trans
      (iInf_le (fun r : {r : ℕ // r.Prime ∧ r ≠ p} =>
        centralizer (pCore r.val G : Set G)) ⟨q, hq, hne⟩)
  have hDN : D ≤ N := by
    refine le_inf ?_ (le_iInf fun q => hc q.val q.property.1 q.property.2)
    intro x hx
    obtain ⟨y, hy, he⟩ := ha (mem_map_of_mem rho hx)
    have hey : rho.rangeRestrict x = y := Subtype.ext he.symm
    change rho.rangeRestrict x ∈ pCore p rho.range
    rwa [hey]
  let R : Subgroup G := (pResidual p N).map N.subtype
  have hRN : R ≤ N := map_subtype_le _
  let f : N →* rho.range := rho.rangeRestrict.comp N.subtype
  have hf : f.range ≤ pCore p rho.range := by
    rintro _ ⟨x, rfl⟩
    exact x.property.1
  have hfP : IsPGroup p f.range := pCore_isPGroup.to_le hf
  have hres : pResidual p N ≤ f.ker :=
    sInf_le ⟨inferInstance, hfP.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  have hRp : R ≤ centralizer (pCore p G : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_iff.mpr
    intro z hz
    have he : rho x.val = 1 := congrArg Subtype.val (show f x = 1 from hres hx)
    have hez := congrArg (fun b : MulAut (pCore p G) => (b ⟨z, hz⟩ : G)) he
    change x.val * z * x.val⁻¹ = z at hez
    exact (mul_inv_eq_iff_eq_mul.mp hez).symm
  have hRC : R ≤ centralizer (fittingSubgroup G : Set G) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    by_cases heq : q.val.val = p
    · rw [heq]
      exact hRp
    · exact hRN.trans (hNq q.val.val (Nat.prime_of_mem_primeFactors q.val.property) heq)
  have hRF : R ≤ fittingSubgroup G := hRC.trans
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  let : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun a b => Subtype.ext ((hRC a.property) b.val (hRF b.property)).symm }
  have hRcop : Nat.Coprime p (Nat.card R) := by
    have ht : pResidual p R = ⊤ :=
      (pResidual_eq_top_iff p R).mpr (isPPerfect_embedded_pResidual p N)
    have hh := coprime_card_pResidual_of_commGroup (A := R) p
    simpa only [ht, card_top] using hh
  have hcentral : R ≤ centralizer (N : Set G) := by
    rw [← Sylow.iSup_sylow_map_eq_top (N := R)]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun q hq => ?_
    let : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have hne : q ≠ p := by
      intro heq
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hRcop
        (heq ▸ Nat.dvd_of_mem_primeFactors hq)
    exact (Sylow.map_le_pCore (inferInstance : R.Normal)
      (inferInstance : Group.IsNilpotent R) q (default : Sylow q R)).trans
      (le_centralizer_iff.mp (hNq q Fact.out hne))
  have hnilN : Group.IsNilpotent N := by
    let : Group.IsNilpotent (N ⧸ pResidual p N) :=
      (isPGroup_quotient_pResidual p).isNilpotent
    apply Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (pResidual p N))
    intro x hx
    have hxR : x.val ∈ R := mem_map_of_mem N.subtype
      ((QuotientGroup.eq_one_iff x).mp hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((hcentral hxR) y.val y.property)
  exact hDN.trans (le_sSup ⟨inferInstance, hnilN⟩)

/-- Once the image lies in F(G), absence of a two-core and its literal
{2,p} prime support put it in the p-core. -/
theorem le_pCore_of_fitting_and_prime_support {p : ℕ} [Fact p.Prime]
    (h2 : pCore 2 G = ⊥) {D : Subgroup G} (hDF : D ≤ fittingSubgroup G)
    (hd : ∀ q : ℕ, q.Prime → q ∣ Nat.card D → q = 2 ∨ q = p) :
    D ≤ pCore p G := by
  have hDc : D ≤ pPrimeCore 2 G :=
    hDF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 h2)
  have hD2 : ¬ 2 ∣ Nat.card D := by
    intro h
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 2) (G := G)) (h.trans (card_dvd_of_le hDc))
  have hDp : IsPGroup p D := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    rcases hd q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq) with heq | heq
    · exact (hD2 (heq ▸ Nat.dvd_of_mem_primeFactors hq)).elim
    · simpa only [heq] using (Fact.out : p.Prime).mem_primeFactors_self
  obtain ⟨S, hS⟩ := hDp.comap_subtype.exists_le_sylow (G := fittingSubgroup G)
  have hmap := map_mono (f := (fittingSubgroup G).subtype) hS
  change (D.subgroupOf (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤ _ at hmap
  rw [map_subgroupOf_eq_of_le hDF] at hmap
  exact hmap.trans (Sylow.map_le_pCore inferInstance inferInstance p S)
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
