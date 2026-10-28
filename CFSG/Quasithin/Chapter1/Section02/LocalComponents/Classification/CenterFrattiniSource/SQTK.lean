module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.Model
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.ParabolicSections
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankCubeFree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Conditional SQTK certificate for the center–Frattini candidate

The normal vector subgroup of the fixed model is `C₁₂₁ × C₁₂₁`. Every
subgroup of it has two generators: projection onto one cyclic coordinate
has cyclic kernel in the other coordinate. If the complement has order
120, the vector subgroup is Sylow at 11. For every other odd prime, the
group order has no prime cube. These facts bound the actual `primeRank`,
defined using generator ranks of abelian prime subgroups, by two.

If the complement is isomorphic to the concrete `SL₂(5)`, its simple
sections are constructed carriers, by the existing SL₂ section theorem.
The abelian kernel and the exact quotient isomorphism then give the same
conclusion for the candidate. We combine the two certificates and transfer
them to any class containing those finite simple constructed carriers.
The constructed catalogue is not asserted to be the full source class K.

This is a conditional helper for the source question surrounding
Aschbacher–Smith, A.3.4–A.3.6, printed pp.43–45, and 1.2.1(4d), p.504,
in `refs/quasithin.pdf` (1 March 2004 manuscript). The assembly owner must
construct the complement isomorphism and order witnesses. No C-component
certificate or QTKE ambient realization is asserted here.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

-- The generator-and-lift argument also occurs in
-- `Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicRanks`.
private theorem rank_le_two_of_cyclic_coordinates
    {A C : Type*} [Group A] [Finite A] [Group C] [IsCyclic C]
    (χ : A →* C) (hχ : IsCyclic χ.ker) : Group.rank A ≤ 2 := by
  classical
  let : IsCyclic χ.ker := hχ
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := χ.ker)
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := χ.range)
  obtain ⟨b, hb⟩ := χ.rangeRestrict_surjective r
  let S : Subgroup A := closure ({a.val, b} : Finset A)
  have haS : a.val ∈ S := subset_closure (by simp)
  have hbS : b ∈ S := subset_closure (by simp)
  have hS : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hr (χ.rangeRestrict x))
    have hn' : χ (b ^ n) = χ x := by
      rw [map_zpow]
      change (χ.rangeRestrict b : C) ^ n = (χ.rangeRestrict x : C)
      rw [hb]
      exact congrArg Subtype.val hn
    let c : χ.ker := ⟨x * (b ^ n)⁻¹, by simp [MonoidHom.mem_ker, hn']⟩
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (ha c)
    have hcS : c.val ∈ S := by
      have hm' : a.val ^ m = c.val := congrArg Subtype.val hm
      rw [← hm']
      exact S.zpow_mem haS m
    have h := S.mul_mem hcS (S.zpow_mem hbS n)
    simpa only [c, inv_mul_cancel_right] using h
  calc
    Group.rank A ≤ ({a.val, b} : Finset A).card := Group.rank_le hS
    _ ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le a.val {b}

private def coordinate (i : Fin 2) : Vector →* Multiplicative (ZMod 121) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => ZMod 121) i)

private theorem vector_subgroup_rank_le_two (A : Subgroup Vector) : Group.rank A ≤ 2 := by
  let χ := (coordinate 0).comp A.subtype
  apply rank_le_two_of_cyclic_coordinates χ
  let ψ : χ.ker →* Multiplicative (ZMod 121) :=
    ((coordinate 1).comp A.subtype).comp χ.ker.subtype
  apply isCyclic_of_injective ψ
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply congrArg Multiplicative.ofAdd
  ext i
  fin_cases i
  · exact (show a.val.val.toAdd 0 = 0 from a.property).trans
      (show b.val.val.toAdd 0 = 0 from b.property).symm
  · exact congrArg Multiplicative.toAdd hab

private theorem kernel_primeRank_le_two (p : ℕ) : primeRank p kernel ≤ 2 := by
  rw [Theory.GroupTheory.primeRank_equiv p kernelEquiv]
  apply csSup_le'
  rintro n ⟨A, _, _, _, hn⟩
  exact hn.trans (vector_subgroup_rank_le_two A)

private theorem candidate_card (hc : Nat.card complement = 120) :
    Nat.card Candidate = 121 ^ 2 * 120 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, hc]
  change Nat.card (Fin 2 → ZMod 121) * 120 = _
  simp

private theorem other_odd_cube_not_dvd {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (h11 : p ≠ 11) : ¬ p ^ 3 ∣ 121 ^ 2 * 120 := by
  intro hd
  have hpd := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have he : 121 ^ 2 * 120 = 11 ^ 4 * (2 ^ 3 * (3 * 5)) := by norm_num
  rw [he, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at hpd
  rcases hpd with h | h | h | h
  · exact h11 (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h)
  · have hp2 : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp (by decide) h
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    subst p
    norm_num at hd
  · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    subst p
    norm_num at hd

/-- The complement order makes the vector kernel a Sylow 11-subgroup and
bounds every other odd prime rank by the group order. -/
public theorem candidate_stronglyQuasithin (hc : Nat.card complement = 120) :
    IsStronglyQuasithin Candidate := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_cases h11 : p = 11
  · subst p
    have hi : ¬ 11 ∣ kernel.index := by
      rw [Subgroup.index_eq_card, Nat.card_congr quotientKernelEquiv.toEquiv, hc]
      decide
    rw [(kernel_isPGroup.toSylow hi).primeRank_eq]
    exact kernel_primeRank_le_two 11
  · apply primeRank_le_two_of_cube_not_dvd
    rw [candidate_card hc]
    exact other_odd_cube_not_dvd hp ho h11

/-- All simple sections are actual constructed carriers, conditional on the
isomorphism of the fixed matrix complement with SL₂(5). -/
public theorem candidate_isKGroup_constructed (e : complement ≃* SL5) :
    IsKGroup CFSG.KnownSimple.IsConstructedCarrier Candidate := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsSolvable kernel := Group.isSolvable_of_isSolvable_injective
    (f := kernelEquiv.toMonoidHom) kernelEquiv.injective
  apply IsKGroup.of_normal_quotient kernel (MainConverse.solvable_isKGroup_constructed _)
  exact (MainConverse.LinearThreeSections.sl2_isKGroup_constructed (ZMod 5)).of_injective
    (quotientKernelEquiv.trans e).toMonoidHom (quotientKernelEquiv.trans e).injective

/-- The two independent complement witnesses supply the conditional SQTK certificate. -/
public theorem candidate_isSQTK_constructed
    (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    IsSQTK CFSG.KnownSimple.IsConstructedCarrier Candidate :=
  ⟨candidate_stronglyQuasithin hc, candidate_isKGroup_constructed e⟩

/-- Only finite simple sections need to be included when enlarging the catalogue. -/
public theorem candidate_isKGroup_of_catalogue {K : GroupClass}
    (hK : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      CFSG.KnownSimple.IsConstructedCarrier S → K S)
    (e : complement ≃* SL5) : IsKGroup K Candidate := by
  intro S _ hS U f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (candidate_isKGroup_constructed e S hS U f hf)

/-- Transfer the conditional certificate to any class containing the finite
simple constructed carriers, without asserting catalogue completeness. -/
public theorem candidate_isSQTK_of_catalogue {K : GroupClass}
    (hK : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      CFSG.KnownSimple.IsConstructedCarrier S → K S)
    (e : complement ≃* SL5) (hc : Nat.card complement = 120) : IsSQTK K Candidate :=
  ⟨candidate_stronglyQuasithin hc, candidate_isKGroup_of_catalogue hK e⟩

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
