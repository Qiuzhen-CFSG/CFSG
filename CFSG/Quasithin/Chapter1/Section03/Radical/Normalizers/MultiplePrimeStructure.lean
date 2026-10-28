module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The structural alternative with two Fitting primes

The natural SL₂ alternative has a Fitting subgroup of prime-square order.
Two distinct Fitting primes therefore force the nilpotent alternative in
A.3.6. Transport through the actual local component quotient equivalence
preserves the generalized Fitting subgroup, the SL₂(5) quotient and the
full extraspecial or homocyclic Sylow shapes, including higher exponents.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.513, the multiple-odd-prime reduction.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open Section02 Section02.LocalModels
universe u

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem layer_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom ≤ componentLayer B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro N hN
  exact map_le_iff_le_comap.mp (le_sSup (hN.map_equiv e))

private theorem generalizedFitting_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (generalizedFitting A).map e.toMonoidHom = generalizedFitting B := by
  have hl : (componentLayer A).map e.toMonoidHom = componentLayer B := by
    apply le_antisymm (layer_map_le e)
    have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
    simpa [map_map] using h
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fitting_map, hl]

private theorem nilpotent_transport {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) (h : A36Nilpotent A) : A36Nilpotent B := by
  let eF : generalizedFitting A ≃* generalizedFitting B :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (generalizedFitting_map e))
  have hF : generalizedFitting B = fittingSubgroup B := by
    rw [← generalizedFitting_map e, h.1, fitting_map e]
  let _ := h.2.1
  have hSL : IsSL (B ⧸ generalizedFitting B) 2 5 := by
    obtain ⟨F, _, _, hFcard, ⟨eS⟩⟩ := h.2.2.1
    exact ⟨F, inferInstance, inferInstance, hFcard,
      ⟨(QuotientGroup.congr _ _ e (generalizedFitting_map e)).symm.trans eS⟩⟩
  refine ⟨hF, Group.nilpotent_of_mulEquiv eF, hSL, ?_⟩
  intro p hp hd
  have hdA : p ∣ Nat.card (generalizedFitting A) := by
    rwa [Nat.card_congr eF.toEquiv]
  obtain ⟨hmod, hshape⟩ := h.2.2.2 p hp hdA
  let ep : pCore p A ≃* pCore p B :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  refine ⟨hmod, ?_⟩
  rcases hshape with ⟨⟨hex, hc⟩, he⟩ | ⟨a, ha, ⟨ea⟩⟩
  · left
    refine ⟨⟨IsExtraspecial.of_mulEquiv ep hex, (Nat.card_congr ep.symm.toEquiv).trans hc⟩, ?_⟩
    intro x
    obtain ⟨y, rfl⟩ := ep.surjective x
    simpa only [map_pow, map_one] using congrArg ep (he y)
  · exact Or.inr ⟨a, ha, ⟨ep.symm.trans ea⟩⟩

/-- Two distinct odd Fitting primes eliminate the natural SL₂ alternative;
transport retains the full generalized Fitting subgroup and every Sylow shape. -/
theorem nilpotent_of_two_fitting_primes
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {L T : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p)
    (hpdiv : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hqdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    A36Nilpotent (XiQuotient L) := by
  let e := radicalLocalQuotientEquiv hL
  have ha := proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1
  have hnC : ¬ IsQuasisimple (radicalLocalImage T L) := by
    intro hc
    let _ := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  rcases RadicalStructure.nonsimple_radical ha hnC with hnat | hnil
  · obtain ⟨hF, r, hr, _, hact⟩ := hnat
    let _ : Fact r.Prime := ⟨hr⟩
    obtain ⟨_, hc⟩ := RadicalStructure.natural_elementary hact
    let eF := (e.subgroupMap (fittingSubgroup (XiQuotient L))).trans
      (MulEquiv.subgroupCongr (fitting_map e))
    have hcard : Nat.card (fittingSubgroup (XiQuotient L)) = r ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, ← hF]
      exact hc
    have hpR : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp
      (hp.dvd_of_dvd_pow (hcard ▸ hpdiv))
    have hqR : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp
      (hq.dvd_of_dvd_pow (hcard ▸ hqdiv))
    exact (hne (hqR.trans hpR.symm)).elim
  · exact nilpotent_transport e.symm hnil

end CFSG.Quasithin.Chapter1.RadicalNormalizers
