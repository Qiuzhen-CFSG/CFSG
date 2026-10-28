module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.FactorTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The source Borel residual and the cubic factors

The two relatively normal cubic source factors generate L₁/O₂(L₁), which
is therefore a three-group. A subgroup with this quotient and containing
a full Sylow two-subgroup must normalize that Sylow. This supplies the
normalization used to identify L₁* with the actual Borel.

The Borel residual retains the full torus only as its two-core quotient.
Its odd-order elements have order dividing three, so two-perfectness gives
B = θ(B). The same quotient and its two-group kernel give m₃(B) = 2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), p.877; proof of 13.8.20, pp.954–955.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open HigherFieldReduction
variable {G : Type*} [Group G] [Finite G]

/-- The two normal cubic factors make the local core quotient a three-group. -/
theorem one_core_threeGroup (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hz : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hx : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    IsPGroup 3 (one L T V₁ ⧸ pCore 2 (one L T V₁)) := by
  let D := one L T V₁
  have hZD := zero_le_one_of_factorization L T V₁ hfactor
  have hXD := plus_le_one L T V₁ hTV
  have hnZ := localImage_normal D (zero L) hZD (one_normalizes_zero L T V₁ hTL)
  have hnX := localImage_normal D (plus L T V₁) hXD (one_normalizes_plus L T V₁)
  let := hnZ
  have hpZ : IsPGroup 3 (Source.starImage D (zero L)) := IsPGroup.of_card (n := 1)
    (by simpa only [pow_one] using normal_star_card_three D (zero L) hZD hnZ hz)
  have hpX : IsPGroup 3 (Source.starImage D (plus L T V₁)) := IsPGroup.of_card (n := 1)
    (by simpa only [pow_one] using normal_star_card_three D (plus L T V₁) hXD hnX hx)
  have he : Source.starImage D (zero L) ⊔ Source.starImage D (plus L T V₁) = ⊤ := by
    change ((zero L).subgroupOf D).map (QuotientGroup.mk' (pCore 2 D)) ⊔
      ((plus L T V₁).subgroupOf D).map (QuotientGroup.mk' (pCore 2 D)) = _
    rw [← Subgroup.map_sup, ← subgroupOf_sup hZD hXD,
      show zero L ⊔ plus L T V₁ = D from (sup_comm _ _).trans hfactor.symm,
      subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hp := hpZ.to_sup_of_normal_left hpX
  rw [he] at hp
  exact hp.of_surjective (⊤ : Subgroup (Source.Hstar D)).subtype (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)

/-- A full Sylow contained in a subgroup with odd core quotient is normal there. -/
theorem le_sylowNormalizer_of_threeCore (D : Subgroup SL) (S : Sylow 2 SL)
    (hSD : (S : Subgroup SL) ≤ D) (hD : IsPGroup 3 (D ⧸ pCore 2 D)) :
    D ≤ normalizer (S : Set SL) := by
  let q := QuotientGroup.mk' (pCore 2 D)
  have he : ((S : Subgroup SL).subgroupOf D).map q = ⊥ := by
    have hp : IsPGroup 2 ((S : Subgroup SL).subgroupOf D) := S.isPGroup'.comap_subtype
    have hd := (hp.map q).disjoint_of_coprime
      (hD.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa only [disjoint_top] using hd
  have hSCore : (S : Subgroup SL) ≤ D.pCoreIn 2 := by
    have hker := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hker
    intro x hx
    exact ⟨⟨x, hSD hx⟩, hker hx, rfl⟩
  have hcore : D.pCoreIn 2 = S := S.is_maximal' (isPGroup_pCoreIn 2 D) hSCore
  change D ≤ normalizer ((S : Subgroup SL) : Set SL)
  rw [← hcore]
  exact D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))

/-- The actual B residual has the full two-parameter quotient. -/
def borelResidualQuotientEquiv (H K B₀ : Subgroup G)
    (eK : Source.starImage H K ≃* SL) (S : Sylow 2 SL)
    (hBH : B₀ ≤ H) (hB : Source.starImage H B₀ = modelBorel H K eK S) :
    (borelResidual B₀ ⧸ pCore 2 (borelResidual B₀)) ≃* (Fˣ × Fˣ) :=
  (starCoreQuotientEquiv H (borelResidual B₀) ((map_subtype_le _).trans hBH)).trans
    ((QuotientGroup.congr _ _
      (MulEquiv.subgroupCongr (starImage_borelResidual_eq_modelBorel H K B₀ eK S hBH hB))
      (pCore_map_iso 2 _)).trans (modelBorelQuotientEquiv H K eK S))

private theorem units_card : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, sl3Field_card]
  decide

/-- The torus in this argument has three-rank two; it is only a quotient of B. -/
theorem torus_threeRank : primeRank 3 (Fˣ × Fˣ) = 2 := by
  have hle : primeRank 3 Fˣ ≤ 1 :=
    (Classical.choice (Sylow.nonempty (p := 3) (G := Fˣ))).primeRank_le_one_of_isCyclic inferInstance
  have hne : primeRank 3 Fˣ ≠ 0 := by
    intro he
    have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp he
    exact hn (units_card ▸ dvd_rfl)
  rw [primeRank_prod_eq_add, show primeRank 3 Fˣ = 1 by omega]

/-- The two-core kernel preserves three-rank of the source Borel residual. -/
theorem rank_of_torus_quotient (D : Subgroup G) (e : (D ⧸ pCore 2 D) ≃* (Fˣ × Fˣ)) :
    primeRank 3 D = 2 := by
  let q := QuotientGroup.mk' (pCore 2 D)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hzero : primeRank 3 q.ker = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  have hl := primeRank_le_of_surjective_of_coprime 3 q (QuotientGroup.mk'_surjective _) hc
  have hu := Theory.GroupTheory.primeRank_le_ker_add (p := 3) q
  rw [hzero, zero_add] at hu
  have hr := Theory.GroupTheory.primeRank_equiv 3 e
  rw [torus_threeRank] at hr
  omega

/-- Odd-order generators have order three, so the two-perfect source B equals θ(B). -/
theorem theta_eq_of_torus_quotient (D : Subgroup G) (hp : IsPPerfect 2 D)
    (e : (D ⧸ pCore 2 D) ≃* (Fˣ × Fˣ)) :
    D = closure {x : G | x ∈ D ∧ orderOf x = 3} := by
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 D).mpr hp)
  apply le_antisymm ?_ ((closure_le _).mpr fun _ hx => hx.1)
  have hl : closure {x : D | Nat.Coprime 2 (orderOf x)} ≤
      (closure {x : G | x ∈ D ∧ orderOf x = 3}).comap D.subtype := by
    apply (closure_le _).mpr
    intro x hx
    let q := QuotientGroup.mk' (pCore 2 D)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have hd : orderOf x ∣ 3 := by
      rw [← q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x hx, ← e.orderOf_eq, Prod.orderOf]
      exact Nat.lcm_dvd
        (units_card ▸ orderOf_dvd_natCard (e (q x)).1)
        (units_card ▸ orderOf_dvd_natCard (e (q x)).2)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with ho | ho
    · have he : x = 1 := orderOf_eq_one_iff.mp ho
      rw [he]
      exact Subgroup.one_mem _
    · exact subset_closure ⟨x.property, (Subgroup.orderOf_coe x).trans ho⟩
  rw [hgen] at hl
  exact fun x hx => hl (show (⟨x, hx⟩ : D) ∈ ⊤ from trivial)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
