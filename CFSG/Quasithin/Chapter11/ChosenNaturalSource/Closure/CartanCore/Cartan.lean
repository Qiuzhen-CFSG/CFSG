module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Cartan disjointness and the core commutator

The Cartan intersection with the literal quotient-action kernel is trivial:
an element lies in L₁, centralizes L₁/O₂(L₁), and hence lies in O₂(L₁)
by the centerless local rank-one quotient. Odd order then kills it.
The rank premise is the preceding marked Cartan calculation. Applying the
proved quasithin rank argument gives 11.5.6(1) and its even-degree consequence.
The core commutator in (5) uses the preceding 11.4.1(3) only in the strict
component case. No exceptional embedding is discarded.
Source: Aschbacher--Smith 11.5.6, printed pp.780--781.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Quotient-kernel membership gives actual commutators in the actual core. -/
theorem coreQuotientCentralizer_commutator {K : Subgroup G} {x k : G}
    (hx : x ∈ coreQuotientCentralizer K) (hk : k ∈ K) :
    ⁅x, k⁆ ∈ K.pCoreIn 2 := by
  obtain ⟨a, ha, rfl⟩ := hx
  let b : K := ⟨k, hk⟩
  have he := congrArg (fun f : MulAut (K ⧸ pCore 2 K) =>
    f (QuotientGroup.mk' (pCore 2 K) b)) (MonoidHom.mem_ker.mp ha)
  rw [coreQuotientAction_apply_mk] at he
  change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom a b) =
    QuotientGroup.mk' (pCore 2 K) b at he
  have hh : K.normalizerMonoidHom a b * b⁻¹ ∈ pCore 2 K :=
    (QuotientGroup.eq_one_iff (N := pCore 2 K) _).mp (by
      change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom a b * b⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel])
  exact ⟨K.normalizerMonoidHom a b * b⁻¹, hh, rfl⟩

namespace Geometry
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The original local quotient, rather than K/O₂(K), is centerless.
This formulation therefore retains the odd-core exceptional K alternatives. -/
theorem local_intersection_Y_le_core
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥) :
    E.L₁ ⊓ E.Y ≤ E.L₁.pCoreIn 2 := by
  rintro x ⟨hx, hy⟩
  let a : E.L₁ := ⟨x, hx⟩
  let q := QuotientGroup.mk' (pCore 2 E.L₁)
  have hc : q a ∈ center (E.L₁ ⧸ pCore 2 E.L₁) := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.L₁) b
    have hcomm := coreQuotientCentralizer_commutator hy.2
      (le_conjugateSpanBy E.L₁ E.G₁ b.property)
    have hcL : ⁅x, (b : G)⁆ ∈ E.L₁ :=
      E.L₁.mul_mem (E.L₁.mul_mem (E.L₁.mul_mem hx b.property) (E.L₁.inv_mem hx))
        (E.L₁.inv_mem b.property)
    obtain ⟨c, hc, hce⟩ := inf_pCoreIn_le_of_le 2
      (le_conjugateSpanBy E.L₁ E.G₁) ⟨hcL, hcomm⟩
    have hin : ⁅a, b⁆ ∈ pCore 2 E.L₁ := by
      have he : c = ⁅a, b⁆ := Subtype.ext hce
      exact he ▸ hc
    have hone : q ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hin
    rw [map_commutatorElement] at hone
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  have he : q a = 1 := mem_bot.mp (hz ▸ hc)
  exact ⟨a, (QuotientGroup.eq_one_iff a).mp he, rfl⟩

/-- Construct the disjointness needed by the numerical Cartan argument. -/
theorem cartan_disjoint_Y
    (hodd : Odd (Nat.card E.X))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥) : Disjoint E.X E.Y := by
  have hcore : E.X ⊓ E.Y ≤ E.L₁.pCoreIn 2 := by
    intro x hx
    exact E.local_intersection_Y_le_core hz ⟨hCX ⟨hx.1, hx.2.1⟩, hx.2⟩
  have hd : Disjoint E.X (E.L₁.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (isPGroup_pCoreIn 2 E.L₁).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  exact disjoint_iff.mpr (le_bot_iff.mp ((le_inf inf_le_left hcore).trans hd.le_bot))

/-- 11.5.6(1) with quotient-kernel disjointness discharged. -/
theorem cartan_coprime_of_local_action (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X))
    (hr : ∀ p : ℕ, p.Prime → p ∣ 2 ^ E.input.field.degree - 1 → 2 ≤ primeRank p E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥) :
    Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1) :=
  E.cartan_coprime hp hX hr (E.cartan_disjoint_Y hodd hCX hz)

/-- The even-degree assertion of 11.5.6(2). -/
theorem three_not_dvd_Y_of_even
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (he : Even E.input.field.degree) : ¬ 3 ∣ Nat.card E.Y := by
  have hd := (Nat.BinaryTorusParity.three_dvd_sub_one_iff E.input.field.degree).mpr he
  exact Nat.prime_three.coprime_iff_not_dvd.mp (hc.of_dvd_right hd).symm

/-- The rank bound in 11.5.6(2). Strict local embeddings occur at q=4,
so the even-degree coprimality already handles them. In the equality case,
odd ranks add across the literal quotient-action centralizer. -/
theorem three_rank_Y_le_one (hp : E.point ≠ ⊥)
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hrank : 1 ≤ primeRank 3 E.L₁) : primeRank 3 E.Y ≤ 1 := by
  by_cases he : Even E.input.field.degree
  · have hzero := PrimeRank.eq_zero_iff_not_dvd_card.mpr (E.three_not_dvd_Y_of_even hc he)
    omega
  · have hKL : E.K = E.L₁ := by
      by_contra hne
      exact he (hexception (lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁) (Ne.symm hne)))
    have hn : E.Y ≤ normalizer (E.K : Set G) := E.Y_le_G₁.trans E.G₁_normalizes_K
    have hcomm : ⁅(pResidual 2 E.Y).map E.Y.subtype, E.K⁆ ≤ E.K.pCoreIn 2 := by
      apply commutator_le.mpr
      intro y hy k hk
      exact coreQuotientCentralizer_commutator ((map_subtype_le _ hy).2) hk
    have hzK : Nat.Coprime 3 (Nat.card (center (E.K ⧸ pCore 2 E.K))) := by
      rw [hKL, hz, Nat.card_unique]
      exact Nat.coprime_one_right 3
    have hadd := Theory.GroupTheory.ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
      (by decide : Odd 3) E.Y E.K hn hcomm hzK
    have hbound : primeRank 3 (E.Y ⊔ E.K : Subgroup G) ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective 3
        (inclusion (sup_le E.Y_le_G₁ E.K_le_G₁)) (inclusion_injective _)).trans
        ((isQuasithin_iff_twoLocal.mp E.input.source.simpleQTKE.quasithin E.G₁
          (D.centralQuotientPreimage_twoLocal E.point hp)) 3 (by decide) (by decide))
    rw [hKL] at hadd hbound
    omega

/-- 11.5.6(5), retaining the preceding 11.4.1(3) only when L₁<K. -/
theorem core_commutator_le
    (hX : E.X ≤ normalizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G))
    (hstrict : E.L₁ < E.K → ⁅E.R₁, E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ E.R₁ :=
    pCoreIn_le_pCoreIn_of_sylow T le_sup_right (sup_le_sup_right E.L₁_le _)
  by_cases he : E.K = E.L₁
  · rw [he]
    exact (le_normalizer_iff_commutator_le_left.mp
      (hX.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans hcore
  · exact (commutator_mono hcore le_rfl).trans
      (hstrict (lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁) (Ne.symm he)))

end Geometry
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
