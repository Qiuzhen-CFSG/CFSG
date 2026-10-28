module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryBenderExclusion
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.SpecificGroups.SymplecticFour.HigherFieldBorelGeometry
public import Theory.SpecificGroups.PSL3.HigherFieldBorelGeometry
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# Borel control for the remaining classical components

Trivial odd core in the plane-centralizer overgroup and the odd covering
kernel force the component center to be trivial. An odd prime of model
rank at least two then prevents a second conjugate component, proving
relative normality. The PSL₃ and Sp₄ Thompson products put the literal
component Sylow normalizer in N_G(J(Q)). This includes Sp₄(4) and uses
the full Sylow of KQ, rather than replacing it by an elementary sixteen.

NonFFSourceDoubledBinaryClassicalExclusion combines these containments with
the previously proved Cartan escape on the original chosen-module plane.
Source: Aschbacher–Smith 7.7.6, printed pp.705–706, refs/quasithin.pdf;
the Thompson products are the matrix calculation underlying 2.5.7.
-/

open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryClassicalExclusion

theorem component_centerless {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H)
    (hH : pPrimeCore 2 H = ⊥) (ho : Odd (Nat.card (center K))) : center K = ⊥ := by
  let := hK.quasisimple
  have hKodd : pPrimeCore 2 K = ⊥ := by
    have hh := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hK.1)
    simpa only [hK.2.1.pPrimeCore_eq_bot hH,Subgroup.map_bot] using hh.symm
  have hZ : IsPGroup 2 (center K) := (IsQuasisimple.center_eq_pCore hKodd).symm ▸ pCore_isPGroup
  obtain ⟨n,hn⟩ := hZ.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hn0
    exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hn0)
  exact card_eq_one.mp (by simpa only [hn0,pow_zero] using hn)

private def wholeEquiv {K S : Type*} [Group K] [Group S]
    (hz : center K = ⊥) (e : K ⧸ center K ≃* S) : K ≃* S :=
  QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)

private theorem normal_of_rank {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H) (hH : IsStronglyQuasithin H)
    (hz : center K = ⊥) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 2 ≤ primeRank p K) : (K.subgroupOf H).Normal := by
  let : Fact p.Prime := ⟨hp⟩
  let e := subgroupOfEquivOfLe hK.1
  have hz' : center (K.subgroupOf H) = ⊥ := by
    apply card_eq_one.mp
    exact (Nat.card_congr (centerCongr e).toEquiv).trans (by rw [hz,card_bot])
  apply hK.2.normal_of_centerless_primeRank (p := p) hz'
  · rwa [primeRank_equiv p e]
  · exact hH p hp ho

theorem linear_normal {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H) (hH : IsStronglyQuasithin H)
    (hz : center K = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n)) :
    (K.subgroupOf H).Normal := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨p,hp,ho,hr⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear (by omega) hF
  apply normal_of_rank H K hK hH hz hp ho
  rwa [primeRank_equiv p (wholeEquiv hz e)]

theorem symplectic_normal {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H) (hH : IsStronglyQuasithin H)
    (hz : center K = ⊥) {n : ℕ} (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n)) :
    (K.subgroupOf H).Normal := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply normal_of_rank H K hK hH hz Nat.prime_three (by decide)
  rw [primeRank_equiv 3 (wholeEquiv hz e)]
  exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic

private theorem transport_normalizer_thompson
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G) (hKH : K ≤ H)
    (S : Sylow 2 H) (hSQ : (S : Subgroup H).map H.subtype = Q)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    (hN : (normalizer ((S : Subgroup H).subgroupOf (K.subgroupOf H) :
      Set (K.subgroupOf H))).map (K.subgroupOf H).subtype ≤
      normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  let K₀ := K.subgroupOf H
  let e : K₀ ≃* K := subgroupOfEquivOfLe hKH
  have hSK : ((S : Subgroup H).subgroupOf K₀).map e.toMonoidHom = (P : Subgroup K) := by
    apply P.is_maximal'
    · exact S.isPGroup'.comap_subtype.map _
    · intro x hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      have hxQ := hPQ (mem_map_of_mem K.subtype hx)
      rw [←hSQ] at hxQ
      obtain ⟨y,hy,he⟩ := hxQ
      have hey : y = (e.symm x).val := Subtype.ext he
      change (e.symm x).val ∈ (S : Subgroup H)
      rw [←hey]
      exact hy
  have hBN : ((normalizer ((S : Subgroup H).subgroupOf K₀ : Set K₀)).map K₀.subtype).map
      H.subtype = (normalizer (P : Set K)).map K.subtype := by
    have hcomp : H.subtype.comp K₀.subtype = K.subtype.comp e.toMonoidHom := rfl
    rw [map_map,hcomp,←map_map,map_equiv_normalizer_eq,hSK]
    rfl
  have hJ : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ Q := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hSQ]
  have hh := (map_mono (f := H.subtype) hN).trans
    (le_normalizer_map (H := elementaryAbelianMaxJ (S : Subgroup H)) H.subtype)
  rwa [hBN,hJ] at hh

/-- Relative normality and the genuine matrix Thompson product put the original
linear-three component Borel in the normalizer of J(Q). -/
theorem linear_normalizer_thompson
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hK : IsComponentIn K H) (hQH : Q ≤ H) (hp : IsPGroup 2 Q)
    (hH : IsStronglyQuasithin H) (hz : center K = ⊥)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n)) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  have hnK := linear_normal H K hK hH hz hn hm
  have hQN : Q ≤ normalizer (K : Set G) := hQH.trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
  let J := K ⊔ Q
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hQN)
  obtain ⟨S,hS⟩ := DoubledBinaryCoverPlacement.core_sylow_join H K Q hK hQH hp P hPQ
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply transport_normalizer_thompson J K Q le_sup_left S hS P hPQ
  exact Matrix.PSL3.OrdinaryBorel.normalizer_thompson K₀
    ((subgroupOfEquivOfLe le_sup_left).trans (wholeEquiv hz e)) (by omega) hF S

/-- The symplectic component Borel normalizes J(Q), including the q=4 row. -/
theorem symplectic_normalizer_thompson
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hK : IsComponentIn K H) (hQH : Q ≤ H) (hp : IsPGroup 2 Q)
    (hH : IsStronglyQuasithin H) (hz : center K = ⊥)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n)) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  have hnK := symplectic_normal H K hK hH hz hm
  have hQN : Q ≤ normalizer (K : Set G) := hQH.trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
  let J := K ⊔ Q
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hQN)
  obtain ⟨S,hS⟩ := DoubledBinaryCoverPlacement.core_sylow_join H K Q hK hQH hp P hPQ
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply transport_normalizer_thompson J K Q le_sup_left S hS P hPQ
  exact Theory.SpecificGroups.SymplecticFour.OrdinaryBorel.normalizer_thompson K₀
    (((subgroupOfEquivOfLe le_sup_left).trans (wholeEquiv hz e)).trans
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm) (by omega) hF S

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryClassicalExclusion
