module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Residual
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankOneNormal
public import Theory.ElementaryAbelian.Injective

/-!
# Prime ranks in the literal Hall quotients of 11.4.2

For a nilpotent subgroup Y, every elementary subgroup survives the extraction
O³(Y) Ω₁(O₃(Y)). Thus extraction preserves prime rank. A rank-two image at
an odd prime forces rank two before quotienting, even with an odd covering
kernel: rank at most one would make the Sylow subgroup cyclic. Quotienting
by O₂(L) then preserves this rank exactly. The chosen-flag Hall endpoint
uses these statements with the original inclusion and action projection.

Source: Aschbacher--Smith, 11.4.2, printed p.777. Nilpotence of the actual
actor remains a Hall-construction obligation of this comparison owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open CommonCore
variable {G : Type*} [Group G] [Finite G]

/-- Every elementary subgroup of a nilpotent Hall group survives extraction. -/
theorem elementary_le_oddCartanPart (Y : Subgroup G) [Group.IsNilpotent Y]
    {p : ℕ} [Fact p.Prime] (A : Subgroup Y) [IsElementaryAbelian p A] :
    A.map Y.subtype ≤ oddCartanPart Y := by
  apply map_mono
  by_cases hp : p = 3
  · subst p
    obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 3 A).exists_le_sylow
    have hn : (P : Subgroup Y).Normal :=
      Group.IsNilpotent.sylow_normal inferInstance 3 P
    have hAC : A ≤ pCore 3 Y := hAP.trans (le_sSup ⟨hn,P.isPGroup'⟩)
    apply le_trans _ le_sup_right
    intro a ha
    refine ⟨⟨a,hAC ha⟩,?_,rfl⟩
    apply Subgroup.subset_closure
    change (⟨a,hAC ha⟩ : pCore 3 Y) ^ 3 = 1
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := A) a ha)
  · apply le_trans _ le_sup_left
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
    exact ((Nat.prime_three.coprime_iff_not_dvd).mpr (fun hd =>
      hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp hd).symm)).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hpow)

/-- Extracting the source odd Cartan part retains every prime rank. -/
theorem oddCartanPart_primeRank (Y : Subgroup G) [Group.IsNilpotent Y]
    (p : ℕ) [Fact p.Prime] : primeRank p (oddCartanPart Y) = primeRank p Y := by
  apply le_antisymm (primeRank_mono p (oddCartanPart_le Y))
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := Y) (p := p)
  let := hA
  have hm : IsElementaryAbelian p (A.map Y.subtype) := IsElementaryAbelian.map Y.subtype
  let := hm
  have hc : Nat.card (A.map Y.subtype) = p ^ primeRank p Y := by
    rwa [card_map_of_injective Y.subtype_injective]
  let B := (A.map Y.subtype).subgroupOf (oddCartanPart Y)
  let : IsElementaryAbelian p B := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (elementary_le_oddCartanPart Y (p := p) A)).toMonoidHom
    (subgroupOfEquivOfLe (elementary_le_oddCartanPart Y (p := p) A)).injective
  apply IsElementaryAbelian.primeRank_ge_of_card B
  exact (Nat.card_congr (subgroupOfEquivOfLe
    (elementary_le_oddCartanPart Y (p := p) A)).toEquiv).trans hc

/-- A rank-two odd image forces rank two before taking a quotient, even
when the kernel contains an odd covering center. -/
theorem two_le_primeRank_of_image {A B : Type*} [Group A] [Finite A] [Group B]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (φ : A →* B)
    (hr : 2 ≤ primeRank p φ.range) : 2 ≤ primeRank p A := by
  by_contra! hsmall
  let P : Sylow p A := Classical.choice inferInstance
  have hcyc := P.isCyclic_of_odd_of_primeRank_le_one hp (by omega)
  have hu := P.primeRank_le_one_of_surjective hcyc φ.rangeRestrict φ.rangeRestrict_surjective
  omega

/-- The actual quotient by O2(L) preserves the rank of a subgroup lying in L. -/
theorem componentQuotient_primeRank (L Y : Subgroup G) (hYL : Y ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p ((Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) =
      primeRank p Y := by
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel hp
    (QuotientGroup.mk' (pCore 2 L)) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
    primeRank_equiv p (subgroupOfEquivOfLe hYL)]

/-- The Hall image rank transfers to the original component quotient after
source Cartan extraction, with the covering kernel retained on the input side. -/
theorem oddCartanPart_quotient_rank_two (L Y : Subgroup G) [Group.IsNilpotent Y]
    (hYL : oddCartanPart Y ≤ L) {A : Type*} [Group A]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (φ : Y →* A)
    (hr : 2 ≤ primeRank p φ.range) :
    2 ≤ primeRank p (((oddCartanPart Y).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L))) := by
  rw [componentQuotient_primeRank L _ hYL hp, oddCartanPart_primeRank]
  exact two_le_primeRank_of_image hp φ hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
