module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Basic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# Placement of a faithful inner Hall action in the original orbit

A faithful inner action embeds the Hall group into the inner automorphism
group of the literal two-component quotient. Each prime in its order is
therefore a component prime. The original rank-two bound makes the section
centralizer coprime to those primes. Coprime-kernel lifting puts the actual
Hall subgroup inside L₀, without any hypothesis on the outer group order.

Consumer: the Suzuki central Hall row of Aschbacher--Smith 10.2.3, p.745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Chapter4
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
private theorem quotient_action_kernel_le_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker.map
      D.maximalLocal.subtype ≤ sectionCentralizer (localOrbit T L) := by
  let K := (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker
  have hKM : K ≤ D.maximalLocal.subgroupOf D.maximalLocal := fun x _ => x.property
  have hk : (action D K hKM).ker = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact x.property
  have hh := action_kernel_image_le D K hKM
  rw [hk,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hh
  exact hh

/-- Innerness on the original product quotient places the faithful Hall group in L₀. -/
theorem hall_le_orbit_of_inner
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {J : Type*} [Group J]
    (e : (L ⧸ pCore 2 L) ≃* J)
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (J × J))
    (hinner : ∀ b : B, action D B c.hall_le b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L))) :
    B.map H.subtype ≤ localOrbit T L := by
  let R := localOrbit T L
  let Q := R ⧸ pCore 2 R
  let C := B.map H.subtype
  let f := (action D B c.hall_le).codRestrict (MulAut.innerSubgroup Q) hinner
  have hfi : Function.Injective f := fun _ _ h =>
    action_injective D B c.hall_le c.faithful (congrArg Subtype.val h)
  have hcard : Nat.card B ∣ Nat.card Q :=
    (card_dvd_of_injective f hfi).trans (card_range_dvd (MulAut.conj : Q →* MulAut Q))
  have hCM : C ≤ D.maximalLocal := map_le_iff_le_comap.mpr c.hall_le
  have hc : Nat.Coprime (Nat.card C) (Nat.card (sectionCentralizer R)) := by
    rw [show Nat.card C = Nat.card B from card_map_of_injective H.subtype_injective]
    apply Nat.coprime_of_dvd
    intro p hp hpB hpC
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr (hall_odd D c)) (even_iff_two_dvd.mpr hpB)
    have hL : p ∣ Nat.card (L ⧸ pCore 2 L) := by
      have hd := hpB.trans hcard
      rw [Nat.card_congr q.toEquiv,Nat.card_prod] at hd
      rw [Nat.card_congr e.toEquiv]
      exact (hp.dvd_mul.mp hd).elim id id
    exact hp.coprime_iff_not_dvd.mp
      (source_nonnormal_sectionCentralizer_prime_coprime D c.nonnormal p hp2 hL) hpC
  have hkcard : Nat.card (normalizerQuotientAction R (pCore 2 R)).ker ∣
      Nat.card (sectionCentralizer R) := by
    rw [←card_map_of_injective (normalizer (R : Set G)).subtype_injective]
    exact card_dvd_of_le (quotient_action_kernel_le_section D)
  apply le_of_normalizerQuotientAction_inner R (pCore 2 R) C hCM
    (hc.coprime_dvd_right hkcard)
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,hba⟩ := ha
  have he : a = (⟨b,c.hall_le hb⟩ : D.maximalLocal) := Subtype.ext hba.symm
  rw [he]
  exact hinner ⟨b,hb⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
