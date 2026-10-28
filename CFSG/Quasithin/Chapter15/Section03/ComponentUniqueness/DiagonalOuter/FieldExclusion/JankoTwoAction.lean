module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual

/-!
# Central-cover reduction for the J₂ action calculation

For a nonidentity element of the faithful four-group, lift the perfect
residual of its fixed subgroup in the central quotient. The lift is perfect
and fixed by that element, so the TI-derived restriction fixes it under the
whole four-group. Its inner automorphisms therefore occur in every action
overgroup considered by `ThreeCoreFreeAction`. The concrete centralizer data
then kills the three-core in the quotient action image, and faithfulness of
the central-quotient action kills the original three-core.

The reduction is valid for arbitrary finite perfect central covers. The
J₂ theorem below is conditional on two local calculations, with no assumed
order or multiplier for the cover. It does not yet prove the J₂ case of the
source theorem: the inner and outer involution-centralizer calculations on
`Sporadic.LeechRelated.J2.Carrier` remain required.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137, using the corrected E₉ residual in `ModelAction`.
The model local data are described in GLS, Volume 3, Table 5.3g and note (3),
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, lines 263--294.
-/

public section

open Subgroup Theory.GroupTheory MulAut
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.JankoTwoAction
variable {K Q A : Type*} [Group K] [Group Q] [Group A]

private theorem perfect_isPPerfect [Finite K] [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The fixed-subgroup restriction supplies the inner perfect residual in the
actual quotient action image, even when fixed points themselves do not lift. -/
theorem fixedPerfectResidualInner_le_quotient_image [Finite K]
    (e : K ⧸ center K ≃* Q) (φ : A →* MulAut K)
    (hφ : FixesTwoPerfectSubgroups φ) (a : A) (ha : a ≠ 1)
    (D : Subgroup (MulAut K))
    (hD : (fixedSubgroupOfAction φ).map (MulAut.conj : K →* MulAut K) ≤ D) :
    fixedPerfectResidualInner (MulAut.centralQuotientAction e (φ a)) ≤
      D.map (MulAut.centralQuotientAction e) := by
  obtain ⟨F, hF, hfix, hmap⟩ := exists_perfect_fixed_lift e (φ a)
  let := hF
  have hFφ : F ≤ fixedSubgroupOfAction φ := by
    intro x hx b
    exact hφ a ha F perfect_isPPerfect
      (fun y => (mem_fixedSubgroup (φ a) y).mp (hfix y.property)) b ⟨x, hx⟩
  have hFD : F.map (MulAut.conj : K →* MulAut K) ≤ D := (map_mono hFφ).trans hD
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := (show y ∈ F.map
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) from hmap.symm ▸ hy)
  refine ⟨MulAut.conj x, hFD (mem_map_of_mem _ hx), ?_⟩
  exact MulAut.centralQuotientAction_conj e x

/-- One nonidentity actor with the specified quotient-centralizer data suffices. -/
theorem threeCoreFreeAction_of_quotient_involution_data [Finite K] [Finite Q]
    [Group.IsPerfect K] (e : K ⧸ center K ≃* Q)
    (φ : A →* MulAut K) (hφ : FixesTwoPerfectSubgroups φ)
    (a : A) (ha : a ≠ 1)
    (hdata : FixedResidualThreeCoreData (MulAut.centralQuotientAction e (φ a))) :
    ThreeCoreFreeAction φ := by
  intro D hDc hDi
  let π := MulAut.centralQuotientAction e
  have hD : D.map π ≤ centralizer ({π (φ a)} : Set (MulAut Q)) := by
    rintro _ ⟨d, hd, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using (congrArg π (hDc hd _ ⟨a, rfl⟩)).symm
  have hcore : pCore 3 (D.map π) = ⊥ :=
    threeCore_eq_bot_of_fixedResidualData _ hdata _ hD
      (fixedPerfectResidualInner_le_quotient_image e φ hφ a ha D hDi)
  have hinj := MulAut.centralQuotientAction_injective e
  have he := pCore_map_iso 3 (D.equivMapOfInjective π hinj)
  rw [hcore] at he
  exact ((pCore 3 D).map_eq_bot_iff_of_injective
    (D.equivMapOfInjective π hinj).injective).mp he

/-- Conditional model reduction for every finite perfect central cover.
The concrete involution-centralizer data must still be established. -/
theorem threeCoreFreeAction_of_all_involution_data [Finite K] [Finite Q]
    [Group.IsPerfect K] [IsKleinFour A] (e : K ⧸ center K ≃* Q)
    (hdata : ∀ b : MulAut Q, orderOf b = 2 → FixedResidualThreeCoreData b)
    (φ : A →* MulAut K) (hinj : Function.Injective φ)
    (hφ : FixesTwoPerfectSubgroups φ) : ThreeCoreFreeAction φ := by
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; decide)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by
    rw [IsKleinFour.card_four]
    decide)
  have hane : a ≠ 1 := by intro he; simp [he] at ha
  apply threeCoreFreeAction_of_quotient_involution_data e φ hφ a hane
  apply hdata
  exact (orderOf_injective ((MulAut.centralQuotientAction e).comp φ)
    (MulAut.centralQuotientAction_comp_injective e φ hinj) a).trans ha

/-- The J₂ specialization, retaining the concrete local proof obligation. -/
theorem threeCoreFreeAction_of_j2_involution_data [Finite K] [IsQuasisimple K]
    [IsKleinFour A] (e : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier)
    (hdata : ∀ b : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf b = 2 →
      FixedResidualThreeCoreData b)
    (φ : A →* MulAut K) (hinj : Function.Injective φ)
    (hφ : FixesTwoPerfectSubgroups φ) : ThreeCoreFreeAction φ :=
  threeCoreFreeAction_of_all_involution_data e hdata φ hinj hφ

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.JankoTwoAction
