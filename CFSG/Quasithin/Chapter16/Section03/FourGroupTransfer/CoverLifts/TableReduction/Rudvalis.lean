module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.SourceClauses
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.IntersectionResidual.ModelFacts
public import BenderSuzuki.Converse.Sz

/-!
# The Rudvalis row in the exceptional-cover table

The quotient action is transported through the actual central quotient of the
quasisimple group.  The literal Rudvalis row is then used in two places.  Its
`E₃₂`/`E₆₄` extension is impossible because the embedded Suzuki component
contributes a factor seven to the fixed-subgroup order, whereas the extension
has order `2^11 * 120`.  In the remaining `E₄ × Sz(8)` row, a two-central
involution would put an ambient Sylow two-subgroup inside the fixed subgroup;
the certified Rudvalis Sylow order `2^14` contradicts the product order.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
16.1.5(11), printed p.1172 / PDF p.1189, and the final paragraph of 16.3.6,
printed p.1179 / PDF p.1196.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction

open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open ClassificationModels

noncomputable section

private abbrev Ru := SporadicName.ru.Carrier

private theorem suzuki_card : Nat.card SzEight = 29120 := by
  have h := (BenderSuzuki.Converse.sz_data 1 (by decide)).2.2.2.2.1
  norm_num [BenderSuzuki.Converse.SzG] at h ⊢
  exact h

private theorem ru_sylow_card (S : Sylow 2 Ru) : Nat.card S = 16384 := by
  let : Finite Ru := inferInstanceAs (Finite Rudvalis.Model)
  let P : Subgroup Rudvalis.Model :=
    _root_.Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate
  have hPcard : Nat.card P = 16384 :=
    _root_.Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate_card
  have hPgroup : IsPGroup 2 P := IsPGroup.of_card (n := 14) hPcard
  have hPindex : ¬ 2 ∣ P.index := by
    intro hd
    apply _root_.Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
    rw [← P.card_mul_index, hPcard]
    exact Nat.mul_dvd_mul_left 16384 hd
  let P' : Sylow 2 Rudvalis.Model := hPgroup.toSylow hPindex
  have hSP : Nat.card S = Nat.card P' :=
    Nat.card_congr (Sylow.equiv S P').toEquiv
  rw [hSP]
  change Nat.card P = 16384
  exact hPcard

private theorem map_component_injective
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (J : Subgroup H) (hJ : Nonempty (J ≃* SzEight)) :
    Function.Injective
      ((QuotientGroup.mk' (center H)).comp J.subtype) := by
  have hcenter : center J = ⊥ :=
    CounterexampleGeometry.center_eq_bot_of_suzuki (X := J) (m := 1)
      (by decide) hJ
  intro x y hxy
  have hxy' : QuotientGroup.mk' (center H) (x : H) =
      QuotientGroup.mk' (center H) (y : H) := hxy
  have hcent : (x : H)⁻¹ * (y : H) ∈ center H :=
    QuotientGroup.eq.mp hxy'
  have hcentJ : x⁻¹ * y ∈ center J := by
    rw [mem_center_iff]
    intro z
    apply Subtype.ext
    exact mem_center_iff.mp hcent (z : H)
  have hbot : x⁻¹ * y ∈ (⊥ : Subgroup J) := by
    simpa [hcenter] using hcentJ
  have hmul : x⁻¹ * y = 1 := by simpa using hbot
  have hmul' : (x : H)⁻¹ * (y : H) = 1 := congrArg Subtype.val hmul
  exact Subtype.ext (inv_mul_eq_one.mp hmul')

private theorem ru_extension_impossible
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (J : Subgroup H) (r : MulAut H)
    (hJfix : J ≤ r.fixedSubgroup)
    (hJmodel : Nonempty (J ≃* SzEight))
    (q : H ⧸ center H ≃* Ru)
    (hExt : IsRudvalisExtension
      (MulAut.centralQuotientAction q r).fixedSubgroup) : False := by
  let φ : J →* Ru :=
    (q.toMonoidHom.comp (QuotientGroup.mk' (center H))).comp J.subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact (map_component_injective J hJmodel) (q.injective hxy)
  let C : Subgroup Ru := (MulAut.centralQuotientAction q r).fixedSubgroup
  have hC (y : J) : φ y ∈ C := by
    rw [MulAut.mem_fixedSubgroup]
    change MulAut.centralQuotientAction q r (q (QuotientGroup.mk' (center H) (y : H))) =
      q (QuotientGroup.mk' (center H) (y : H))
    rw [MulAut.centralQuotientAction_apply,
      (MulAut.mem_fixedSubgroup r (y : H)).mp (hJfix y.property)]
  let ψ : J →* C := φ.codRestrict C hC
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact hφ (congrArg Subtype.val hxy)
  obtain ⟨eJ⟩ := hJmodel
  have hJcard : Nat.card J = 29120 := by
    rw [Nat.card_congr eJ.toEquiv, suzuki_card]
  have hseven : 7 ∣ Nat.card C := by
    have hsub : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_injective ψ hψ
    rw [hJcard] at hsub
    exact dvd_trans (by norm_num) hsub
  rcases hExt with ⟨N, hN, ⟨eN⟩, P, hP, ⟨eP⟩, ⟨eQ⟩⟩
  have hNcard : Nat.card N = 32 := by
    rw [Nat.card_congr eN.toEquiv]
    simp [Elementary, C2, Nat.card_eq_fintype_card]
  have hPcard : Nat.card P = 64 := by
    rw [Nat.card_congr eP.toEquiv]
    simp [Elementary, C2, Nat.card_eq_fintype_card]
  have hQcard : Nat.card (((C ⧸ N) ⧸ P)) = 120 := by
    rw [Nat.card_congr eQ.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hCcard : Nat.card C = 32 * 64 * 120 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P]
    rw [hNcard, hPcard, hQcard]
  rw [hCcard] at hseven
  norm_num at hseven

private theorem ru_fixed_product
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (J : Subgroup H) (r : MulAut H) (tables : InvolutionTables)
    (hr : orderOf r = 2)
    (hJfix : J ≤ r.fixedSubgroup)
    (hJmodel : Nonempty (J ≃* SzEight))
    (q : H ⧸ center H ≃* Ru) :
    Nonempty ((MulAut.centralQuotientAction q r).fixedSubgroup ≃*
      Elementary 2 × SzEight) := by
  have hr' : orderOf (MulAut.centralQuotientAction q r) = 2 := by
    exact (orderOf_injective _ (MulAut.centralQuotientAction_injective q) _).trans hr
  rcases tables.ru _ hr' with ⟨hin, hrow⟩
  rcases hrow with hExt | hProd
  · exact (ru_extension_impossible J r hJfix hJmodel q
      hExt).elim
  · exact hProd

/-- The inner quotient actor in the literal Ru row lifts to an inner actor
on the quasisimple group, since its action on the central quotient is faithful. -/
theorem rudvalis_inner_of_source
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (J : Subgroup H) (r : MulAut H) (tables : InvolutionTables)
    (hr : orderOf r = 2)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (hJmodel : Nonempty (J ≃* SzEight))
    (hq : Nonempty ((H ⧸ center H) ≃* SporadicName.ru.Carrier)) :
    ∃ g : H, r = MulAut.conj g := by
  obtain ⟨q⟩ := hq
  have hr' : orderOf (MulAut.centralQuotientAction q r) = 2 := by
    exact (orderOf_injective _ (MulAut.centralQuotientAction_injective q) _).trans hr
  rcases tables.ru _ hr' with ⟨hin, hrow⟩
  rcases hrow with hExt | hProd
  · exact (ru_extension_impossible J r hJ.1 hJmodel q
      hExt).elim
  · exact (MulAut.centralQuotientAction_inner_iff q r).mp hin

/-- A conjugating representative has non-two-central image in the actual
central quotient: the Suzuki component selects the product row, whose order
cannot contain an ambient Sylow two-subgroup. -/
theorem rudvalis_non_two_central_of_source
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (J : Subgroup H) (r : MulAut H) (tables : InvolutionTables)
    (hr : orderOf r = 2)
    (hJ : IsComponentIn J r.fixedSubgroup)
    (hJmodel : Nonempty (J ≃* SzEight))
    (hq : Nonempty ((H ⧸ center H) ≃* SporadicName.ru.Carrier))
    (f : H) (hf : MulAut.conj f = r)
    (_hf2 : orderOf (QuotientGroup.mk' (center H) f) = 2) :
    ¬ TwoCentral (QuotientGroup.mk' (center H) f) := by
  obtain ⟨q⟩ := hq
  have hprod := ru_fixed_product J r tables hr hJ.1 hJmodel q
  obtain ⟨e⟩ := hprod
  intro htwo
  obtain ⟨S₀, hu₀, hz₀⟩ := htwo
  let S : Sylow 2 Ru := S₀.mapSurjective (f := q.toMonoidHom) q.surjective
  have hSle : (S : Subgroup Ru) ≤
      (MulAut.centralQuotientAction q r).fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulAut.mem_fixedSubgroup, ← hf, MulAut.centralQuotientAction_conj,
      MulAut.conj_apply]
    have hc : x * QuotientGroup.mk' (center H) f =
        QuotientGroup.mk' (center H) f * x :=
      congrArg Subtype.val (mem_center_iff.mp hz₀ ⟨x, hx⟩)
    have hc' : q x * q (QuotientGroup.mk' (center H) f) =
        q (QuotientGroup.mk' (center H) f) * q x := by
      simpa only [map_mul] using congrArg q hc
    change q (QuotientGroup.mk' (center H) f) * q x *
      (q (QuotientGroup.mk' (center H) f))⁻¹ = q x
    rw [← hc', mul_inv_cancel_right]
  have hSCard : Nat.card S = 16384 := ru_sylow_card S
  have hCcard : Nat.card ((MulAut.centralQuotientAction q r).fixedSubgroup) =
      4 * 29120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, suzuki_card]
    norm_num [Elementary, C2, Nat.card_eq_fintype_card]
  have hdiv : 16384 ∣ 4 * 29120 := by
    have := Subgroup.card_dvd_of_le hSle
    rwa [hSCard, hCcard] at this
  norm_num at hdiv

end
end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
