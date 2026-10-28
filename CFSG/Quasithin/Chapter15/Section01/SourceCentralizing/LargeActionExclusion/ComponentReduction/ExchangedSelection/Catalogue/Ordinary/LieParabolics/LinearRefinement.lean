module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.QuinticSylow
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeFree

/-!
# Binary linear parabolics and residual control before exchanged selection

The original permuting quintic actor would give a subgroup of the actual
SL₄(2) or SL₅(2) quotient containing a full Sylow, with order divisible by
five and prime to three. The intrinsic flag theorem identifies that subgroup
with the Sylow, a contradiction. Thus the source prime is three, and the
already proved cubic-residual escape applies to the same quotient. The
intrinsic Sylow-fixer bound gives the literal residual-centralizer identity.

Both M_L and M ∩ L are actual proper flag parabolics under the original
linear equivalence, and M_L contains the Sylow-center centralizer. The
conditional Ordinary22 theorem therefore retains exactly the remaining
generation clause. Its construction stays with this ordinary catalogue
owner, qt-e-15122-ordinary-pre-exclusion; this module does not claim the
complete binary linear row. Both original-marker applications preserve d,
Z₁, row and prime. Earlier independent source premises retain their existing
producers and final discharge by qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.20(3e), 15.1.21(ii), 15.1.22(7),
printed pp.1094--1100, refs/quasithin.pdf. Only the original pre-selection
hypotheses enter the unconditional parabolic and residual calculation.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private noncomputable def linearQuotient
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := by
  have hz : center d.L = ⊥ := by
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,(linear hn).1,card_bot]
  exact ((QuotientGroup.quotientMulEquivOfEq
    ((s.ordinary hL).center_eq.symm.trans hz)).trans QuotientGroup.quotientBot).trans e

/-- The original prime-five actor is impossible in both binary linear models. -/
theorem PreExclusionSource.not_binaryLinear_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  obtain ⟨P,H,a,b,hPH,h5,hc⟩ := s.quintic_two_five_sylow_overgroup (h := h) hG hM hJ hL
    (linearQuotient (h := h) s hL hn e) (linear hn)
  have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
      ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
  let f := BinaryLinear.OuterCyclic.slEquivLinear n
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_equiv (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) f.toEquiv
  let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
  let K := H.map f.toMonoidHom
  have hQK : (Q : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n)) ≤ K := map_mono hPH
  have hK3 : ¬3 ∣ Nat.card K := by rwa [card_map_of_injective f.injective]
  have he : K = (Q : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n)) := by
    rcases hn with rfl | rfl <;>
      exact BinaryLinear.SylowFlagOvergroups.eq_sylow_of_not_three_dvd Q K hQK hK3
  have hK5 : 5 ∣ Nat.card K := by rwa [card_map_of_injective f.injective]
  obtain ⟨r,hr⟩ := Q.isPGroup'.exists_card_eq
  rw [he,hr] at hK5
  exact (by decide : ¬5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hK5)

/-- Binary SL₄ and SL₅ force the original source prime to be three. -/
theorem PreExclusionSource.prime_three_of_binaryLinear
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : p = 3 := by
  rcases hp with hp | rfl
  · exact hp
  · exact (s.not_binaryLinear_of_prime_five (h := h) hG hM hJ hL hn e).elim

/-- Both binary linear rows have the literal residual escape and centralizer
identity before exchanged selection. Only their parabolic generation is separate. -/
theorem PreExclusionSource.binaryLinear_residual_control
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    p = 3 ∧ ¬d.localThreeResidual ≤ d.ML ∧ d.OrdinaryCentralizerIdentity := by
  have hp3 := s.prime_three_of_binaryLinear (h := h) hp hG hM hJ hL hn e
  subst p
  have hf := Facts.of_equiv (linearQuotient (h := h) s hL hn e) (linear hn)
  have hr := s.localThreeResidual_escape_of_cubic_model (h := h) hG hf
  exact ⟨rfl,hr,(s.linear_model_control (h := h) hM.1.2 hu hL hn e).2 hr⟩

/-- Both original local intersections are proper parabolics under the same
linear marking, and their literal residual-centralizer identity holds. -/
theorem PreExclusionSource.binaryLinear_parabolic_refinement
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    p = 3 ∧ d.OrdinaryLinearParabolic e d.ML ∧
      d.OrdinaryLinearParabolic e (M ⊓ d.L) ∧
      d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML ∧
      d.OrdinaryCentralizerIdentity := by
  have hc := s.binaryLinear_residual_control (h := h) hp hG hM hJ hu hL hn e
  have hl := s.local_intersections (h := h) hG hu hM.1.2
  have ho := s.ordinary hL
  exact ⟨hc.1,
    s.linear_flag_overgroup (h := h) (by omega) e d.ML ho.sylow_le_local ho.local_proper,
    s.linear_flag_overgroup (h := h) (by omega) e (M ⊓ d.L) hl.2.2.2.1 hl.2.2.2.2.1,
    s.linear_centralizer_le (h := h) hG hM hu hL hn e,hc.2.2⟩

/-- Generation is the sole remaining clause for the original binary linear
Ordinary22 row; all parabolic and residual clauses are discharged here. -/
theorem PreExclusionSource.ordinary22_linear_of_generation
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hgen : d.ML ⊔ (M ⊓ d.L) = d.L) : d.Ordinary22Alternatives := by
  obtain ⟨_,hML,hMI,hZ,hC⟩ := s.binaryLinear_parabolic_refinement (h := h)
    hp hG hM hJ hu hL hn e
  exact .linear n hn e hML hMI hZ hgen hC

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the binary linear residual calculation without changing the source
marker, component, source row or prime. -/
theorem PreparedChosenModule.source_preExclusion_binary_linear_residual_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ (n : ℕ), (n = 4 ∨ n = 5) →
          (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
          m.prime = 3 ∧ ¬d.localThreeResidual ≤ d.ML ∧ d.OrdinaryCentralizerIdentity) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn e =>
    s.binaryLinear_residual_control (h := h) hp hG hM hJ hu hL hn e⟩

/-- Assemble the ordinary binary linear row at the original marker once
its remaining generation clause is proved by the ordinary catalogue owner. -/
theorem PreparedChosenModule.source_preExclusion_binary_linear_of_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ (n : ℕ), (n = 4 ∨ n = 5) →
          (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
          (d.ML ⊔ (M ⊓ d.L) = d.L → d.Ordinary22Alternatives)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn e hgen =>
    s.ordinary22_linear_of_generation (h := h) hp hG hM hJ hu hL hn e hgen⟩


end CFSG.Quasithin.Chapter15.Section01
