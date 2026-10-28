module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.ModelControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLargeTwentyThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLargeTwentyFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.HeldRudvalis
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.MathieuEleven
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement
public import Theory.Mathieu.M12.Properties.SylowFixedActions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers

/-!
# Surviving sporadic quotients before exchanged selection

The actual M₁₂, M₂₂, M₂₃, M₂₄, J₂ and Held Sylow-fixer bounds make the
omega center of the original normalizer quotient have order two. The
faithful central seed supplies the lower bound, including for nontrivial
central two-covers. The same quotient marking and the initial centralizer
calculations supply every clause of Ordinary22 row (5) once an escaping
source parabolic is placed by (*).

The final reduction and marker application expose exactly the unfinished
geometry: an escaping member of the literal source family. They do not
assert that such a member exists. Its construction and the HS/Ru exclusions
remain with qt-e-15122-ordinary-pre-exclusion; (*) remains with
qt-e-15122-parabolic-placement, with final discharge by
qt-e-15122-pre-exclusion-catalogue. The Cubic extension discharges escape
independently when the original prime is three.

Source: Aschbacher--Smith 15.1.20(3d), 15.1.22(**),(!),(5),
printed pp.1097--1100, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Quotient-model control retains arbitrary central two-covers of the original component. -/
theorem PreExclusionSource.ordinary_quotient_model_control
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2) :
    Nat.card d.plusOmega = 2 ∧
      (¬ d.localThreeResidual ≤ d.ML → d.OrdinaryCentralizerIdentity) := by
  have o := s.ordinary hL
  have hb : Nat.card d.plusOmega ≤ 2 := by
    rw [d.ordinary_plusOmega_card]
    exact d.ordinary_omega_bound_of_model hL o.center_eq s.component_sylow e hfix
  have hZ1 := d.marked_le_sylow h hTM
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact d.central_seed_plus_ne_bot hu hZ1 o.central_normalizes
      (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1 o.central_normalizes))
  have hc : Nat.card d.plusOmega = 2 := by
    have hh := (one_lt_card_iff_ne_bot _).mpr hne
    omega
  refine ⟨hc, ?_⟩
  intro hout
  apply d.ordinary_residual_centralizer_of_model hTM hu hL o.center_eq o.center_two
    o.central_normalizes s.component_sylow hZ1 e hfix
  intro hR
  exact hout (le_inf hR d.localThreeResidual_le_component)

/-- All six surviving sporadic quotients discharge the intrinsic model premises in (**). -/
theorem PreExclusionSource.sporadic_quotient_model_control
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    Nat.card d.plusOmega = 2 ∧
      (¬ d.localThreeResidual ≤ d.ML → d.OrdinaryCentralizerIdentity) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A _ hfix => Sporadic.Mathieu.m12_faithful_sylow_fixed_action_card_le_two
        P A.subtype A.subtype_injective (fun a x => hfix a a.property x.val x.property))
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A hA hfix => @Sporadic.Mathieu.m22_elementary_sylow_fixer_card_le_two
        Sporadic.Mathieu.m22_center_eq_bot P A hA hfix)
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A hA hfix => @Sporadic.Mathieu.m23_elementary_sylow_fixer_card_le_two
        Sporadic.Mathieu.M23Geometry.m23_center_eq_bot P A hA hfix)
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A hA hfix => @Sporadic.Mathieu.m24_elementary_sylow_fixer_card_le_two
        Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot P A hA hfix)
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A hA hfix => @Sporadic.LeechRelated.J2.elementary_sylow_fixer_card_le_two
        Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot P A hA hfix)
  · exact s.ordinary_quotient_model_control (h := h) hTM hu hL e
      (fun P A hA hfix => @Held.elementary_sylow_fixer_card_le_two P A hA hfix)

/-- Reuse the proved initial centralizer arguments with the same quotient marking. -/
theorem PreExclusionSource.surviving_sporadic_centralizer_eq
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :
    d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  let : Finite name.Carrier := Finite.of_equiv (d.L ⧸ pCore 2 d.L) e.toEquiv
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup name.Carrier := ec.symm.isSimpleGroup
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
      Sporadic.Mathieu.m12_center_eq_bot
      (fun P a => Sporadic.Mathieu.m12_automorphism_inner_of_fixes_sylow a P)
      Sporadic.Mathieu.OrdinaryTwelve.sylow_center_card_two
      Sporadic.Mathieu.OrdinaryTwelve.twoCentral_centralizer_isCoatom
  · exact s.centralizer_eq_of_quotient_residual_control (h := h) hG hempty hM hu hL e
      Sporadic.Mathieu.m22_center_eq_bot
      (fun Q a ha => Sporadic.Mathieu.M22SylowPointwise.automorphism_inner_of_fixes_sylow a Q ha)
      Sporadic.Mathieu.m22_sylow_center_card_le_two
      Sporadic.Mathieu.OrdinaryTwentyTwo.centralizer_eq_of_residual_le
  · apply s.centralizer_eq_of_quotient_residual_control (h := h) hG hempty hM hu hL e
        Sporadic.Mathieu.M23Geometry.m23_center_eq_bot
    · intro Q a ha
      obtain ⟨g,hg⟩ := Sporadic.Mathieu.m23_conj_surjective a
      exact ⟨g,hg.symm⟩
    · exact Sporadic.Mathieu.m23_sylow_center_card_le_two
    · intro U t ht _ hCU hR
      exact Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.centralizer_eq_of_residual_le
        U t ht hCU hR
  · apply s.centralizer_eq_of_quotient_residual_control (h := h) hG hempty hM hu hL e
        Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
    · intro Q a ha
      obtain ⟨g,hg⟩ := Sporadic.Mathieu.M24OuterRestriction.conj_surjective a
      exact ⟨g,hg.symm⟩
    · exact Sporadic.Mathieu.m24_sylow_center_card_le_two
    · exact Sporadic.Mathieu.M24InvolutionCentralizers.OrdinarySource.centralizer_eq_of_residual_le
  · exact s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
      Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot
      Sporadic.LeechRelated.J2.automorphism_inner_of_fixes_sylow
      Sporadic.LeechRelated.J2.sylow_center_card_two
      Sporadic.LeechRelated.J2.OrdinaryLocal.twoCentral_centralizer_isCoatom
  · apply s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
      Held.LocalPairs.center_eq_bot
    · intro P a ha
      obtain ⟨t,ht⟩ := Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow
        Held.Realization.normalizer_surjective P a ha
      exact ⟨t,ht.symm⟩
    · exact Held.LocalPairs.SylowGeometry.Calculations.inner_center_card
    · exact Held.OrdinaryLocal.twoCentral_centralizer_isCoatom

/-- An actual escaping source parabolic, placed by (*), proves every clause of row (5). -/
theorem PreExclusionSource.ordinary22_sporadic_of_source_parabolic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    {P : Subgroup G} (hP : d.IsSourceParabolic P) (hout : ¬ P ≤ d.ML) :
    d.Ordinary22Alternatives := by
  have hR := (s.parabolic_family_residual_escape (h := h) hG hu hM.1.2 hplacement
    {P} (by intro Q hQ; rcases hQ with rfl; exact hP)
    (by simpa only [csSup_singleton] using hout)).2
  exact .sporadic name hn
    ⟨(QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e⟩
    (s.surviving_sporadic_centralizer_eq (h := h) hG hempty hM hu hL hn e)
    ((s.sporadic_quotient_model_control (h := h) hM.1.2 hu hL hn e).2 hR)

/-- For each surviving named model, only containment of the entire source family
can prevent the row-(5) conclusion after (*). The omega-center order is unconditional. -/
theorem PreExclusionSource.surviving_sporadic_refinement
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {name : SporadicName}
    (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) :
    Nat.card d.plusOmega = 2 ∧
      (d.Ordinary22Alternatives ∨ ∀ P ∈ d.sourceParabolics, P ≤ d.ML) := by
  classical
  refine ⟨(s.sporadic_quotient_model_control (h := h) hM.1.2 hu hL hn e).1, ?_⟩
  by_cases hall : ∀ P ∈ d.sourceParabolics, P ≤ d.ML
  · exact .inr hall
  · obtain ⟨P,hP⟩ := not_forall.mp hall
    obtain ⟨hP,hout⟩ := Classical.not_imp.mp hP
    exact .inl (s.ordinary22_sporadic_of_source_parabolic (h := h)
      hG hempty hM hu hL hn e hplacement hP hout)

/-- Exhaust the initial sporadic row at the original d. The exact remaining
obstructions are HS, Ru, or containment of every literal source parabolic. -/
theorem PreExclusionSource.ordinary22_or_sporadic_obstruction
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (hn3 : name ≠ .j3) (hn4 : name ≠ .j4)
    (e : (d.L ⧸ pCore 2 d.L) ≃* name.Carrier)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) :
    d.Ordinary22Alternatives ∨ name = .hs ∨ name = .ru ∨
      (Nat.card d.plusOmega = 2 ∧ ∀ P ∈ d.sourceParabolics, P ≤ d.ML) := by
  have hsurv (hn : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨
      name = .m24 ∨ name = .j2 ∨ name = .he) :
      d.Ordinary22Alternatives ∨ name = .hs ∨ name = .ru ∨
        (Nat.card d.plusOmega = 2 ∧ ∀ P ∈ d.sourceParabolics, P ≤ d.ML) := by
    obtain ⟨hc,ha | hall⟩ := s.surviving_sporadic_refinement (h := h)
      hG hempty hM hu hL hn e hplacement
    · exact .inl ha
    · exact .inr (.inr (.inr ⟨hc,hall⟩))
  cases name with
  | m11 => exact .inl (s.ordinary22_of_mathieuEleven_quotient (h := h) hG hM hu hL e)
  | m12 => exact hsurv (.inl rfl)
  | m22 => exact hsurv (.inr (.inl rfl))
  | m23 => exact hsurv (.inr (.inr (.inl rfl)))
  | m24 => exact hsurv (.inr (.inr (.inr (.inl rfl))))
  | j2 => exact hsurv (.inr (.inr (.inr (.inr (.inl rfl)))))
  | he => exact hsurv (.inr (.inr (.inr (.inr (.inr rfl)))))
  | j3 => exact (hn3 rfl).elim
  | j4 => exact (hn4 rfl).elim
  | hs => exact .inr (.inl rfl)
  | ru => exact .inr (.inr (.inl rfl))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Apply the sporadic refinement to the component constructed from the original
marker. The row, Z₁, prime, and pre-exclusion witness are retained at the same d. -/
theorem PreparedChosenModule.source_preExclusion_sporadic_refinement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ (name : SporadicName), name ≠ .j3 → name ≠ .j4 →
        ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier) →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) →
        d.Ordinary22Alternatives ∨ name = .hs ∨ name = .ru ∨
          (Nat.card d.plusOmega = 2 ∧ ∀ P ∈ d.sourceParabolics, P ≤ d.ML)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL name hn3 hn4 e hplacement =>
    s.ordinary22_or_sporadic_obstruction (h := h)
      hG hempty hM hu hL name hn3 hn4 e hplacement⟩

end CFSG.Quasithin.Chapter15.Section01
