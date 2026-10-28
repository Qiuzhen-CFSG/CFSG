module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.BinaryRankTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.MarkedSylow
public import Theory.GroupTheory.SylowCenterCover
public import Theory.Mathieu.M12.OrdinaryLocal
public import Theory.Mathieu.M12.Properties.SylowCentralizing
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OrdinaryLocal

/-!
# Initial M₁₂ and Hall--Janko rows with their central covers

A faithful original central involution fixes the literal component Sylow.
Pointwise Sylow fixers are inner on each model and hence on every perfect
central cover. The model Sylow center has order two, so its maximal
centralizer lifts to the full upstairs Sylow-center centralizer. The source
singleton centralizer overgroup places this subgroup in M_L, and properness
of M_L forces equality.

The model applications discharge all these intrinsic premises and construct
the complete 15.1.20(3d) rows for the actual two-core quotients. No exchanged
selection or exhaustive ordinary catalogue is assumed. The remaining initial
families and the 15.1.22 refinement stay with the ordinary catalogue owner.
Source: Aschbacher--Smith, printed pp.1095--1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Maximal two-central model centralizers determine the original M_L,
with the actual two-core quotient and every central two-cover retained. -/
theorem PreExclusionSource.centralizer_eq_of_quotient_sylow_fixers
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] [Finite X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hX : center X = ⊥)
    (hinner : ∀ (Q : Sylow 2 X) (a : MulAut X),
      (∀ x ∈ Q, a x = x) → ∃ t : X, a = MulAut.conj t)
    (hcard : ∀ Q : Sylow 2 X, Nat.card (center Q) = 2)
    (hmax : ∀ t : X, orderOf t = 2 → DoubleCoverCentralizer.TwoCentral t →
      IsCoatom (centralizer ({t} : Set X))) :
    d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let f := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  have hinnerL (P : Sylow 2 d.L) (a : MulAut d.L) (hfix : ∀ x ∈ P, a x = x) :
      ∃ t : d.L, a = MulAut.conj t := by
    apply (MulAut.centralQuotientAction_inner_iff f a).mp
    obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow f a P hfix
    exact hinner Q _ hQ
  apply s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL (MulEquiv.refl d.L)
  · intro P a _ ha
    exact hinnerL P a ha
  · intro P
    obtain ⟨R,_,α,ha,hne,hfix⟩ := s.exists_nontrivial_sylow_fixer (h := h) hG hM hu hL
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq d.L R P
    let a := MulAut.congr (MulAut.conj g) α
    have hR : (R : Subgroup d.L).map (MulAut.conj g).toMonoidHom = P :=
      congrArg (fun Q : Sylow 2 d.L => (Q : Subgroup d.L)) hg
    have hfixP : ∀ x ∈ P, a x = x := by
      intro x hx
      change x ∈ (P : Subgroup d.L) at hx
      rw [← hR] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (MulAut.conj g) (α ((MulAut.conj g).symm ((MulAut.conj g) y))) = (MulAut.conj g) y
      rw [MulEquiv.symm_apply_apply,hfix y hy]
    have ho : orderOf a = 2 :=
      ((MulAut.congr (MulAut.conj g)).orderOf_eq α).trans (orderOf_eq_prime ha hne)
    obtain ⟨t,ht⟩ := hinnerL P a hfixP
    exact SylowCenterCover.center_centralizer_isCoatom f (s.ordinary hL).center_two hX
      P a ho ⟨t,ht.symm⟩ hfixP hcard hmax
/-- The full initial M₁₂ row, with the original two-core quotient and
literal Sylow-center centralizer, including its central two-covers. -/
theorem PreExclusionSource.ordinary20_of_mathieuTwelve_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M12) :
    d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.sporadic .m12 (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  exact s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
    Sporadic.Mathieu.m12_center_eq_bot
    (fun P a => Sporadic.Mathieu.m12_automorphism_inner_of_fixes_sylow a P)
    Sporadic.Mathieu.OrdinaryTwelve.sylow_center_card_two
    Sporadic.Mathieu.OrdinaryTwelve.twoCentral_centralizer_isCoatom

/-- The full initial Hall--Janko row retains the actual ATLAS quotient
and every central two-cover of the source ordinary component. -/
theorem PreExclusionSource.ordinary20_of_jankoTwo_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.J2.Carrier) :
    d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.sporadic .j2 (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  exact s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
    Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot
    Sporadic.LeechRelated.J2.automorphism_inner_of_fixes_sylow
    Sporadic.LeechRelated.J2.sylow_center_card_two
    Sporadic.LeechRelated.J2.OrdinaryLocal.twoCentral_centralizer_isCoatom

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
