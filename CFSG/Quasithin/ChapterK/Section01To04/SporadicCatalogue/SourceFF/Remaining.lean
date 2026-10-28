module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Sieve
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.JankoTwo
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyThree
public import Theory.Representation.Mathieu.M24DegreeSpectrum.CentralCover
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceCompletion

/-!
# Remaining concrete sporadic FF branches

The proved source exclusions leave M12, M22, M24 and HS. The M22 code and
cocode cases are removed on their original markings, leaving its literal
triple-cover action. The M12 ambient recognition transports a concrete heart
exclusion to the source actor. For M24 the center and outer action disappear,
and four-conjugate generation bounds the native faithful irreducible FF degree
by twenty-four. Its remaining native small-module calculation is explicit.

Source: Aschbacher--Smith B.4.2, printed p.86, and K.4, printed pp.457--459.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The actual Aut(M12) heart calculation excludes the marked source action. -/
theorem not_ff_m12_of_native
    (hn : ¬ IsFFModule ChapterH.Section10To12.M12Calculations.Ambient.automorphismRepresentation)
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier)) :
    ¬ IsFFModule ρ := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : M12Source.Hypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, cubic_ratio := h.smallCubic }
  obtain ⟨_,f,_,hf,_,_,⟨E⟩⟩ := M12Source.source_native_ambient_equiv ρ hs e
  intro hff
  exact hn (hff.map_equivariant ρ _ f hf E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))

set_option backward.isDefEq.respectTransparency false in
/-- Source M24 FF modules retain their original vector space and have degree at most 24. -/
theorem m24_native_small (h : RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier)) :
    ∃ (e : G ≃* M24) (σ : Representation (ZMod 2) M24 V),
      σ = ρ.comp e.symm.toMonoidHom ∧ Function.Injective σ ∧ σ.IsIrreducible ∧
      IsFFModule σ ∧ Module.finrank (ZMod 2) V ≤ 24 := by
  rcases h.fitting with rfl
  obtain ⟨q⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := IsQuasisimple.simple
  let : IsSimpleGroup M24 := q.symm.isSimpleGroup
  have htop := LargeMathieu.m24_generalizedFitting_eq_top h.quasisimple q
  let σL := ρ.comp (generalizedFitting G).subtype
  let eL := Representation.Mathieu.M24DegreeSpectrum.CentralCover.groupEquiv σL
    (h.faithful.comp Subtype.val_injective) h.irreducible q
  let d : generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  let e : G ≃* M24 := d.symm.trans eL
  let σ : Representation (ZMod 2) M24 V := ρ.comp e.symm.toMonoidHom
  have hiρ : ρ.IsIrreducible :=
    (irreducible_comp_surjective_iff (generalizedFitting G).subtype
      (fun g => ⟨d.symm g,d.apply_symm_apply g⟩) ρ).mp h.irreducible
  have hiσ : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hiρ
  have hfσ : Function.Injective σ := h.faithful.comp e.symm.injective
  have hffσ : IsFFModule σ := hff.map_equivariant ρ σ e.toMonoidHom e.injective
    (LinearEquiv.refl _ _) (fun g v => by change ρ g v = ρ (e.symm (e g)) v; rw [e.symm_apply_apply])
  have hiT : IsIrreducible (σ.comp (⊤ : Subgroup M24).subtype) :=
    (irreducible_comp_surjective_iff (⊤ : Subgroup M24).subtype
      (fun g => ⟨⟨g,mem_top g⟩,rfl⟩) σ).mpr hiσ
  have hd : Module.finrank (ZMod 2) V ≤ 24 := by
    have hfix : fixedSpace σ ⊤ = ⊥ := by
      have hh := invariants_eq_bot_of_faithful_irreducible σ hfσ hiσ
      exact (show fixedSpace σ ⊤ = σ.invariants by
        ext v
        exact ⟨fun hv g => hv ⟨g, mem_top g⟩, fun hv g => hv g⟩).trans hh
    have hh := finrank_le_of_cubicRatio_le_of_conjugates σ ⊤ hfix
      (n := 4) (m := 1) (r := 6)
      (fun t ht ht2 => by
        obtain ⟨c,hc⟩ := LargeInvolutionGeneration.m24_four_conjugates_generate t
          (orderOf_eq_prime_iff.mpr ⟨ht2,ht⟩)
        exact ⟨c,hc.ge⟩)
      m24_twoRank_le_six
      (by simpa only [Nat.cast_one] using (isFFModule_iff_cubicRatio_le_one σ).mp hffσ)
    simpa only [Nat.mul_one,one_mul] using hh
  exact ⟨e,σ,rfl,hfσ,hiσ,hffσ,hd⟩

/-- The remaining native M24 small-module exclusion transfers to the source. -/
theorem not_ff_m24_of_native_small
    (hn : ∀ σ : Representation (ZMod 2) M24 V,
      Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) V ≤ 24 →
      ¬ IsFFModule σ)
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier)) :
    ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨_,σ,_,hf,hi,hffσ,hd⟩ := m24_native_small h hff he
  exact hn σ hf hi hd hffσ

/-- Seven actual source branches of the eleven-entry catalogue are excluded. -/
theorem remaining_four_central_quotient (h : RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L)) :
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier) := by
  rcases remaining_central_quotient h hff hm with h12 | h22 | h23 | h24 | h2 | hhs
  · exact Or.inl h12
  · exact Or.inr (Or.inl h22)
  · exact (not_ff_m23 h h23 hff).elim
  · exact Or.inr (Or.inr (Or.inl h24))
  · exact (not_ff_j2 h h2 hff).elim
  · exact Or.inr (Or.inr (Or.inr hhs))

/-- The simple M22 actions are excluded; its literal triple action remains marked. -/
theorem remaining_marked_branches (h : RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L)) :
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier) ∨
    Nonempty (M22Source.MarkedTripleModel ρ L) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier) := by
  rcases remaining_four_central_quotient h hff hm with h12 | h22 | h24 | hhs
  · exact Or.inl h12
  · exact Or.inr (Or.inl (m22_triple_of_ff h hff h22))
  · exact Or.inr (Or.inr (Or.inl h24))
  · exact Or.inr (Or.inr (Or.inr hhs))
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
