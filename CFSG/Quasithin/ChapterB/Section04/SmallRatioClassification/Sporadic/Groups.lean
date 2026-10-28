module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.HigmanSims
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoOneExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoFourExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoFourLyons.Source

/-!
# Sporadic source actions with a marked involution of small displacement

The original chief action in 13.5.21 has an involution moving at most two
binary dimensions. Four conjugates bound a J2 or M24 action by degree eight;
five conjugates bound an HS action by degree ten. Faithful degree lower
bounds contradict these estimates. M11 already has involution codimension
at least four, and the full cubic-source exclusions settle J1, J4, Held and
Rudvalis. Central covers and outer involutions are retained throughout.

Source: Aschbacher--Smith B.4.5, K.4 and 13.5.21; the native conjugate
generation and faithful degree theorems cited in the imported modules.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open _root_.Sporadic.Mathieu
open ComponentRecognition.KnownFFTypes.Sporadic
open ChapterK.SporadicCatalogue
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original literal F* data supplies the older cubic-source record. -/
private theorem sourceHypotheses (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting G)) :
    ChapterK.SporadicCatalogue.SourceHypotheses ρ := {
  sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
  irreducible := h.irreducible, cubic_le_two := h.smallCubic }

/-- J2 is impossible when the original ambient action contains the marked small involution. -/
theorem j2_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  have hz2 := Theory.SpecificGroups.J2HSMultipliers.J2.center_isPGroup_of_quotient_equiv e
  have hk := normal_p_subgroup_le_ker (ρ.comp (generalizedFitting G).subtype)
    (center (generalizedFitting G)) hz2
  have hZ : center (generalizedFitting G) = ⊥ := by
    apply bot_unique
    simpa only [(ρ.comp (generalizedFitting G).subtype).ker_eq_bot_iff.mpr
      (h.faithful.comp (generalizedFitting G).subtype_injective)] using hk
  let eL : generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := h.quasisimple.simple
  let : IsSimpleGroup _root_.Sporadic.LeechRelated.J2.Carrier := e.symm.isSimpleGroup
  let : IsSimpleGroup (generalizedFitting G) := eL.isSimpleGroup
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  obtain ⟨c,hc⟩ := _root_.Sporadic.LeechRelated.J2.FourConjugateGeneration.involution_conjugate_generation_bound
    eL t (orderOf_eq_prime_iff.mp ht).2 (orderOf_eq_prime_iff.mp ht).1
  have hu := finrank_le_mul_fixedCodim_of_conjugates ρ (generalizedFitting G) hfix t c hc
  let σ := (ρ.comp (generalizedFitting G).subtype).comp eL.symm.toMonoidHom
  have hfσ : Function.Injective σ :=
    h.faithful.comp ((generalizedFitting G).subtype_injective.comp eL.symm.injective)
  have hiσ : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eL.symm.toMonoidHom eL.symm.surjective _).mpr h.irreducible
  have hlo := Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hfσ hiσ (by omega)
  omega

/-- The HS degree bound uses all ambient involution classes, including outer ones. -/
theorem hs_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
  rcases h.fitting with rfl
  let hs : Leech.HigmanSims.SourceHypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, centralQuotient := he }
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  obtain ⟨e⟩ := he
  have hc := Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e
  obtain ⟨_,σ,hf,_,_⟩ := Leech.HigmanSims.Twenty.Inner.exists_marked_carrier_representation hs hc
  obtain ⟨a,ha,hdegree⟩ := Leech.HigmanSims.AbsoluteWindow.finrank_eq_fixed_add_twenty_mul σ hf
  obtain ⟨c,hc⟩ := hs.five_conjugates t
    (orderOf_eq_prime_iff.mp ht).2 (orderOf_eq_prime_iff.mp ht).1
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := IsQuasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  have hu := finrank_le_mul_fixedCodim_of_conjugates ρ (generalizedFitting G) hfix t c hc
  omega

/-- A faithful M24 source action has degree at least eleven, whereas a small marked
involution and four-conjugate generation would force degree at most eight. -/
theorem m24_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
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
  have hfix : fixedSpace σ ⊤ = ⊥ := by
    have hh := invariants_eq_bot_of_faithful_irreducible σ hfσ hiσ
    exact (show fixedSpace σ ⊤ = σ.invariants by
      ext v
      exact ⟨fun hv g => hv ⟨g,mem_top g⟩, fun hv g => hv g⟩).trans hh
  have hto : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
  obtain ⟨c,hc⟩ := LargeInvolutionGeneration.m24_four_conjugates_generate (e t) hto
  have hu := finrank_le_mul_fixedCodim_of_conjugates σ ⊤ hfix (e t) c hc.ge
  have hcod : fixedCodim σ (zpowers (e t)) = fixedCodim ρ (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) (ρ (e.symm (e t)) - LinearMap.id).range = _
    rw [e.symm_apply_apply]
  rw [hcod] at hu
  have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank σ hfσ
    (by decide : Nat.Prime 23) (by decide : 23 ≠ 2)
    (show 23 ∣ Nat.card M24 by rw [m24_order]; norm_num)
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_twentyThree] at hlo
  omega
/-- The M11 source displacement bound applies through every central cover. -/
theorem m11_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m11.Carrier))
    (t : G) (ht : orderOf t = 2) (hd : fixedCodim ρ (zpowers t) ≤ 2) : False := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hlo := m11_involution_fixedCodim_ge_four ρ (sourceHypotheses h) e t
    (orderOf_eq_prime_iff.mp ht).2 (orderOf_eq_prime_iff.mp ht).1
  omega

/-- Four sporadic carrier exclusions already hold on the full cubic source domain. -/
theorem other_cubic_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j1.Carrier) ∨
      Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j4.Carrier) ∨
      Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.he.Carrier) ∨
      Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.ru.Carrier)) : False := by
  rcases h.fitting with rfl
  rcases he with hj1 | hj4 | hhe | hru
  · exact sourceExclusion_j1 ρ (sourceHypotheses h) hj1
  · exact sourceExclusion_j4_of_bounded_geometry boundedSourceExclusion_j4
      ρ (sourceHypotheses h) hj4
  · exact SourceFF.held_impossible h hhe
  · exact sourceExclusion_ru ρ (sourceHypotheses h) hru

end CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
