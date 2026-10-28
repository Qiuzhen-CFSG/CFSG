module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Preparation

/-!
# Preparing the contrary center at the original G,T

The local center intersections put Z(I₂) in the original Sylow subgroup
and separate it from V₁. Relative normality then produces a central Sylow
involution if Z(I₂) is nontrivial. Its L-orbit and its join with V are
reduced LT-modules by B.2.14 and the local structural theorem.

This is the initial input to the original shifted-center and Goldschmidt
argument, not its centerlessness conclusion. The literal involution and
orbit feed source_contrary_reduced_module_at in this file.
Source: Aschbacher--Smith 14.3.28--31, pp.1002--1003, and B.2.14, p.78.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Select the actual omitted-point conjugator inside L. -/
theorem source_conjugator_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  obtain ⟨g, _, hgP, hgH⟩ :=
    CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  exact ⟨g, hgP, hgH⟩

theorem source_center_location_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    Chapter12.Section08.centerIn (F.I₂ L) ≤ F.ZU ∧
      Chapter12.Section08.centerIn (F.I₂ L) ≤ (T : Subgroup G) ∧
      Disjoint (F.Vi 1) (Chapter12.Section08.centerIn (F.I₂ L)) := by
  obtain ⟨g, hgP, hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  have hi := (source_center_intersections_at d earlier hq chosen structural alternatives
    F hne g hgP hgH).1
  have hc := (source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  have hD : Chapter12.Section08.centerIn (F.I₂ L) ≤ F.ZU := hi.ge.trans inf_le_left
  refine ⟨hD, hD.trans ((map_subtype_le (center F.U)).trans
    (source_closure_le_sylow_at d earlier hq chosen structural alternatives F)), ?_⟩
  rw [disjoint_iff, ← hi, ← inf_assoc]
  have hpZ : F.Vi 1 ≤ F.ZU := hc ▸ inf_le_right
  rw [inf_eq_left.mpr hpZ]
  exact F.point_inf_conjugate_ZU (by decide) hc g
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hgH

theorem source_center_involution_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 := by
  obtain ⟨hDZ, hDT, hdis⟩ :=
    source_center_location_at d earlier hq chosen structural alternatives F hne
  let D := Chapter12.Section08.centerIn (F.I₂ L)
  let N := D.subgroupOf (T : Subgroup G)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hDT).mpr (center_normalized F)
  have hn : N ≠ ⊥ := by
    intro he
    have hm := map_subgroupOf_eq_of_le hDT
    change N.map (T : Subgroup G).subtype = D at hm
    rw [he, Subgroup.map_bot] at hm
    exact hI hm.symm
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨A, _, hAN, hcard, hAZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) N ((nontrivial_iff_ne_bot N).mpr hn)
  have ha : A ≠ ⊥ := (one_lt_card_iff_ne_bot A).mp (by omega)
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr ha
  obtain ⟨e, he⟩ := exists_ne (1 : A)
  have he1 : ((e : T) : G) ≠ 1 := fun hh => he (Subtype.ext (Subtype.ext hh))
  have he2 : ((e : T) : G) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := e)
    rw [hcard] at hh
    exact congrArg (fun x : A => ((x : T) : G)) hh
  have heD : ((e : T) : G) ∈ D := hAN e.property
  have heZ : ((e : T) : G) ∈ Chapter12.Section08.centerIn (T : Subgroup G) :=
    mem_map_of_mem (T : Subgroup G).subtype (hAZ e.property)
  refine ⟨e, orderOf_eq_prime_iff.mpr ⟨he2, he1⟩, heD,
    (omegaOneAmbient_le_iff _ _).mp le_rfl _ heZ he2, hDZ heD, ?_⟩
  intro hp
  exact he1 (show ((e : T) : G) ∈ (⊥ : Subgroup G) from
    (disjoint_iff.mp hdis) ▸ (show ((e : T) : G) ∈ F.Vi 1 ⊓ D from ⟨hp, heD⟩))

theorem source_involution_orbit_reduced_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (e : G) (he : orderOf e = 2) (heZ : e ∈ sylowOmega T) :
    IsPReduced 2 ((conjugateSpanBy (zpowers e) L).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let : IsElementaryAbelian 2 (zpowers e) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      have hh := pow_card_eq_one' (x := x)
      simpa only [Nat.card_zpowers, he] using hh }
  have heT : e ∈ (T : Subgroup G) :=
    (map_subtype_le (center (T : Subgroup G))) (omegaOneAmbient_le _ heZ)
  have hZC : zpowers e ≤ centralizer (T : Set G) :=
    zpowers_le.mpr (omega_centralizes_sylow heZ)
  have hr := reduced_conjugateSpan_of_sylow_central T
    (L ⊔ (T : Subgroup G)) (zpowers e) le_sup_right (zpowers_le.mpr heT) hZC
    (source_LT_characteristic d chosen F)
  have hn : (T : Subgroup G) ≤ normalizer (zpowers e : Set G) :=
    (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  rwa [conjugateSpanBy_sup_of_normalizes_seed _ _ _ hn
    ((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).sylow_normalizes_at structural)] at hr

theorem source_seed_sup_involution_orbit_reduced_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (e : G) (he : orderOf e = 2) (heZ : e ∈ sylowOmega T) :
    IsPReduced 2 ((V ⊔ conjugateSpanBy (zpowers e) L).subgroupOf
      (L ⊔ (T : Subgroup G))) := by
  have hV : V ≤ L ⊔ (T : Subgroup G) := chosen.le_sylow.trans le_sup_right
  have heT : e ∈ (T : Subgroup G) :=
    (map_subtype_le (center (T : Subgroup G))) (omegaOneAmbient_le _ heZ)
  have hE : conjugateSpanBy (zpowers e) L ≤ L ⊔ (T : Subgroup G) :=
    conjugateSpanBy_le (zpowers_le.mpr (mem_sup_right heT))
      (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer)
  rw [subgroupOf_sup hV hE]
  exact ((structural L (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).source).2.2 V chosen).2.1.sup
    (source_involution_orbit_reduced_at d earlier hq chosen structural F e he heZ)

theorem source_contrary_reduced_module_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      IsPReduced 2 ((V ⊔ conjugateSpanBy (zpowers e) L).subgroupOf
        (L ⊔ (T : Subgroup G))) := by
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution_at d earlier hq chosen structural alternatives F hne hI
  exact ⟨e, he, heI, heT, heU, heV,
    source_seed_sup_involution_orbit_reduced_at d earlier hq chosen structural F e he heT⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
