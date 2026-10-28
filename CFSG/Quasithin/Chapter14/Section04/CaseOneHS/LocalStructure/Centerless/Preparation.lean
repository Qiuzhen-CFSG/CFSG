module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Geometry
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# The original parabolic center and its Sylow involution

Construct an omitted-point conjugator for the specified rank-three flag,
then use the original center intersections to place Z(I₂) in Z(U) and T
and separate it from V₁. Since T normalizes Z(I₂), a nontrivial center
contains an involution in Ω₁(Z(T)), outside V₁. This prepares the contrary
branch without assuming the order-two bound of 14.3.30.

Source: Aschbacher--Smith, 12.8.9--10 and the setup of 14.3.29--31,
printed pp.852--854 and 1002. The remaining source exclusion is not
asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The fixed original flag has a genuine omitted-point conjugator. -/
theorem source_conjugator (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : ∃ g : G, g ∈ F.P L ∧ g ∉ F.H := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨b, _, hb⟩ := F.exists_naturalFlag_marking L chosen.normalizes
    h.full_L_action h.naturalMarking.coordinates
  obtain ⟨g, hg, hh, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (h.sylow_normalizes_seed structural) (h.full_LT_action structural)
    h.naturalMarking.coordinates b hb
  exact ⟨g, hg, hh⟩

omit [Finite G] in
/-- Normalization uses the defining P-span, with relative normality only. -/
theorem center_normalized (F : InvariantFlag T V 3) :
    (T : Subgroup G) ≤ normalizer (Chapter12.Section08.centerIn (F.I₂ L) : Set G) :=
  (F.binary_sylow_le_P L).trans ((le_normalizer_conjugateSpanBy F.U (F.P L)).trans
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L))))

/-- Z(I₂) lies in the actual Sylow subgroup and misses the marked point. -/
theorem source_center_location (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    Chapter12.Section08.centerIn (F.I₂ L) ≤ F.ZU ∧
      Chapter12.Section08.centerIn (F.I₂ L) ≤ (T : Subgroup G) ∧
      Disjoint (F.Vi 1) (Chapter12.Section08.centerIn (F.I₂ L)) := by
  obtain ⟨g, hgP, hgH⟩ := source_conjugator d earlier hq chosen structural F
  have hi := (source_center_intersections d earlier hq chosen structural alternatives
    F hne g hgP hgH).1
  have hc := (source_closure d earlier hq chosen structural alternatives F hne).2.2
  have hD : Chapter12.Section08.centerIn (F.I₂ L) ≤ F.ZU := hi.ge.trans inf_le_left
  refine ⟨hD, hD.trans ((map_subtype_le (center F.U)).trans
    (source_closure_le_sylow d earlier hq chosen structural alternatives F)), ?_⟩
  rw [disjoint_iff, ← hi, ← inf_assoc]
  have hpZ : F.Vi 1 ≤ F.ZU := hc ▸ inf_le_right
  rw [inf_eq_left.mpr hpZ]
  exact F.point_inf_conjugate_ZU (by decide) hc g
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hgH

/-- The contrary branch supplies an actual central Sylow involution. -/
theorem source_center_involution (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 := by
  obtain ⟨hDZ, hDT, hdis⟩ :=
    source_center_location d earlier hq chosen structural alternatives F hne
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

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
