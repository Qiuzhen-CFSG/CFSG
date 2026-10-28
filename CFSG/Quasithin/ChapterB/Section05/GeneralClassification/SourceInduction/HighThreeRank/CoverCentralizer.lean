module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Involutions
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Structure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.ModelRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction

/-!
# Assembly of the cover, three-core and odd-centralizer arguments

Construct a lifted component using the complete existential B.5.2 input.
The full B.5.5 model conclusion makes every component have positive three-rank;
A.2.1 and the multiplier bound from I.1.3 give center order one or three.
The ambient rank bound and cyclic-Sylow transfer then establish both layer
identities. Transfer the strict rank inequality through the actual projection.
A trivial
component center kills the cover's three-core, hence the actor's three-core.
Otherwise its cubic center is first omega of a cyclic three-core. Lifting
involutions and applying coprime action then proves the centralizer odd.

`reduction` constructs the requested dichotomy from four explicit universal
earlier inputs: B.5.2 (`SourceConstruction.CoverInput`) and B.5.5
(`SourceConstruction.ComponentsInput`), produced by
`qt-b05-quotient-components`; A.2.1 (`SourceConstruction.SemisimpleInput`),
produced by `qt-a-02`; and the order-divides-48 consequence of I.1.3
(`SourceConstruction.MultiplierInput`), produced by `qt-i-01`.
`component_rank_pos` uses only the complete B.5.5 input.
The final source assembly must discharge these inputs. No B.5.6, B.5.7,
A.3.18 alternative, lifted-cover witness or outer-shape premise is assumed.
Source: Aschbacher–Smith, B.5.7, printed pp.105–106, combined manuscript of
1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
universe u v

private theorem normal_of_eq_layer {G : Type*} [Group G] {L : Subgroup G}
    (hL : IsComponent G L) (he : componentLayer G = L) : L.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  apply (hL.map_conj g).eq_of_le hL
  exact (show L.map (MulAut.conj g).toMonoidHom ≤ componentLayer G from
    le_sSup (hL.map_conj g)).trans he.le

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- All remaining fields of the requested dichotomy follow from the structural
cover target. In particular rank, normality, cyclicity, omega and oddness are
proved here, rather than supplied as fields of that target. -/
theorem reduction_of_liftedCover (hyp : FFHypothesis K ρ)
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) (d : LiftedCover K G L) :
    (IsSQTK K L ∧ generalizedFitting G = L ⊔ center G) ∨
      Nonempty (NoncentralContext K G L) := by
  classical
  by_cases hc : pCore 3 G ≤ center G
  · left
    refine ⟨d.component_sqtk, ?_⟩
    rw [d.fitting]
    exact le_antisymm
      (sup_le (sup_le le_sup_left (hc.trans le_sup_right)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  · right
    have hrLift : 1 < primeRank 3 d.lift :=
      lift_rank d.cover.projection d.lift d.component_image hr
    have hrCover : primeRank 3 d.cover.Cover ≤ 2 :=
      d.cover.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide)
    have hz : Nat.card (center d.lift) = 3 := by
      rcases d.center_order with hz | hz
      · have hzbot : center d.lift = ⊥ := (center d.lift).card_eq_one.mp hz
        have hcore : pCore 3 d.cover.Cover = ⊥ :=
          threeCore_eq_bot_of_component_rank d.component hzbot
            (by omega) hrCover
        have hcoreG : pCore 3 G = ⊥ := by
          rw [← d.cover.map_pCore 3, hcore, Subgroup.map_bot]
        exact (hc (hcoreG ▸ bot_le)).elim
      · exact hz
    let : d.lift.Normal := normal_of_eq_layer d.component d.lift_layer
    obtain ⟨hcyc, hω⟩ := cyclic_threeCore_and_omega d.component hrLift hrCover hz
    have hodd := odd_centralizer d.cover d.component d.component_image hyp.twoCore
      d.fitting hcyc (hω.le.trans (map_subtype_le _))
    exact ⟨{
      cover := d.cover
      lift := d.lift
      component := d.component
      component_image := d.component_image
      lift_rank := hrLift
      lift_layer := d.lift_layer
      layer := d.layer
      normal := normal_of_eq_layer hL d.layer
      component_sqtk := d.component_sqtk
      fitting := d.fitting
      noncentral := hc
      odd_centralizer := hodd
      cyclic_threeCore := hcyc
      omega := hω }⟩

/-- The cover and odd-centralizer reduction in B.5.7, from complete earlier
source implications. The lifted cover and every noncentral-context field
are constructed, retaining the original component and representation. -/
theorem reduction (h52 : SourceConstruction.CoverInput K)
    (h55 : SourceConstruction.ComponentsInput.{u,v} K)
    (hA : SourceConstruction.SemisimpleInput K)
    (hI : SourceConstruction.MultiplierInput K)
    (hyp : FFHypothesis K ρ) (hL : IsComponent G L) (hr : 1 < primeRank 3 L) :
    (IsSQTK K L ∧ generalizedFitting G = L ⊔ center G) ∨
      Nonempty (NoncentralContext K G L) := by
  obtain ⟨d⟩ := SourceConstruction.exists_liftedCover ρ h52 h55 hA hI hyp hL hr
  exact reduction_of_liftedCover hyp hL hr d

/-- B.5.5 gives the lower bound for the parent's exact rank-one reduction,
for every component under B.5.3, using the literal faithful chief-section image. -/
theorem component_rank_pos (h55 : SourceConstruction.ComponentsInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hL : IsComponent G L) : 0 < primeRank 3 L :=
  SourceConstruction.component_rank_pos ρ h55 hyp hL

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
