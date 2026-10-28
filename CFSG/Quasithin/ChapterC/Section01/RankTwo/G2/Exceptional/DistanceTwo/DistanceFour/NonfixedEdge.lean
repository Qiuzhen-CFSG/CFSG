module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.CriticalEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.Source
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Completing distance-four exclusion from the nonfixed triple calculation

Critical seed pairs generate the derived radius; noncritical pairs commute.
If their commutators centralize the first edge kernel, the whole critical
commutator is the source auxiliary and is fixed at the midpoint. Thus the
entire derived radius is fixed. The already proved natural-module argument
then contradicts the critical commutator's order-eight lower bound.

Only the nonfixed branch needs the triple-commutator calculation recorded
as NonfixedCriticalEdgeInput. This is still an obligation of
qt-e-ms-small-g2-reconstruction, which retains final source assembly.
The present reduction does not prove that input or unconditional reconstruction.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.8), printed p.879. The private import reuses the earlier binary proof's
normalizer and generated-commutator lemmas; its module classification is unused.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)

/-- Critical seed pairs generate the derived radius. Their edge centralization
therefore makes the whole derived radius fixed by its actual midpoint residual. -/
theorem radius_derived_le_fixed_of_critical_edges
    (h : Pair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hb : (geometry h).b T = 4)
    (c : Vertex T) (hcColor : color T c = false)
    (htrip : ∀ (a : Vertex T) (ha : color T a = false) (z : Vertex T),
      CriticalPair T a z ((geometry h).exists_critical a ha) →
      ∀ t, Adjacent T a t → Adjacent T c t →
      (cosetGraph T).dist a c = 2 → (cosetGraph T).dist c z = 2 →
      ⁅⁅Z T a,Z T z⁆,Q T t⁆ = ⊥) :
    ⁅V T c,V T c⁆ ≤ fixedCore T c := by
  let I := {d : Vertex T // color T d = false ∧ (cosetGraph T).dist d c ≤ 2}
  have heq : V T c = ⨆ d : I, Z T d.val := by
    apply le_antisymm
    · apply radius_le_of_m_ball hcColor
      intro d hd hdist
      exact le_iSup_of_le (⟨d,hd,hdist⟩ : I) le_rfl
    · apply iSup_le
      intro d
      exact le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  have hn : V T c ≤ normalizer (fixedCore T c : Set (FreeAmalgam T)) :=
    (((geometry h).V_le_Q (by omega) c hcColor).trans (fun _ hx => hx.1)).trans
      (fixedCore_normalized c)
  rw [heq] at hn ⊢
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro d
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro f
  by_cases hZQ : Z T f.val ≤ Q T d.val
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hZQ.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp
          ((geometry h).centralizes d.val d.property.1))))).le.trans bot_le
  have hmin := criticalDistance_le T f.val
    ((geometry h).exists_critical f.val f.property.1) hZQ
  have hfcrit : criticalDistance T f.val
      ((geometry h).exists_critical f.val f.property.1) = 4 :=
    ((geometry h).distance_constant f.val f.property.1).trans hb
  rw [hfcrit] at hmin
  have hcd : (cosetGraph T).dist c d.val ≤ 2 := by
    simpa only [SimpleGraph.dist_comm] using d.property.2
  have hfc := f.property.2
  have htri := (cosetGraph_connected T).dist_triangle (u := f.val) (v := c) (w := d.val)
  have hfd : (cosetGraph T).dist f.val d.val = 4 := by omega
  have hfc2 : (cosetGraph T).dist f.val c = 2 := by omega
  have hcd2 : (cosetGraph T).dist c d.val = 2 := by omega
  have hcrit : CriticalPair T f.val d.val
      ((geometry h).exists_critical f.val f.property.1) :=
    ⟨hfd.trans hfcrit.symm,hZQ⟩
  obtain ⟨t,hft,hct⟩ := exists_common_neighbor_of_dist_two T f.val c hfc2
  exact critical_commutator_le_fixed_of_centralizes h e hb f.val d.val f.property.1
    hcrit t c hcColor hft hct hfc2 hcd2
    (commutator_eq_bot_iff_le_centralizer.mp
      (htrip f.val f.property.1 d.val hcrit t hft hct hfc2 hcd2))

/-- The final nonfixed-derived calculation of MS93 (3.8), p.879. The exact
triple commutator vanishes only in the branch where the midpoint derived
radius is not fixed. The reconstruction owner must still establish this input. -/
def NonfixedCriticalEdgeInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 4 →
    ∀ c : Vertex (R.subgroupOf (L ⊔ R)), color (R.subgroupOf (L ⊔ R)) c = false →
      ¬ ⁅V (R.subgroupOf (L ⊔ R)) c,V (R.subgroupOf (L ⊔ R)) c⁆ ≤
        fixedCore (R.subgroupOf (L ⊔ R)) c →
      ∀ (a : Vertex (R.subgroupOf (L ⊔ R))) (ha : color (R.subgroupOf (L ⊔ R)) a = false)
        (z : Vertex (R.subgroupOf (L ⊔ R))),
        CriticalPair (R.subgroupOf (L ⊔ R)) a z ((geometry h).exists_critical a ha) →
        ∀ t, Adjacent (R.subgroupOf (L ⊔ R)) a t → Adjacent (R.subgroupOf (L ⊔ R)) c t →
          (cosetGraph (R.subgroupOf (L ⊔ R))).dist a c = 2 →
          (cosetGraph (R.subgroupOf (L ⊔ R))).dist c z = 2 →
          ⁅⁅Z (R.subgroupOf (L ⊔ R)) a,Z (R.subgroupOf (L ⊔ R)) z⁆,
            Q (R.subgroupOf (L ⊔ R)) t⁆ = ⊥

/-- The common auxiliary argument discharges derived fixation from the
nonfixed-branch triple calculation, keeping both branches separate. -/
theorem fixedRadius_of_nonfixedCriticalEdge
    (htrip : NonfixedCriticalEdgeInput.{u}) : FixedRadiusInput.{u} := by
  intro J _ _ L R h e hb _ c hc
  by_contra hn
  exact hn (radius_derived_le_fixed_of_critical_edges h e hb c hc
    (htrip J L R h e hb c hc hn))

/-- The nonfixed branch supplies fixation; the already proved fixed branch
then contradicts the actual critical commutator lower bound. -/
theorem distanceFourExclusion_of_nonfixedCriticalEdge
    (htrip : NonfixedCriticalEdgeInput.{u}) : DistanceFourExclusionInput.{u} :=
  distanceFourExclusion_of_fixedRadius (fixedRadius_of_nonfixedCriticalEdge htrip)

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour

