module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Core
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The whole moved cover and the edge seed

On every original replacement, the omega orbit is the product of the entire
moved cover and the edge seed. This is a subgroup join, with the central
attachment retained. Conjugation gives the same identity at every incident
vertex and edge. Consequently the displacement of the full vertex layer
under the edge kernel equals the displacement of its whole moving layer.

These are the literal layers used in the plane calculation in MS93 (3.6),
printed p.871. The normal-closure argument is adapted from
SymplecticSetup/EdgeLayer; no natural subgroup or point-core marking is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)

include h e hz

/-- The original whole cover, rather than a complement, generates the
replacement omega orbit together with its actual edge seed. -/
theorem seedHull_eq_moved_sup_seed :
    normalClosure (omegaCenter d.radical : Set d.overgroup) =
      replacementMoved d ⊔ omegaCenter d.radical := by
  let H := normalClosure (omegaCenter d.radical : Set d.overgroup)
  have hHK : ⁅H,pResidual 2 d.overgroup⁆ = replacementMoved d := by
    apply map_injective (embedM_injective d.radical)
    have he := (replacement_centralLayer d e hz h).U_eq_moved
    rw [U,ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull,
      Ltilde_alpha,←map_commutator] at he
    exact he
  have hHM : ⁅H,(⊤ : Subgroup d.overgroup)⁆ ≤ replacementMoved d := by
    rw [normalClosure_commutator_eq_of_centralizing_supplement
      (omegaCenter d.radical) (pResidual 2 d.overgroup) d.radical
      (Geometry.replacement_residual_sup_radical h d)
      (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)]
    rw [←hHK]
    exact commutator_mono le_normalClosure le_rfl
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    have hc : ⁅g,a⁆ ∈ replacementMoved d := by
      apply hHM
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top g) (subset_normalClosure ha)
    have he : g*a*g⁻¹ = ⁅g,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    rw [he]
    exact mul_mem (mem_sup_left hc) (mem_sup_right ha)
  · apply sup_le _ le_normalClosure
    rw [←hHK]
    exact commutator_le_left H _

/-- The base vertex layer is the join of its whole moving layer and edge seed. -/
theorem Z_eq_moving_sup_edge :
    Z d.radical (alpha d.radical) =
      U d.radical (alpha d.radical) ⊔ Z d.radical (beta d.radical) := by
  rw [ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull,
    seedHull_eq_moved_sup_seed h e hz d,Subgroup.map_sup,
    (replacement_centralLayer d e hz h).U_eq_moved]
  congr 1
  rw [Z,if_neg (by exact Bool.noConfusion : color d.radical (beta d.radical) ≠ false),
    edgeOmega,Q_beta,omegaCenter_map _ _ (embedM_injective d.radical)]

/-- The same whole-layer identity holds on every literal incident pair. -/
theorem Z_eq_moving_sup_edge_at {a b : Vertex d.radical}
    (ha : color d.radical a = false) (hab : Adjacent d.radical a b) :
    Z d.radical a = U d.radical a ⊔ Z d.radical b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical a b).mp hab
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (fun A : Subgroup (FreeAmalgam d.radical) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) (Z_eq_moving_sup_edge h e hz d)
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

/-- In the actual plane calculation, all edge displacement comes from the
whole moved cover, including any central fixed line. -/
theorem edge_displacement_eq_moving {a b : Vertex d.radical}
    (ha : color d.radical a = false) (hab : Adjacent d.radical a b) :
    ⁅Q d.radical b,Z d.radical a⁆ = ⁅Q d.radical b,U d.radical a⁆ := by
  have hb : color d.radical b = true := by
    have hc := adjacent_color_ne d.radical hab
    cases he : color d.radical b <;> simp_all
  have hZC : Z d.radical b ≤ centralizer (Q d.radical b : Set (FreeAmalgam d.radical)) := by
    simp only [Z,hb,Bool.true_eq_false,if_false,edgeOmega]
    exact fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have hpos : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  have hUQ : U d.radical a ≤ Q d.radical b :=
    ((U_le_Z a).trans ((replacementGeometry h d).omega_bound a ha hpos)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h d.radical hb hab))
  exact (commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (Z_eq_moving_sup_edge_at h e hz d ha hab).symm)
    hZC (hUQ.trans (Q d.radical b).le_normalizer)).symm

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

