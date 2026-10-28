module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.KernelCentrality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.QuotientIrreducible

/-!
# The irreducible moving quotient of the actual A₆ replacement

The literal pullback of the moving radius through embedM is nonabelian.
Its central quotient is the same elementary group as the graph moving
quotient. The proved chief budget forces irreducibility of the actual
conjugation action. These constructions keep the exact replacement and
quotient maps, for the remaining natural-module commutator estimate.

Source: MS93 (3.8), printed pp.878--879.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The actual moving subgroup in the original replacement. -/
abbrev movingPreimage := (Vcirc r.radical (alpha r.radical)).comap (embedM r.radical)

include h in
theorem movingPreimage_map (hb : 2 < replacementDistance h r) :
    (movingPreimage r).map (embedM r.radical) = Vcirc r.radical (alpha r.radical) := by
  apply map_comap_eq_self
  have hPV : Vcirc r.radical (alpha r.radical) ≤ V r.radical (alpha r.radical) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (V_normalized _))
  exact ((hPV.trans ((replacementGeometry h r).V_le_Q hb _ rfl)).trans
    (fun _ hx => hx.1)).trans_eq (stabilizer_m_base r.radical)

/-- The original embedding restricted to its exact moving subgroup. -/
def movingPreimageEquiv (hb : 2 < replacementDistance h r) :
    movingPreimage r ≃* Vcirc r.radical (alpha r.radical) :=
  ((movingPreimage r).equivMapOfInjective (embedM r.radical) (embedM_injective r.radical)).trans
    (MulEquiv.subgroupCongr (movingPreimage_map h r hb))

theorem movingPreimageEquiv_val (hb : 2 < replacementDistance h r) (x : movingPreimage r) :
    (movingPreimageEquiv h r hb x : FreeAmalgam r.radical) = embedM r.radical x := rfl

private theorem center_map_equiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (center P).map e.toMonoidHom = center Q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨w,rfl⟩ := e.surjective z
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e (mem_center_iff.mp hy w)
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using mem_center_iff.mp hx (e y)

/-- The literal central quotient, identified through the original embedding. -/
def movingPreimageQuotientEquiv (hb : 2 < replacementDistance h r) :
    ((movingPreimage r) ⧸ center (movingPreimage r)) ≃*
      ((Vcirc r.radical (alpha r.radical)) ⧸ center (Vcirc r.radical (alpha r.radical))) :=
  QuotientGroup.congr _ _ (movingPreimageEquiv h r hb) (center_map_equiv _)

theorem movingPreimage_quotient_elementary
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) :
    IsElementaryAbelian 2 ((movingPreimage r) ⧸ center (movingPreimage r)) := by
  let := moving_quotient_elementary h m hz hn r himage fg (alpha r.radical) rfl
  exact IsElementaryAbelian.of_injective (movingPreimageQuotientEquiv h r
    (by rw [fg.distance]; decide)).toMonoidHom (MulEquiv.injective _)

/-- Conjugation by the original overgroup on the actual moving central quotient. -/
def preimageQuotientAction : r.overgroup →* MulAut ((movingPreimage r) ⧸ center (movingPreimage r)) :=
  (quotientAut (center (movingPreimage r))).comp (MulAut.conjNormal : r.overgroup →* MulAut (movingPreimage r))

omit [Finite G] in
theorem preimageQuotientAction_mk (g : r.overgroup) (x : movingPreimage r) :
    preimageQuotientAction r g (QuotientGroup.mk' (center (movingPreimage r)) x) =
      QuotientGroup.mk' (center (movingPreimage r)) (MulAut.conjNormal g x) :=
  quotientAut_apply_mk _ _ _

/-- Every original-group moving radius is nonabelian in this critical branch. -/
theorem moving_not_commutative
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ¬ IsMulCommutative (Vcirc r.radical a) := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical (alpha r.radical)
    ((replacementGeometry h r).exists_critical (alpha r.radical) rfl)
  let p := CriticalPath.ofPair (geometry := replacementGeometry h r) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans fg.distance
  have hle : 2 ≤ p.walk.length := by omega
  have hc : color r.radical (p.walk.getVert 2) = false := (p.vertex_color hle).mpr (by decide)
  have hncomm := critical_midpoint_moving_not_commutative h m hz hn r himage fg
    (alpha r.radical) rfl b hcrit (p.walk.getVert 2) hc (p.dist_start hle)
      (by rw [p.dist_end,hl])
  obtain ⟨g,hg⟩ := exists_mVertex_of_color r.radical ha
  obtain ⟨k,hk⟩ := exists_mVertex_of_color r.radical hc
  let f := g⁻¹*k
  have hf : act r.radical f a = p.walk.getVert 2 := by
    rw [hg,hk,act_mVertex]
    simp only [f,mul_inv_cancel_left]
  intro hcomm
  let := hcomm
  apply hncomm
  rw [←hf,Vcirc_act]
  infer_instance

/-- The normal-layer dichotomy is discharged for the actual moving preimage. -/
theorem movingPreimage_normal_dichotomy
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (Y : Subgroup r.overgroup) [Y.Normal] (hYP : Y ≤ movingPreimage r) :
    Y ≤ movingPreimage r ⊓ centralizer (movingPreimage r : Set r.overgroup) ∨
      movingPreimage r ≤ Y ⊔ (movingPreimage r ⊓ centralizer (movingPreimage r : Set r.overgroup)) := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical (alpha r.radical)
    ((replacementGeometry h r).exists_critical (alpha r.radical) rfl)
  let p := CriticalPath.ofPair (geometry := replacementGeometry h r) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans fg.distance
  have hle : 2 ≤ p.walk.length := by omega
  obtain ⟨q,hq,hk,_,hPk,hfull,hfixed,A,a,ha,haA,hi⟩ :=
    moving_budget_data h m hz hn r himage fg b hcrit (p.walk.getVert 2)
      ((p.vertex_color hle).mpr (by decide)) (p.dist_start hle) (by rw [p.dist_end,hl])
  exact AlternatingBudget.normal_subgroup_central_or_cover q hq
    (by rw [hk]; exact pCore_isPGroup) (movingPreimage r) hPk A a ha haA hi hfull hfixed Y hYP

/-- The precise nonzero irreducible binary action of the original replacement
on its moving central quotient. Every chief and nonabelian premise is discharged. -/
theorem movingPreimage_quotient_irreducible
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) :
    letI := movingPreimage_quotient_elementary h m hz hn r himage fg
    Representation.IsIrreducible (Offenders.linearize (preimageQuotientAction r)) := by
  let := movingPreimage_quotient_elementary h m hz hn r himage fg
  apply AlternatingBudget.quotient_linear_irreducible (movingPreimage r)
  · intro hcomm
    let := hcomm
    apply moving_not_commutative h m hz hn r himage fg (alpha r.radical) rfl
    rw [←movingPreimage_map h r (by rw [fg.distance]; decide)]
    infer_instance
  · intro Y hY hYP
    let := hY
    exact movingPreimage_normal_dichotomy h m hz hn r himage fg Y hYP
  · exact preimageQuotientAction_mk r

/-- The same irreducibility on the original replacement, with the critical
geometry supplied by its proved producer. -/
theorem movingPreimage_quotient_irreducible_of_alternating
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h r) :
    let fg := Estimates.fourGeometry_of_alternating h m hz hn r himage hb
    letI := movingPreimage_quotient_elementary h m hz hn r himage fg
    Representation.IsIrreducible (Offenders.linearize (preimageQuotientAction r)) :=
  movingPreimage_quotient_irreducible h m hz hn r himage
    (Estimates.fourGeometry_of_alternating h m hz hn r himage hb)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
