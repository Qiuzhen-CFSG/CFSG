module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift

/-!
# The small-slice source choice in the original cubic plane branch

Original plane radius escape supplies an actual forward critical path with
all of the old walk's retained vertices. The plane also supplies forward
eligibility, so the small-slice commutator is an order-two line that is
noncentral at the midpoint. The full-cover generator theorem chooses one
residual conjugator whose line centralizer generates the midpoint stabilizer
with that same new endpoint, and that endpoint moves the line.

This constructs the existing SmallSliceShift witness from the actual plane
hypotheses. It does not require the point-core image used by the earlier
constructor, does not assume forward eligibility separately, and retains
both moving covers and the full original cubic projection kernel. Subsequent
orbit comparison, strict-slice exclusion and terminal reconstruction remain
separate source obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8)--(5.9), printed
pp.919--922, particularly equation (**) on p.920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- Forward radius escape supplies a critical path with the literal initial overlap. -/
theorem plane_forward_critical_path
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ z, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) z,
      ∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2) := by
  have hl : 2 ≤ p.walk.length := by have he := p.length_eq_b; change p.walk.length = sourceDistance h at he; omega
  let rev : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hend : rev.walk.getVert (rev.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,Nat.sub_sub_self hl]
  have hs : ∃ z, ∃ q : CriticalPath Rg (sourceGeometry h) z
      (rev.walk.getVert (rev.walk.length-2)),
      ∀ i ≤ rev.walk.length-2, q.walk.getVert (i+2) = rev.walk.getVert i := by
    obtain ⟨z,w,q,hw,hq,hover⟩ := (plane_critical_paths h e hz hk u hfull rev).2.1
    exact ⟨z,q,hover⟩
  rw [hend] at hs
  obtain ⟨z,q,hover⟩ := hs
  let fwd : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) z :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  refine ⟨z,fwd,?_⟩
  intro i hi
  change q.walk.reverse.getVert i = _
  rw [SimpleGraph.Walk.getVert_reverse,hlen]
  have hi' : p.walk.length-i = (p.walk.length-i-2)+2 := by omega
  rw [hi',hover (p.walk.length-i-2) (by
    change p.walk.length-i-2 ≤ p.walk.reverse.length-2
    rw [SimpleGraph.Walk.length_reverse]
    omega)]
  change p.walk.reverse.getVert (p.walk.length-i-2) = _
  rw [SimpleGraph.Walk.getVert_reverse]
  congr 1
  omega

include h e hz hk in
/-- Radius escape and the marked cover construct equation (**) of (5.9).
No independent displacement or generating-centralizer premise is assumed. -/
theorem plane_exists_small_slice_shift
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    Nonempty (SmallSliceShift h p) := by
  have heligible := (plane_critical_paths h e hz hk u hfull p).2.2.2
  obtain ⟨z,q,hover⟩ := plane_forward_critical_path h e hz hk hb u hfull p
  have hline := small_forward_slice_central_line h e hz hk hb p hsmall hslice heligible
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator h e hz hk q
    (forwardSliceLine h (alpha Rg) c) hHU hline.1 hline.2.2.2
  exact ⟨⟨z,q,hover,g,hg,hgen,hmove⟩⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
