module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongIntermediateLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongEdges

/-!
# Actual terminal actions and distance-six radius in the original plane branch

Three selected edge-aligned shifts provide both same-radius actions.
At distance six, their intermediate lines are noncentral and the actual
opposite radius consequently has image order four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The original cubic plane branch supplies the actual terminal plane
and both same-radius action estimates in one coherent three-shift chain.
The strict radius bound and intermediate noncentrality remain separate
source obligations; they are not hypotheses hidden in this construction. -/
theorem plane_long_edge_paired_terminal_radius_actions
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ q : EdgePlanePairedBackwardShift (h := h) p,
      ∃ r : EdgePlanePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePlanePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z Rg r.start,Z Rg z₄⁆
          let R₆ := ⁅Z Rg t.start,Z Rg z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam Rg)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z Rg r.start ⊓
            centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) ∧
          (2 < (Q Rg q.start).relIndex (V Rg z₄) →
            R₄ ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) ∧
          (2 < (Q Rg r.start).relIndex (V Rg z₄ ⊓ Q Rg q.start) →
            R₆ ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg))) := by
  obtain ⟨q,r,t,hdis,hcard,hplane⟩ := plane_long_edge_paired_terminal_plane h e hz hk hb u hR p
  have hact := plane_long_paired_same_radius_actions h e hz hk hb u hR q.path
    r.toPlanePairedBackwardShift t.toPlanePairedBackwardShift r.first_kernel_generation t.first_kernel_generation
  exact ⟨q,r,t,hdis,hcard,hplane,hact⟩

include h e hz hk in
/-- In the literal three-shift chain at distance six, both terminal lines
are noncentral at the intervening stabilizers. The existing same-radius
action implications force the opposite radius index to equal four. -/
theorem plane_long_edge_paired_terminal_six
    (hb : sourceDistance h = 6)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ q : EdgePlanePairedBackwardShift (h := h) p,
      ∃ r : EdgePlanePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePlanePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z Rg r.start,Z Rg z₄⁆
          let R₆ := ⁅Z Rg t.start,Z Rg z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam Rg)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z Rg r.start ⊓
            centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) ∧
          (¬ R₄ ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) ∧
          (¬ R₆ ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg))) ∧
          (Q Rg r.start).relIndex (V Rg z₄) = 4 := by
  have hb4 : 4 < sourceDistance h := by omega
  obtain ⟨q,r,t,hdis,hcard,hplane,hact₄,hact₆⟩ := plane_long_edge_paired_terminal_radius_actions h e hz hk hb4 u hR p
  have hn₄ := plane_long_paired_intermediate_noncentral_six h e hz hk hb u hR p
    q.toPlanePairedBackwardShift r.toPlanePairedBackwardShift q.first_kernel_generation
  have hn₆ := plane_long_paired_intermediate_noncentral_six h e hz hk hb u hR q.path
    r.toPlanePairedBackwardShift t.toPlanePairedBackwardShift r.first_kernel_generation
  refine ⟨q,r,t,hdis,hcard,hplane,hn₄,hn₆,?_⟩
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  have hi₄ : (Q Rg q.start).relIndex (V Rg z₄) ≤ 2 := by
    by_contra! hh
    exact hn₄ (hact₄ hh)
  have hi₆ : (Q Rg r.start).relIndex (V Rg z₄ ⊓ Q Rg q.start) ≤ 2 := by
    by_contra! hh
    exact hn₆ (hact₆ hh)
  have hVQ : V Rg z₄ ≤ Q Rg z₄ :=
    V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color
      (by change 2 < sourceDistance h; omega)
  let := finite_stabilizer Rg z₄
  let : Finite (V Rg z₄) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have htower := relIndex_inf_mul_relIndex (Q Rg r.start) (Q Rg q.start) (V Rg z₄)
  rw [inf_comm (Q Rg q.start)] at htower
  have hmono : (Q Rg r.start).relIndex (V Rg z₄) ≤
      (Q Rg r.start ⊓ Q Rg q.start).relIndex (V Rg z₄) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hupper : (Q Rg r.start).relIndex (V Rg z₄) ≤ 4 := by
    rw [←htower] at hmono
    exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
  exact (small_opposite_radius_eq_four h e hz hk (by omega) r.path hupper).2.2

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
