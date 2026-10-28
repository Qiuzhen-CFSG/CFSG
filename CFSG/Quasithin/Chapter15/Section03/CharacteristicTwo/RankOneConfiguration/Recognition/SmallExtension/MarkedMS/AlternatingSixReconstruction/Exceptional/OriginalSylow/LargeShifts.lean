module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeShifts

/-!
# Large critical shifts in the original-Sylow Borel branch

The original Sylow hypothesis leaves only the Borel cubic image. For every
large critical path, the shared cubic source construction then produces a
backward critical path from any eligible strict Baumann slice, retaining the
original graph and all overlapping vertices. This closes the large-image
shift step for the exceptional source; small-image shifts and the terminal
contradictions remain necessary for whole-core exhaustion.

Source: Meierfrankenfeld--Stellmacher (1993), (5.6)--(5.8), pp.917--920;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R))
  (e : CentralMarking L) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "Rg" => edge L R

include hSyl in
/-- In the original-Sylow Borel branch, every large critical path has an
actual backward shift whenever its adjacent forward slice has index greater
than two. The same path, conjugator and overlap vertices are retained. -/
theorem coreExhaustion_or_borel_large_backward_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∧
        ∀ (a' delta : Vertex Rg)
          (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) →
          Adjacent Rg delta (p.walk.getVert 1) →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg delta) →
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
                (p.walk.getVert (p.walk.length - 2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length - 2,
                  q.walk.getVert (i + 2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g delta)) := by
  rcases coreExhaustion_or_borel_generating_edges h hSyl e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR,_⟩
  · exact Or.inl hex
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,hR,?_⟩
    intro a' delta p hlarge hdelta hslice
    exact large_remaining_backward_shift_of_two_lt_slice h e hz hk hb u
      (Or.inr hR) p hlarge hdelta hslice

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
