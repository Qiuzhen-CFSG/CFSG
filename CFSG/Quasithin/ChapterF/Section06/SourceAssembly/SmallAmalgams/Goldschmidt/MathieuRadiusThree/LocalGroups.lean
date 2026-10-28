module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsFirstRecognition
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOpposite
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeRecognition

/-!
# The original Mathieu endpoint groups

The two generated source groups are the original vertex stabilizers. Their
literal label and local-action calculations identify the first group with
the concrete involution centralizer and the second with the concrete
normalizer of the natural four-group. This discharges the endpoint input of
the compatible radius-three marking theorem.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.6) and its conclusion, printed pp.405--406.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open Sporadic.Mathieu.M12SmallPair
universe u
variable {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem LocalRelations.endpointTypes
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3) : EndpointTypes d := by
  let a := RankTwo.base F d.side
  let v := RankTwo.base F (!d.side)
  have ha : a.type=d.side := rfl
  have hv : v.type ≠ d.side := by simp [v,base]
  have hva : (RankTwo.graph F).Adj v a := ⟨hv, incident_base F _ _⟩
  have hcards : ∀ w : RankTwo.Vertex F, w.type=d.side → Nat.card (d.labelBall w 4)=192 :=
    fun w hw => r.radiusFour_card hr w hw
  obtain ⟨ep⟩ := r.radiusFour_equiv_firstParabolic hr a ha
  obtain ⟨eq⟩ := r.oppositeGroup_equiv_secondParabolic hr v hv (fun w hw => hcards w (by
    have hn := hw.1
    cases h0 : v.type <;> cases h1 : w.type <;> cases h2 : d.side <;> simp_all))
  have hHcard : Nat.card (oppositeGroup d v)=192 :=
    (Nat.card_congr eq.toEquiv).trans card_secondParabolic
  obtain ⟨hP,hQ⟩ := r.generated_locals_eq_stabilizers_of_card hr ha hva (hcards a ha) hHcard
  have hGa : RankTwo.stabilizer F a=F d.side := stabilizer_base F d.side
  have hGv : RankTwo.stabilizer F v=F (!d.side) := stabilizer_base F (!d.side)
  have hpModel : firstParabolic=GreenBook.MathieuTwelve.P 0 :=
    (GreenBook.MathieuTwelve.P_eq_L 0).symm
  have hqModel : secondParabolic=GreenBook.MathieuTwelve.P 1 :=
    (GreenBook.MathieuTwelve.P_eq_L 1).symm
  exact ⟨⟨(MulEquiv.subgroupCongr (hP.trans hGa).symm).trans
      (ep.trans (MulEquiv.subgroupCongr hpModel))⟩,
    ⟨(MulEquiv.subgroupCongr (hQ.trans hGv).symm).trans
      (eq.trans (MulEquiv.subgroupCongr hqModel))⟩⟩

/-- The generated local groups identify both original endpoint carriers.
The marked overlap is supplied separately by the established compatibility theorem. -/
theorem localGroupsInput : LocalGroupsInput.{u} := by
  intro G _ F s h d hr r
  exact r.endpointTypes hr

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
