module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathCentralSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import Theory.GroupAction.CubicTree.CubicOrbitCorrection
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Second-ball fixation of the original six-path correction

The literal universal-to-reduced covering transports the binary local degree
and lifts fixation from the chosen reflection's opposite-core placement.
The six-path root has order two and fixes its outer path vertex. Together
with the cubic orbit identity this proves that both the adjustment x tᵢ d
and the cube (x tᵢ)³ fix the second ball, in the universal tree and in the
original reduced graph.

This is the geometric part of DGS (14.17), printed p.223. It retains the
selected reflection's core placement and the common cubic inverter as
explicit source inputs. It does not identify the second-ball kernel with
Zᵢ: that stronger local assertion is not justified by cubic geometry.
Central placement and the replacement-root argument remain separate.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (c : CompatibleCartans L (reducedSylow L S))
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) j =
  base (Universal.cosetFamily (reducedAmalgam L S)) j)
variable (htmove : ∀ j, t j • base (Universal.cosetFamily (reducedAmalgam L S)) (!j) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!j))
variable (htsq : ∀ j, t j*t j=1)
variable (htnorm : ∀ j, t j∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include htfix htmove htsq htnorm in
private theorem six_cubic_second_ball
    (i : Bool)
    (hdegree : ∀ j, Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet
      (base (Universal.cosetFamily (reducedAmalgam L S)) j))=3)
    (hcard : Nat.card (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)=2)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)
    (d : (reducedAmalgam L S).Universal) (hd : d^3=1)
    (hxd : x*d*x⁻¹=d⁻¹) (htd : t i*d*(t i)⁻¹=d⁻¹)
    (hdm : d • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (hdv : d • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htouter : t i • (d⁻¹ •
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2) =
      d⁻¹ • (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.reverse.getVert 2) :
    Commute (x*t i*d) d ∧
      x*t i*d∈graphBallFixer (sourceGraph (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 2 ∧
      (x*t i)^3∈graphBallFixer (sourceGraph (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 2 := by
  let A := reducedAmalgam L S
  let F := Universal.cosetFamily A
  let p := reflectionPath c t htfix htmove htnorm 6 (by decide) i
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hdeg : ∀ v : SourceVertex A, Nat.card ((sourceGraph A).neighborSet v)=3 :=
    RankTwo.card_neighbors_of_indices F (fun _ => 3) (fun j =>
      (RankTwo.card_neighbor_base F j).symm.trans (hdegree j))
  have hfirst : p.walk.reverse.getVert 1=base F (!i) := by
    rw [SimpleGraph.Walk.getVert_reverse]
    exact p.previous
  have hmv : (sourceGraph A).Adj (base F i) (base F (!i)) := by
    simpa only [SimpleGraph.Walk.getVert_zero,hfirst] using
      p.walk.reverse.adj_getVert_succ (i := 0) (by rw [SimpleGraph.Walk.length_reverse,p.length_eq]; decide)
  have hva : (sourceGraph A).Adj (base F (!i)) (p.walk.reverse.getVert 2) := by
    simpa only [hfirst] using
      p.walk.reverse.adj_getVert_succ (i := 1) (by rw [SimpleGraph.Walk.length_reverse,p.length_eq]; decide)
  have hma : base F i≠p.walk.reverse.getVert 2 := by
    intro he
    have hh := p.isPath.reverse.getVert_injOn
      (by simp only [SimpleGraph.Walk.length_reverse,p.length_eq]; omega : 0≤p.walk.reverse.length)
      (by simp only [SimpleGraph.Walk.length_reverse,p.length_eq]; omega : 2≤p.walk.reverse.length)
      (by simpa only [SimpleGraph.Walk.getVert_zero] using he)
    omega
  let P := pathRoot (X := A.Universal) p.walk
  have hc : Nat.card P=2 := hcard
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  have hx2 : x*x=1 := by
    have hh := congrArg (fun y : P => (y : A.Universal))
      (pow_card_eq_one' (x := (⟨x,hx⟩ : P)))
    change x^Nat.card P=1 at hh
    simpa only [hc,pow_two] using hh
  have hxa : x • p.walk.reverse.getVert 2=p.walk.reverse.getVert 2 := by
    rw [SimpleGraph.Walk.getVert_reverse]
    exact pCoreIn_le 2 (pathFixer (X := A.Universal) p.walk) hx _ (Nat.sub_le _ _)
  exact Theory.GroupAction.CubicTree.inverted_cubic_product_mem_second_ball
    htree (source_action A) hmv hva hma (hdeg _) (fun v _ => hdeg v)
    x (t i) d hd hx2 (htsq i) hxd htd hdm hdv (pathRoot_fixes p.walk hx).1
    (htfix i) hxa htouter

include htfix htmove htsq htnorm in
/-- The original core placement of the chosen reflection supplies the outer
fixation in the cubic-orbit argument. Both words fix the actual second ball,
and their images fix the corresponding reduced ball under the literal map. -/
theorem source_six_cubic_second_ball_of_core
    (h : HypothesisF11 L S) (i : Bool)
    (hdegree : ∀ j, Nat.card ((RankTwo.graph (reducedFamily L S)).neighborSet
      (RankTwo.base (reducedFamily L S) j))=3)
    (hcard : Nat.card (pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)=2)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk)
    (d : (reducedAmalgam L S).Universal) (hd : d^3=1)
    (hxd : x*d*x⁻¹=d⁻¹) (htd : t i*d*(t i)⁻¹=d⁻¹)
    (hdm : d • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (hdv : d • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hcore : bOne_tree_map h (d*t i*d⁻¹) ∈
      Q (reducedFamily L S) (RankTwo.base (reducedFamily L S) (!i))) :
    Commute (x*t i*d) d ∧
      x*t i*d∈graphBallFixer (sourceGraph (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 2 ∧
      (x*t i)^3∈graphBallFixer (sourceGraph (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 2 ∧
      bOne_tree_map h (x*t i*d)∈RankTwo.ballKernel (reducedFamily L S)
        (RankTwo.base (reducedFamily L S) i) 2 ∧
      bOne_tree_map h ((x*t i)^3)∈RankTwo.ballKernel (reducedFamily L S)
        (RankTwo.base (reducedFamily L S) i) 2 := by
  let A := reducedAmalgam L S
  let F := Universal.cosetFamily A
  let π := bOne_tree_cover h
  let p := reflectionPath c t htfix htmove htnorm 6 (by decide) i
  have hdeg (j : Bool) : Nat.card ((sourceGraph A).neighborSet (base F j))=3 := by
    have he := Nat.card_congr (Equiv.ofBijective _ (π.neighbor_bijective (base F j)))
    change Nat.card ((sourceGraph A).neighborSet (base F j)) =
      Nat.card ((RankTwo.graph (reducedFamily L S)).neighborSet (π.vertex (base F j))) at he
    rw [π.vertex_base] at he
    exact he.trans (hdegree j)
  let y := d*t i*d⁻¹
  have hym : y • base F i=base F i := by
    have hdim : d⁻¹ • base F i=base F i := inv_smul_eq_iff.mpr hdm.symm
    have htm : t i • base F i = base F i := htfix i
    have hdm' : d • base F i = base F i := hdm
    simp only [y,mul_smul,hdim,htm,hdm']
  have hU : bOne_tree_map h y ∈ U (reducedFamily L S)
      (RankTwo.base (reducedFamily L S) (!i)) :=
    (source_Z_Q_U (reduced_triple h) _).2 hcore
  have hmv : (sourceGraph A).Adj (base F i) (base F (!i)) :=
    ⟨by change i≠(!i); cases i <;> decide,incident_base _ _ _⟩
  have hyv : y • base F (!i)=base F (!i) :=
    π.fixes_neighbor_of_image hmv y hym (by
      rw [π.vertex_base]
      exact U_le_stabilizer _ _ hU)
  have hball := π.ballKernel_lift (base F (!i)) 1 y hyv (by
    rw [π.vertex_base]
    exact hU)
  have hfirst : p.walk.reverse.getVert 1=base F (!i) := by
    rw [SimpleGraph.Walk.getVert_reverse]
    exact p.previous
  have hva : (sourceGraph A).Adj (base F (!i)) (p.walk.reverse.getVert 2) := by
    simpa only [hfirst] using
      p.walk.reverse.adj_getVert_succ (i := 1)
        (by rw [SimpleGraph.Walk.length_reverse,p.length_eq]; decide)
  have hya := hball (p.walk.reverse.getVert 2) ((RankTwo.mem_ball_one _ _ _).mpr (Or.inl hva))
  have htouter : t i • (d⁻¹ • p.walk.reverse.getVert 2)=d⁻¹ • p.walk.reverse.getVert 2 := by
    have hh := congrArg (d⁻¹ • ·) hya
    simpa only [y,mul_smul,inv_smul_smul] using hh
  obtain ⟨hcomm,hadj,hcube⟩ := six_cubic_second_ball c t htfix htmove htsq htnorm
    i hdeg hcard x hx d hd hxd htd hdm hdv htouter
  have hmap (z : A.Universal) (hz : z∈graphBallFixer (sourceGraph A) (base F i) 2) :
      bOne_tree_map h z∈RankTwo.ballKernel (reducedFamily L S)
        (RankTwo.base (reducedFamily L S) i) 2 := by
    have hz' : z∈RankTwo.ballKernel F (base F i) 2 :=
      fun v hv => (mem_graphBallFixer _ _ 2 z).mp hz v hv
    have hh := π.ballKernel_map_le (base F i) 2 (mem_map_of_mem (bOne_tree_map h) hz')
    rwa [π.vertex_base] at hh
  exact ⟨hcomm,hadj,hcube,hmap _ hadj,hmap _ hcube⟩

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
