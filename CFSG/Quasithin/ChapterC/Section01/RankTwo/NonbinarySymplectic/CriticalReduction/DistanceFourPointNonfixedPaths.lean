module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNonfixedNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointLargePaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNeighbor

/-!
# The actual point selector has a root backward image in the nonfixed branch

The original point selector at the literal path[2] supplies one residual
conjugator, actual generation by its selected mover and the original endpoint,
and the overlapping backward path. Its selected mover lies in that literal
edge kernel. The nonfixed normalizer obstruction therefore excludes a large
backward image on these same witnesses. Critical image recognition makes
both reciprocal backward images exactly q.

The complete original selection clauses are retained, and no independent
generation or normality assumption is added. This removes the nonfixed
large-back alternative in the point branch of MS93 (5.12)(2), p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same actual point selector retains every generation and path clause;
unless the full radius is fixed, both backward critical images have order q. -/
theorem Input.replacement_distance_four_point_backward_fixed_or_root
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hlarge : Nat.card F < (Q d.radical a).relIndex (Z d.radical z))
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ c, c=path.walk.getVert 2 ∧ Adjacent d.radical c t ∧ ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom = Subgroup.SmallMover.join
        (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a ∨
          ((Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical v)=Nat.card F ∧
            (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F)) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hlen : path.walk.length-2=2 := by have hh := path.length_eq_b; omega
  have hct : Adjacent d.radical (path.walk.getVert 2) t := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnoriginal := h.replacement_path_neighbor_join_not_normal_of_four_le d path hb4
  have hselected := h.replacement_large_movement_selected_large_at_neighbor
    d path hb4 hat hfirst hct hnoriginal hlarge hJm
  obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hbackexists⟩ := hselected
  rw [hlen] at hbackexists
  obtain ⟨back,hback,hover⟩ := hbackexists
  let c := path.walk.getVert 2
  refine ⟨c,rfl,hct,g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,back,hback,hover,?_⟩
  by_cases hfix : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a
  · exact Or.inl hfix
  right
  have hmid : back.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hbound : (Q d.radical (path.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g⁻¹ c)) ≤ Nat.card F := by
    by_contra! hbad
    apply h.replacement_distance_four_nonfixed_edge_generation_obstruction
      d path hb back hmid hbad hfix
    have hres : Ltilde d.radical a ≤
        Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
          (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
            (Nat.card F^2) ⊔ Z d.radical z := by
      rw [←htransport,hgen]
      exact Ltilde_le_stabilizer a
    rw [hback]
    exact hres.trans (sup_le_sup_right (Subgroup.SmallMover.join_le _ _ _ _) _)
  have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g⁻¹ c)) < Nat.card F^2 := by
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  exact h.replacement_small_critical_indices_eq_field d back (by omega) hsmall

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
