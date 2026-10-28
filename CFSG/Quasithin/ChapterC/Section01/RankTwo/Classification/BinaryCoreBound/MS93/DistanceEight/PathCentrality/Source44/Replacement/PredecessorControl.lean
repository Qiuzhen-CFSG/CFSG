module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorKernel

/-!
# Predecessor control at the last backward switching position

Equal images of the predecessor kernel and the odd edge kernel modulo Q_c
make their join with Q_c the whole edge kernel. At j=4 the predecessor is
p[2]; its kernel fixes the original center a and hence normalizes every
VBall at a. It also normalizes Q_(p[4]). Thus it normalizes the required
radius join, as does Q_(p[4]), proving the original normalization at this
position whenever the predecessor image fills the edge image.

In particular the order-eight predecessor obstruction cannot occur at j=4.
The large-image extension applies this fact to the actual failed-span
switching and replacement consumers. No normalization at earlier switching
positions or general normality of involution images is asserted.

Source: Meierfrankenfeld--Stellmacher (1993), the backward induction in
(4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorControl
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem sup_eq_of_index_eq {G : Type*} [Group G]
    {A B S : Subgroup G} [Finite S] (hAS : A ≤ S) (hBS : B ≤ S)
    (hi : B.relIndex A = B.relIndex S) : A ⊔ B = S := by
  have hs := sup_le hAS hBS
  let : Finite (A ⊔ B : Subgroup G) :=
    Finite.of_injective (inclusion hs) (inclusion_injective _)
  have he : B.relIndex (A ⊔ B) = B.relIndex S := le_antisymm
    (relIndex_le_of_le_right hs index_ne_zero_of_finite)
    (hi ▸ relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite)
  have hm := relIndex_mul_relIndex B (A ⊔ B) S le_sup_right hs
  rw [he] at hm
  have hp : 0 < B.relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu : (A ⊔ B).relIndex S = 1 := by nlinarith
  exact le_antisymm hs (relIndex_eq_one.mp hu)

/-- Equal predecessor and edge images generate the literal edge kernel. -/
theorem predecessor_sup_kernel_eq_edge
    {c s d : Vertex R} (hc : color R c = false)
    (hcs : Adjacent R c s) (hds : Adjacent R d s)
    (hi : (Q R c).relIndex (Q R d) = (Q R c).relIndex (Q R s)) :
    Q R d ⊔ Q R c = Q R s := by
  have hs : color R s = true := by
    have hn := adjacent_color_ne R hcs
    cases hs : color R s <;> simp_all
  let := finite_stabilizer R s
  let : Finite (Q R s) := Finite.of_injective
    (inclusion (show Q R s ≤ stabilizer R s from fun _ hx => hx.1))
    (inclusion_injective _)
  exact sup_eq_of_index_eq (Q_le_adjacent_h R hs hds) (Q_le_adjacent_h R hs hcs) hi

/-- At stage j=4 the predecessor kernel fixes the original radius center.
If its image fills the edge image, this proves the required normalization. -/
theorem radius_normalized_at_four_of_full_predecessor
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (hj : p.walk.length - 4 * n = 4)
    (hi : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) =
      (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 1)))) :
    Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R)) := by
  have h4 : 4 ≤ p.walk.length := by omega
  have hc := (p.vertex_color h4).mpr (by decide : Even 4)
  have hd := (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide : Even 2)
  have hcs : Adjacent R (p.walk.getVert 4) (p.walk.getVert 3) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 3) (by omega)))
  have hds : Adjacent R (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  simp only [hj, Nat.reduceSub] at hi ⊢
  rw [← predecessor_sup_kernel_eq_edge hc hcs hds hi]
  apply sup_le
  · have hda : Q R (p.walk.getVert 2) ≤ stabilizer R a :=
      Q_le_stabilizer_of_dist_two R _ _ hd (by
        rw [SimpleGraph.dist_comm, p.dist_start (by omega)])
    have hdc : Q R (p.walk.getVert 2) ≤ stabilizer R (p.walk.getVert 4) :=
      Q_le_stabilizer_of_dist_two R _ _ hd (by
        rw [Iteration.path_distance p (by decide) h4])
    exact (le_inf (hda.trans (Escape.Propagation.RadiusFour.VBall_normalized a (4 * n)))
      (hdc.trans (Q_normalized R _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact le_sup_right.trans (VBall R a (4 * n) ⊔ Q R (p.walk.getVert 4)).le_normalizer

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorControl
