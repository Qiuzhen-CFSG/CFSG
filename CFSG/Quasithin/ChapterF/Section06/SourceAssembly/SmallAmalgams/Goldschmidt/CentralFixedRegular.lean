module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBalance
public import Theory.GroupAction.CubicTree.TrackArcs

/-!
# Regularity of a central involution's fixed interval

The involution fixes its entire track interval and moves the next vertex
at each end. The cubic local action therefore makes both ends regular.
An odd such interval lies strictly below the first singular length, by the
parity conclusion of the source arc-transitivity theorem.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5), p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.centralInterval_arc_regular (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) :
    Regular (A := G) (t.arc d.fixedLeft (d.fixedRight - d.fixedLeft).toNat) := by
  let n := (d.fixedRight - d.fixedLeft).toNat
  have hL := d.centralLeft_mem
  have hR := d.centralRight_mem
  have hlt := d.central_lt
  have hn : 0 < n := by dsimp only [n]; omega
  have hncast : d.fixedLeft + (n : ℤ) = d.fixedRight := by dsimp only [n]; omega
  have hfix : ∀ v ∈ (t.arc d.fixedLeft n).vertices, z • v = v := by
    rw [t.fixes_arc_iff, t.mem_segmentFixer]
    exact fun i hi hir => (d.fixed_iff _).2 ⟨hi, by omega⟩
  have hmR : z • t.vertex (d.fixedRight + 1) ≠ t.vertex (d.fixedRight + 1) := by
    intro hh
    have hi := (d.fixed_iff _).1 hh
    omega
  have hmL : z • t.vertex (d.fixedLeft - 1) ≠ t.vertex (d.fixedLeft - 1) := by
    intro hh
    have hi := (d.fixed_iff _).1 hh
    omega
  have hfw : Theory.GroupAction.CubicTree.Forward (t.arc d.fixedLeft n)
      (t.vertex (d.fixedRight + 1)) := by
    simpa only [hncast] using t.arc_forward d.fixedLeft n
  have hbw := t.arc_backward d.fixedLeft n
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change Regular (A := G) (t.arc d.fixedLeft n)
  rw [hm] at hfix hfw hbw ⊢
  constructor
  · by_contra hr
    exact hmL (fixes_backward_of_not_leftRegular trackGraphAction _
      (h.card_neighbor _) hr z hfix hbw)
  · by_contra hr
    exact hmR (fixes_forward_of_not_rightRegular trackGraphAction _
      (h.card_neighbor _) hr z hfix hfw)

theorem CubicTreeAction.odd_centralInterval_length_lt_singularity (h : CubicTreeAction F)
    {s : ℕ} (hs : 0 < s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z)
    (ho : Odd (d.fixedRight - d.fixedLeft)) : (d.fixedRight - d.fixedLeft).toNat < s := by
  by_contra hge
  have hr := h.regular_endpoints hs hshort p hp hn (by omega)
    (t.arc d.fixedLeft (d.fixedRight - d.fixedLeft).toNat)
    (t.arc_nonbacktracking _ _) (h.centralInterval_arc_regular t d)
  obtain ⟨k, hk⟩ := hr.2.2
  obtain ⟨j, hj⟩ := ho
  have hL := d.centralLeft_mem
  have hR := d.centralRight_mem
  have hlt := d.central_lt
  have hncast : ((d.fixedRight - d.fixedLeft).toNat : ℤ) = d.fixedRight - d.fixedLeft := by omega
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
