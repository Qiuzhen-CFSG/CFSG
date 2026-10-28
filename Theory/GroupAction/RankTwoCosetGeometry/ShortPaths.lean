module
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.GroupAction.ThreePointKernelSeparation

/-!
# Pointwise fixers of short cubic paths

For a nonbacktracking two-edge path, the pointwise fixer is the radius-one
ball kernel at its middle vertex. A three-edge path has pointwise fixer equal
to the intersection of the radius-one kernels at its two middle vertices.

The existing three-point action theorem supplies the argument: fixing the
center and two distinct neighbors fixes the whole closed star. Only the
middle vertices need degree three; no finiteness, connectedness or tree
hypothesis is needed.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the local
kernel comparison in (4.4), printed p.393.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem mem_ballKernel_one_of_two_neighbors {a b c : Vertex F}
    (hab : (graph F).Adj a b) (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph F).neighborSet b) = 3)
    (g : G) (ha : g • a = a) (hb : g • b = b) (hc : g • c = c) :
    g ∈ ballKernel F b 1 := by
  have hfix : ∀ z ∈ (graph F).neighborSet b, g • z = z :=
    MulAction.fixes_three_point_set _ hcard g (fun z => by
      change (graph F).Adj b z ↔ (graph F).Adj b (g • z)
      simpa only [translationGraphIso_apply, hb] using
        ((translationGraphIso F g).map_adj_iff (v := b) (w := z)).symm)
      hab.symm hbc hac ha hc
  intro z hz
  rcases (mem_ball_one F b z).mp hz with hz | rfl
  · exact hfix z hz
  · exact hb

theorem pathStabilizer_two_eq_ballKernel_one {a : Vertex F}
    (p : BasedWalk (graph F) 2 a) (hp : p.Nonbacktracking)
    (hcard : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3) :
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 := by
  rcases p with ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, p⟩⟩
  ext g
  change (∀ z ∈ [a, b, c], g • z = z) ↔ g ∈ ballKernel F b 1
  simp only [List.forall_mem_cons]
  constructor
  · rintro ⟨ha, hb, hc, _⟩
    exact mem_ballKernel_one_of_two_neighbors F hab hbc hp.1.symm hcard g ha hb hc
  · intro hg
    exact ⟨hg a ((mem_ball_one F b a).mpr (.inl hab.symm)),
      hg b (center_mem_ball F b 1), hg c ((mem_ball_one F b c).mpr (.inl hbc)),
      by intro z hz; cases hz⟩

theorem pathStabilizer_three_eq_ballKernel_one_inf {a : Vertex F}
    (p : BasedWalk (graph F) 3 a) (hp : p.Nonbacktracking)
    (hb : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3)
    (hc : Nat.card ((graph F).neighborSet (p.2.1 : Vertex F)) = 3) :
    pathStabilizer F p =
      ballKernel F (p.1 : Vertex F) 1 ⊓ ballKernel F (p.2.1 : Vertex F) 1 := by
  rcases p with ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, ⟨⟨d, hcd⟩, p⟩⟩⟩
  ext g
  change (∀ z ∈ [a, b, c, d], g • z = z) ↔
    g ∈ ballKernel F b 1 ∧ g ∈ ballKernel F c 1
  simp only [List.forall_mem_cons]
  constructor
  · rintro ⟨ha, hb', hc', hd, _⟩
    exact ⟨mem_ballKernel_one_of_two_neighbors F hab hbc hp.1.symm hb g ha hb' hc',
      mem_ballKernel_one_of_two_neighbors F hbc hcd hp.2.1.symm hc g hb' hc' hd⟩
  · rintro ⟨hb', hc'⟩
    exact ⟨hb' a ((mem_ball_one F b a).mpr (.inl hab.symm)),
      hb' b (center_mem_ball F b 1), hc' c (center_mem_ball F c 1),
      hc' d ((mem_ball_one F c d).mpr (.inl hcd)), by intro z hz; cases hz⟩

end Subgroup.CosetGeometry.RankTwo
