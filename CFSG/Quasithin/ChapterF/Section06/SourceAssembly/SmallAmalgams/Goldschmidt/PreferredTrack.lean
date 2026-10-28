module
public import Theory.GroupAction.CubicTree.Reflections
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSetup

/-!
# Tracks selected compatibly with endpoint reflections

A preferred track runs through the literal base edge. If adjacent vertices
admit involutions fixing one endpoint and moving the other, conjugate and
orient that edge onto the base edge and use the two involutions to construct
the track. They then reflect its integer coordinates about zero and one.
This retains the implication when no such adjacent involutions exist.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the choice
of track at the start of Section 6, printed p.395; used in (6.5).
-/

@[expose] public section
open Subgroup Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem mem_local_iff_fixed (x : G) (i : Bool) :
    x ∈ F i ↔ x • RankTwo.base F i = RankTwo.base F i := by
  change x ∈ F i ↔ x ∈ RankTwo.stabilizer F (RankTwo.base F i)
  rw [RankTwo.stabilizer, RankTwo.base, stabilizer_base]

private theorem base_involution_movers
    (hm : AdjacentInvolutionMovers (RankTwo.graph F) G) :
    ∃ x y : G, x ∈ F false ∧ y ∈ F true ∧ x ∉ F true ∧ y ∉ F false ∧
      x ^ 2 = 1 ∧ y ^ 2 = 1 := by
  obtain ⟨a,b,x,y,hab,hx,hy,hxb,hya,hx2,hy2⟩ := hm
  obtain ⟨g,hg⟩ := RankTwo.edge_transitive F hab
  have ha : a = g • RankTwo.base F false ∨ a = g • RankTwo.base F true := by
    have hh := (Set.ext_iff.mp hg a).mp (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have hb : b = g • RankTwo.base F false ∨ b = g • RankTwo.base F true := by
    have hh := (Set.ext_iff.mp hg b).mp (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have build (x y : G)
      (hx : x • (g • RankTwo.base F false) = g • RankTwo.base F false)
      (hy : y • (g • RankTwo.base F true) = g • RankTwo.base F true)
      (hxb : x • (g • RankTwo.base F true) ≠ g • RankTwo.base F true)
      (hya : y • (g • RankTwo.base F false) ≠ g • RankTwo.base F false)
      (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) :
      ∃ x y : G, x ∈ F false ∧ y ∈ F true ∧ x ∉ F true ∧ y ∉ F false ∧
        x ^ 2 = 1 ∧ y ^ 2 = 1 := by
    let c : MulAut G := MulAut.conj g⁻¹
    refine ⟨c x,c y,?_,?_,?_,?_,?_,?_⟩
    · apply (mem_local_iff_fixed _ false).mpr
      simpa [c, mul_smul] using congrArg (g⁻¹ • ·) hx
    · apply (mem_local_iff_fixed _ true).mpr
      simpa [c, mul_smul] using congrArg (g⁻¹ • ·) hy
    · intro hh
      apply hxb
      have hh := congrArg (g • ·) ((mem_local_iff_fixed _ true).mp hh)
      simpa [c, mul_smul] using hh
    · intro hh
      apply hya
      have hh := congrArg (g • ·) ((mem_local_iff_fixed _ false).mp hh)
      simpa [c, mul_smul] using hh
    · rw [← map_pow, hx2, map_one]
    · rw [← map_pow, hy2, map_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab.1 (congrArg (fun v : RankTwo.Vertex F => v.type)
      (ha.trans hb.symm))).elim
  · exact build x y (by simpa [ha] using hx) (by simpa [hb] using hy)
      (by simpa [hb] using hxb) (by simpa [ha] using hya) hx2 hy2
  · exact build y x (by simpa [hb] using hy) (by simpa [ha] using hx)
      (by simpa [ha] using hya) (by simpa [hb] using hxb) hy2 hx2
  · exact (hab.1 (congrArg (fun v : RankTwo.Vertex F => v.type)
      (ha.trans hb.symm))).elim

theorem CubicTreeAction.exists_preferred_track (h : CubicTreeAction F) :
    ∃ t : Track (RankTwo.graph F) G,
      t.vertex 0 = RankTwo.base F false ∧ t.vertex 1 = RankTwo.base F true ∧
      (AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections) := by
  classical
  by_cases hm : AdjacentInvolutionMovers (RankTwo.graph F) G
  · obtain ⟨x,y,hx,hy,hxb,hya,hx2,hy2⟩ := base_involution_movers hm
    refine ⟨h.selectedTrack x y hx hy hxb hya,
      h.selectedTrack_zero x y hx hy hxb hya,
      h.selectedTrack_one x y hx hy hxb hya, ?_⟩
    intro _
    obtain ⟨hl,hr⟩ := h.selectedTrack_reflections x y hx hy hxb hya
      (by simpa only [pow_two] using hx2) (by simpa only [pow_two] using hy2)
    exact ⟨x,y,hx2,hy2,hl,hr⟩
  · obtain ⟨t,h0,h1⟩ := h.exists_track
    exact ⟨t,h0,h1,fun hh => (hm hh).elim⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
