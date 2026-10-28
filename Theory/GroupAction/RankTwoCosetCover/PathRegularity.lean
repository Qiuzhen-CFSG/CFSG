module
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.GroupAction.CubicTree.ArcTransport

/-!
# Endpoint regularity through coset coverings

A coset cover identifies each full pointwise path stabilizer and bijects the
neighbors at both endpoints. These maps preserve the excluded predecessor,
so regularity transfers in both directions along the literal path lifting
equivalence. In particular, two completions of the same marked amalgam have
the same regular nonbacktracking path lengths.

Source: Aschbacher--Smith, F.3.3--4, pp.270--271; DGS, *Groups and Graphs*
(1985), endpoint regularity on pp.73--74.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Subgroup.CosetGeometry.RankTwo.CoverData
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
variable {A B : Type*} [Group A] [Group B]
variable {F : Bool → Subgroup A} {E : Bool → Subgroup B}
variable {f : A →* B} (c : CoverData F E f)

private theorem penultimate_map {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) (n+1) v) :
    (p.map c.hom).penultimate = c.vertex p.penultimate := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih p.2

private theorem forward_image {n : ℕ} {v z : Vertex F}
    (p : BasedWalk (graph F) n v) (hz : (graph F).Adj p.endpoint z) :
    Forward (p.map c.hom) (c.vertex z) ↔ Forward p z := by
  cases n with
  | zero => exact ⟨fun _ => hz,fun _ => c.hom.map_adj hz⟩
  | succ n =>
    simp only [Forward,endpoint_map,penultimate_map]
    constructor
    · exact fun hh => ⟨hz,fun he => hh.2 (congrArg c.vertex he)⟩
    · intro hh
      refine ⟨c.hom.map_adj hz,?_⟩
      intro he
      exact hh.2 (congrArg Subtype.val ((c.neighbor_bijective p.endpoint).1
        (a₁ := ⟨z,hz⟩) (a₂ := ⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩)
        (Subtype.ext he)))

private theorem forward_lift {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) {z : Vertex E}
    (hz : Forward (p.map c.hom) z) :
    ∃ w, Forward p w ∧ c.vertex w = z := by
  have hzadj : (graph E).Adj (c.hom p.endpoint) z := by
    simpa only [endpoint_map] using forward_adj (p.map c.hom) hz
  obtain ⟨w,hw⟩ := (c.neighbor_bijective p.endpoint).2 ⟨z,hzadj⟩
  have he : c.vertex w = z := congrArg Subtype.val hw
  exact ⟨w,(c.forward_image p w.property).mp (he.symm ▸ hz),he⟩

/-- The whole path fixer has the same action on forward continuations. -/
theorem rightRegular_pathEquiv_iff {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) :
    RightRegular (A := B) (c.pathEquiv n v p) ↔ RightRegular (A := A) p := by
  constructor
  · intro hr z w hz hw
    have hr' : RightRegular (A := B) (p.map c.hom) := by
      simpa only [pathEquiv_apply] using hr
    obtain ⟨b,hb,he⟩ := hr' (c.vertex z) (c.vertex w)
      ((c.forward_image p (forward_adj p hz)).mpr hz)
      ((c.forward_image p (forward_adj p hw)).mpr hw)
    have hb' : b ∈ (pathStabilizer F p).map f := by
      rw [c.pathStabilizer_map p]
      change ∀ y ∈ (c.pathEquiv n v p).vertices, b • y = y
      simpa only [pathEquiv_apply] using hb
    obtain ⟨a,ha,rfl⟩ := hb'
    refine ⟨a,ha,?_⟩
    have haend : a • p.endpoint = p.endpoint := ha _ (by
      rw [←support_toWalk]
      exact Walk.end_mem_support _)
    have haz : (graph F).Adj p.endpoint (a • z) := by
      have hh := (translationGraphIso F a).toHom.map_adj (forward_adj p hz)
      change (graph F).Adj (a • p.endpoint) (a • z) at hh
      rwa [haend] at hh
    exact congrArg Subtype.val ((c.neighbor_bijective p.endpoint).1
      (a₁ := ⟨a • z,haz⟩) (a₂ := ⟨w,forward_adj p hw⟩)
      (Subtype.ext ((c.vertex_smul a z).trans he)))
  · intro hr z w hz hw
    have hz' : Forward (p.map c.hom) z := by simpa only [pathEquiv_apply] using hz
    have hw' : Forward (p.map c.hom) w := by simpa only [pathEquiv_apply] using hw
    obtain ⟨z',hzp,rfl⟩ := c.forward_lift p hz'
    obtain ⟨w',hwp,rfl⟩ := c.forward_lift p hw'
    obtain ⟨a,ha,he⟩ := hr z' w' hzp hwp
    refine ⟨f a,?_,(c.vertex_smul a z').symm.trans (congrArg c.vertex he)⟩
    have hh : f a ∈ (pathStabilizer F p).map f := Subgroup.mem_map_of_mem f ha
    rwa [c.pathStabilizer_map p] at hh

/-- Reversal gives the corresponding left endpoint action as well. -/
theorem regular_pathEquiv_iff {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) :
    Regular (A := B) (c.pathEquiv n v p) ↔ Regular (A := A) p := by
  have he : (c.pathEquiv n p.endpoint (reverse p)).vertices =
      (reverse (c.pathEquiv n v p)).vertices := by
    simp only [pathEquiv_vertices,vertices_reverse,List.map_reverse]
  have hl : LeftRegular (A := B) (c.pathEquiv n v p) ↔ LeftRegular (A := A) p := by
    rw [← rightRegular_reverse_iff, ← rightRegular_reverse_iff p,
      ← c.rightRegular_pathEquiv_iff (reverse p)]
    exact ⟨rightRegular_of_vertices_eq _ _ he.symm,
      rightRegular_of_vertices_eq _ _ he⟩
  exact and_congr hl (c.rightRegular_pathEquiv_iff p)

/-- A regular nonbacktracking path exists at the image root exactly when it
exists at the chosen root of the cover. -/
theorem exists_regular_path_iff (n : ℕ) (v : Vertex F) :
    (∃ p : BasedWalk (graph E) n (c.vertex v),
      p.Nonbacktracking ∧ Regular (A := B) p) ↔
    (∃ p : BasedWalk (graph F) n v, p.Nonbacktracking ∧ Regular (A := A) p) := by
  constructor
  · rintro ⟨p,hp,hr⟩
    obtain ⟨q,rfl⟩ := (c.pathEquiv n v).surjective p
    refine ⟨q,?_,(c.regular_pathEquiv_iff q).mp hr⟩
    exact (BasedWalk.nonbacktracking_map_iff c.hom
      (fun v => (c.neighbor_bijective v).1) q).mp (by
        simpa only [pathEquiv_apply] using hp)
  · rintro ⟨p,hp,hr⟩
    refine ⟨c.pathEquiv n v p,?_,(c.regular_pathEquiv_iff p).mpr hr⟩
    simpa only [pathEquiv_apply] using
      (BasedWalk.nonbacktracking_map_iff c.hom
        (fun v => (c.neighbor_bijective v).1) p).mpr hp

end Subgroup.CosetGeometry.RankTwo.CoverData
