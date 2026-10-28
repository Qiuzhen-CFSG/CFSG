module
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRoot
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Long-path roots and ball kernels under coset coverings

The actual covering homomorphism maps the full path fixer onto the target
path fixer and is injective on it. Consequently it maps their two-cores
exactly. An element fixing a source vertex lifts fixation of a target ball:
local injectivity propagates fixation along each lifted path.

These statements use the literal covering map, with no global injectivity
or identification of quotient vertex fibers with group-kernel orbits.
The b=1 DGS application is Assembly/BOneMidpointCover.
Source: Aschbacher--Smith F.3.3--4, printed p.270; DGS, Groups and Graphs
(1985), the universal-tree setup and path roots, pp.208--211.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph
namespace Subgroup.CosetGeometry.RankTwo.CoverData
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y : Type*} [Group X] [Group Y]
  {F : Bool → Subgroup X} {E : Bool → Subgroup Y} {f : X →* Y}
  (c : CoverData F E f)

/-- The graph homomorphism uses exactly the covering's vertex map. -/
theorem hom_apply_vertex (v : Vertex F) : c.hom v=c.vertex v := rfl

private theorem pathFixer_eq_pathStabilizer {a b : Vertex F} (p : (graph F).Walk a b) :
    pathFixer (X := X) p = pathStabilizer F (BasedWalk.ofWalk p) := by
  ext x
  change (∀ j ≤ p.length, x • p.getVert j=p.getVert j) ↔
    ∀ z ∈ (BasedWalk.ofWalk p).vertices, x • z=z
  rw [BasedWalk.vertices_ofWalk]
  constructor
  · intro hx z hz
    obtain ⟨j,rfl,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    exact hx j hj
  · intro hx j hj
    exact hx _ (Walk.mem_support_iff_exists_getVert.mpr ⟨j,rfl,hj⟩)

/-- The literal image of the complete pointwise path fixer. -/
theorem pathFixer_map {a b : Vertex F} (p : (graph F).Walk a b) :
    (pathFixer (X := X) p).map f = pathFixer (X := Y) (p.map c.hom) := by
  rw [pathFixer_eq_pathStabilizer,pathFixer_eq_pathStabilizer,c.pathStabilizer_map]
  ext x
  change (∀ z ∈ (c.pathEquiv p.length a (BasedWalk.ofWalk p)).vertices, x • z=z) ↔
    ∀ z ∈ (BasedWalk.ofWalk (p.map c.hom)).vertices, x • z=z
  rw [c.pathEquiv_vertices,BasedWalk.vertices_ofWalk,BasedWalk.vertices_ofWalk,Walk.support_map]
  rfl

/-- The covering preserves the embedded two-core of the same path fixer. -/
theorem pathRoot_map {a b : Vertex F} (p : (graph F).Walk a b) :
    (pathRoot (X := X) p).map f = pathRoot (X := Y) (p.map c.hom) := by
  have hle : pathFixer (X := X) p ≤ stabilizer F a := by
    intro x hx
    change x • a=a
    simpa only [Walk.getVert_zero] using hx 0 (Nat.zero_le _)
  let φ := f.comp (pathFixer (X := X) p).subtype
  have hi : Function.Injective φ := by
    intro x y he
    have hh := (c.stabilizerHom_bijective a).1
      (a₁ := ⟨x,hle x.property⟩) (a₂ := ⟨y,hle y.property⟩) (Subtype.ext he)
    exact Subtype.ext (congrArg (fun z : stabilizer F a => (z:X)) hh)
  have hm : φ.range=pathFixer (X := Y) (p.map c.hom) := by
    rw [MonoidHom.range_comp,range_subtype,c.pathFixer_map]
  have hh := pCoreIn_range_of_injective 2 φ hi
  rw [hm] at hh
  simpa only [pathRoot,pCoreIn,Subgroup.map_map] using hh.symm

/-- Fixation lifts locally through the same covering, at every finite radius. -/
theorem ballKernel_lift (v : Vertex F) (n : ℕ) (x : X)
    (hx : x • v=v) (hf : f x∈ballKernel E (c.vertex v) n) :
    x∈ballKernel F v n := by
  intro z hz
  change (graph F).edist v z≤(n:ℕ∞) at hz
  obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (show (graph F).edist v z ≠ ⊤ from ne_top_of_le_ne_top (by simp) hz)
  have hlen : p.length≤n := by exact_mod_cast hp.symm ▸ hz
  have hfix : f x∈pathFixer (X := Y) (p.map c.hom) := by
    intro j hj
    rw [Walk.getVert_map]
    apply hf
    change (graph E).edist (c.vertex v) (c.vertex (p.getVert j))≤(n:ℕ∞)
    exact ((p.take j).map c.hom).edist_le.trans (by
      rw [Walk.length_map,Walk.take_length]
      exact_mod_cast (min_le_right j p.length).trans hlen)
  rw [←c.pathFixer_map p] at hfix
  obtain ⟨y,hy,he⟩ := hfix
  have hyv : y • v=v := by simpa only [Walk.getVert_zero] using hy 0 (Nat.zero_le _)
  have heq := (c.stabilizerHom_bijective v).1
    (a₁ := ⟨y,hyv⟩) (a₂ := ⟨x,hx⟩) (Subtype.ext he)
  have hyx : y=x := congrArg Subtype.val heq
  simpa only [Walk.getVert_length,hyx] using hy p.length le_rfl

end Subgroup.CosetGeometry.RankTwo.CoverData
