module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.TwoNeighborCore
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySuzukiKernels

/-!
# Interior core control for actual path stabilizers

For either orientation of the original linear/Suzuki markings, every
two-subgroup fixing a nonbacktracking path fixes two distinct neighbors
at each interior vertex. TwoNeighborCore therefore puts it in every
interior vertex core. Conversely those cores fix the whole path, and
their intersection is a normal two-subgroup of the path stabilizer.
This identifies its literal two-core and preserves the original inclusion,
for every Suzuki parameter. When both markings are binary, the proved
full-Borel identity makes the entire path stabilizer a two-group, so the
same intersection equals the full path stabilizer.

This proves the core-placement step in DGS85 (12.7), printed p.184.
The further argument that a nine-path has trivial two-core is not asserted
here; it requires the remaining centralizer-propagation argument of (12.7).
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups CommutingNontrivial Theory.GroupTheory.AmalgamLocalCores
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
section Mixed
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {n : ℕ}
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)

include h i eLin eSuz

/-- Every two-subgroup fixing a nonbacktracking path lies in all its interior cores. -/
theorem source_mixed_path_two_subgroup_core {r : ℕ} {a : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) (r+2) a) (hp : p.Nonbacktracking)
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p) :
    ∀ v ∈ p.2.vertices.dropLast, D ≤ Q (reducedFamily L S) v := by
  let F := reducedFamily L S
  induction r generalizing a with
  | zero =>
    rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,q⟩⟩
    intro v hv
    have hvb : v = b := by simpa only [BasedWalk.vertices, List.dropLast_cons_cons,
      List.dropLast_singleton, List.mem_singleton] using hv
    subst v
    apply source_mixed_two_neighbor_core h i eLin eSuz hab.symm hbc hp.1.symm D hD
    · intro d hd
      exact hfix hd b (by change b ∈ [a,b,c]; simp)
    · intro d hd
      exact hfix hd a (by change a ∈ [a,b,c]; simp)
    · intro d hd
      exact hfix hd c (by change c ∈ [a,b,c]; simp)
  | succ r ih =>
    rcases p with ⟨⟨b,hab⟩,q⟩
    have hq : D ≤ pathStabilizer F q := by
      intro d hd v hv
      exact hfix hd v (List.mem_cons_of_mem a hv)
    have hfirst : D ≤ Q F b := by
      apply source_mixed_two_neighbor_core h i eLin eSuz hab.symm q.1.property hp.1.symm D hD
      · exact hq.trans (pathStabilizer_le F q)
      · exact hfix.trans (pathStabilizer_le F _)
      · intro d hd
        exact hq hd q.1.val (List.mem_cons_of_mem b (origin_mem_vertices F q.2))
    intro v hv
    have he : q.vertices.dropLast = b :: q.2.vertices.dropLast := by
      change (b :: q.2.vertices).dropLast = _
      exact List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (origin_mem_vertices F q.2))
    rw [he,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hfirst
    · exact ih q hp.2 hq v hv

omit i eLin eSuz in
private theorem internal_cores_fix_path {r : ℕ} {a : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) (r+2) a)
    (D : Subgroup (G₀ L S))
    (hD : ∀ v ∈ p.2.vertices.dropLast, D ≤ Q (reducedFamily L S) v) :
    D ≤ pathStabilizer (reducedFamily L S) p := by
  let F := reducedFamily L S
  induction r generalizing a with
  | zero =>
    rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,q⟩⟩
    have hb : D ≤ Q F b := hD b (by change b ∈ [b]; exact List.mem_singleton_self _)
    have hu : D ≤ U F b := hb.trans (source_Z_Q_U (reduced_triple h) b).2
    intro d hd v hv
    change v ∈ [a,b,c] at hv
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hv :
      v = a ∨ v = b ∨ v = c) with hva | hvb | hvc
    · subst v
      exact hu hd a ((mem_ball_one F b a).mpr (.inl hab.symm))
    · subst v
      exact Q_le_stabilizer F b (hb hd)
    · subst v
      exact hu hd c ((mem_ball_one F b c).mpr (.inl hbc))
  | succ r ih =>
    rcases p with ⟨⟨b,hab⟩,q⟩
    have he : q.vertices.dropLast = b :: q.2.vertices.dropLast := by
      change (b :: q.2.vertices).dropLast = _
      exact List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (origin_mem_vertices F q.2))
    have hb : D ≤ Q F b := hD b (by rw [he]; exact List.mem_cons_self)
    have htail := ih q (fun v hv => hD v (by rw [he]; exact List.mem_cons_of_mem b hv))
    intro d hd v hv
    change v ∈ a :: q.vertices at hv
    rcases List.mem_cons.mp hv with hva | hv
    · subst v
      exact (source_Z_Q_U (reduced_triple h) b).2 (hb hd) a
        ((mem_ball_one F b a).mpr (.inl hab.symm))
    · exact htail hd v hv

/-- The full path fixer's two-core is exactly the intersection of the interior cores. -/
theorem source_mixed_path_core_intersection {r : ℕ} {a : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) (r+2) a) (hp : p.Nonbacktracking) :
    let F := reducedFamily L S
    let I : Subgroup (G₀ L S) := ⨅ v, ⨅ (_ : v ∈ p.2.vertices.dropLast), Q F v
    (pathStabilizer F p).pCoreIn 2 = I ∧
    ((pathStabilizer F p).map (G₀ L S).subtype).pCoreIn 2 = I.map (G₀ L S).subtype ∧
    ∀ v ∈ p.2.vertices.dropLast,
      (pathStabilizer F p).pCoreIn 2 ≤ centralizer (Z F v : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let I : Subgroup (G₀ L S) := ⨅ v, ⨅ (_ : v ∈ p.2.vertices.dropLast), Q F v
  let P := pathStabilizer F p
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  have hIv (v) (hv : v ∈ p.2.vertices.dropLast) : I ≤ Q F v :=
    iInf_le_of_le v (iInf_le _ hv)
  have hPI : P.pCoreIn 2 ≤ I := le_iInf fun v => le_iInf fun hv =>
    source_mixed_path_two_subgroup_core h i eLin eSuz p hp _ (isPGroup_pCoreIn 2 P)
      (pCoreIn_le 2 P) v hv
  have hfirst : (p.1 : Vertex F) ∈ p.2.vertices.dropLast := by
    change (p.1 : Vertex F) ∈ ((p.1 : Vertex F) :: p.2.2.vertices).dropLast
    rw [List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (origin_mem_vertices F p.2.2))]
    exact List.mem_cons_self
  have hIP : I ≤ P := internal_cores_fix_path h p I hIv
  have hnI : P ≤ normalizer (I : Set (G₀ L S)) := by
    apply le_normalizer_iff.mpr
    intro g hg z hz
    apply mem_iInf.mpr
    intro v
    apply mem_iInf.mpr
    intro hv
    have hgv : g ∈ stabilizer F v := hg v
      (List.mem_cons_of_mem a (List.mem_of_mem_dropLast hv))
    exact (mem_normalizer_iff.mp (CommutingNontrivial.stabilizer_normalizes_Q F v hgv) z).mp
      (hIv v hv hz)
  have he : P.pCoreIn 2 = I := le_antisymm hPI (le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 (stabilizer F (p.1 : Vertex F))).to_le (hIv _ hfirst)) hIP hnI)
  refine ⟨he, ?_, ?_⟩
  · rw [pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,he]
  · intro v hv
    apply (hPI.trans (hIv v hv)).trans
    apply le_centralizer_iff.mp
    intro z hz q hq
    exact Z_centralizes_Q F v (source_Z_Q_U (reduced_triple h) v).1 hz q hq

end Mixed

/-- With the two binary markings, the full path stabilizer equals the interior-core intersection. -/
theorem source_binary_suzuki_path_stabilizer_intersection
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,ZMod 2))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    {r : ℕ} {a : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) (r+2) a) (hp : p.Nonbacktracking) :
    let F := reducedFamily L S
    let I : Subgroup (G₀ L S) := ⨅ v, ⨅ (_ : v ∈ p.2.vertices.dropLast), Q F v
    pathStabilizer F p = I ∧
    (pathStabilizer F p).map (G₀ L S).subtype = I.map (G₀ L S).subtype ∧
    IsPGroup 2 (pathStabilizer F p) := by
  let F := reducedFamily L S
  let P := pathStabilizer F p
  have hbase : IsPGroup 2 (F false ⊓ F true : Subgroup (G₀ L S)) := by
    change IsPGroup 2 (((P₀ L S 0).subgroupOf (G₀ L S)) ⊓
      ((P₀ L S 1).subgroupOf (G₀ L S)) : Subgroup (G₀ L S))
    rw [(reduced_triple h).intersection,
      binary_suzuki_reduced_borel h (!i) eSuz (by cases i <;> exact eLin)]
    exact h.S_isP.comap_subtype
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F p.1.property
  have hedge : IsPGroup 2 (stabilizer F a ⊓ stabilizer F (p.1 : Vertex F) : Subgroup (G₀ L S)) := by
    rw [hg]
    exact hbase.map _
  have hP : IsPGroup 2 P := hedge.to_le (le_inf (pathStabilizer_le F p) (by
    intro d hd
    exact hd (p.1 : Vertex F) (List.mem_cons_of_mem a (origin_mem_vertices F p.2))))
  have he := (source_mixed_path_core_intersection h i eLin eSuz p hp).1
  rw [pCoreIn_eq_self_of_isPGroup 2 P hP] at he
  exact ⟨he,congrArg (Subgroup.map (G₀ L S).subtype) he,hP⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
