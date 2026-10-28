module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathSupplement
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel

/-!
# The path-fixer core at a linear endpoint

The path product from 6.7 is applied to the terminal edge. The full
normalizer calculation marks any supplied linear local quotient at the
penultimate vertex. Root irreducibility and the explicit root action then
force the path-fixer two-core into the full endpoint kernel whenever the
fixer is not transitive on the remaining neighbors: DGS 6.8(a). The proved
Sylow control of that kernel further puts the same core in Q.

The reduced F1.11 application discharges the source graph and Sylow
hypotheses and transports through the original inclusion. The linear
quotient and Chapter 3 path-transitivity/model-branching inputs remain
explicit. No conclusion about the path length is asserted here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.2(d), 6.7 and 6.8(a), pp.119 and 123.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem endpoint_mem_vertices {F : Bool → Subgroup G} {v : Vertex F} {n : ℕ}
    (p : BasedWalk (graph F) n v) : p.endpoint ∈ p.vertices := by
  induction n generalizing v with
  | zero => exact List.mem_cons_self
  | succ n ih => exact List.mem_cons_of_mem _ (ih p.2)

private theorem penultimate_mem_vertices {F : Bool → Subgroup G} {v : Vertex F} {n : ℕ}
    (p : BasedWalk (graph F) (n+1) v) : p.penultimate ∈ p.vertices := by
  induction n generalizing v with
  | zero => exact List.mem_cons_self
  | succ n ih => exact List.mem_cons_of_mem _ (ih p.2)

/-- In the source two-closed edge, a two-subgroup of the full local kernel
lies in the actual vertex core. This does not identify the two kernels. -/
theorem source_pGroup_le_Q_of_le_U (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAU : A ≤ U (family P) v) :
    A ≤ Q (family P) v := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) v from inf_le_left))
    (inclusion_injective _)
  have hUE : U (family P) v ≤ E := ballKernel_one_le_edge (family P) hvw
  let : Finite (U (family P) v) := Finite.of_injective (inclusion hUE) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hvw
  have hs := core_sylow_of_le E (U (family P) v) hUE (source_edge_core_sylow h hB hvw)
  exact (pGroup_le_core_of_core_sylow _ A hAU hA hs).trans_eq
    (core_ballKernel_one (family P) hvw T (hT.trans inf_le_right))

/-- DGS 6.8(a) for the literal path fixer and full endpoint kernel. The
actual linear quotient is the model premise; its action marking is proved. -/
theorem source_path_core_le_endpoint_kernel (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (q : graphLocalGroup (family P) p.endpoint →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : Function.Surjective q)
    (hk : q.ker = (Q (family P) p.endpoint).subgroupOf (graphLocalGroup (family P) p.endpoint))
    (hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val) :
    (pathStabilizer (family P) p).pCoreIn 2 ≤ U (family P) p.endpoint := by
  have hadj := p.adj_penultimate_endpoint.symm
  obtain ⟨a,ha⟩ := source_linear_borel_marking h hB hS hadj q hq hk
  exact core_le_ballKernel_of_linear_supplement (family P) _
    (pathStabilizer_le_edge (family P) p (endpoint_mem_vertices p) (penultimate_mem_vertices p))
    ((MulAut.conj a).toMonoidHom.comp q) ((MulAut.conj a).surjective.comp hq) ha
    (source_path_edge_product h hB hbranch ht p hp hadj
      (endpoint_mem_vertices p) (penultimate_mem_vertices p))
    (fun x => graphLocalGroup_transitive h hB hS p.endpoint ⟨p.penultimate,hadj⟩ x) hnot

/-- The exact local quotient supplies the homomorphism and its vertex-core
kernel. This is the linear source hypothesis of 6.8, with no extra marking. -/
theorem source_path_core_le_endpoint_kernel_of_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) p.endpoint ⧸ pCore 2 (graphLocalGroup (family P) p.endpoint)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val) :
    (pathStabilizer (family P) p).pCoreIn 2 ≤ U (family P) p.endpoint := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) p.endpoint
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hc : L.pCoreIn 2 = Q (family P) p.endpoint := sylowGenerated_core _
  have hk : q.ker = (Q (family P) p.endpoint).subgroupOf L := by
    rw [← hc]
    change q.ker = ((pCore 2 L).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact source_path_core_le_endpoint_kernel h hB hS hbranch ht p hp q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk hnot

/-- The path two-core also lies in the endpoint two-core, by the proved
Sylow property of the full local kernel. -/
theorem source_path_core_le_endpoint_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) p.endpoint ⧸ pCore 2 (graphLocalGroup (family P) p.endpoint)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val) :
    (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint :=
  source_pGroup_le_Q_of_le_U h hB hS p.adj_penultimate_endpoint.symm _
    (isPGroup_pCoreIn 2 _) (source_path_core_le_endpoint_kernel_of_quotient h hB hS hbranch ht p hp e hnot)

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The actual reduced F1.11 path, with every graph, Sylow and marking
premise discharged. The printed linear quotient and path inputs are retained. -/
theorem reduced_path_core_le_endpoint_kernel (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (reducedFamily L S) p.endpoint ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) p.endpoint)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (reducedFamily L S)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (reducedFamily L S) p, g • x.val = y.val) :
    (pathStabilizer (reducedFamily L S) p).pCoreIn 2 ≤ U (reducedFamily L S) p.endpoint :=
  source_path_core_le_endpoint_kernel_of_quotient (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hbranch ht p hp e hnot

/-- The same path-core assertion after the literal reduced-to-original
inclusion. The core is computed in the actual original image of the fixer. -/
theorem reduced_path_original_core_le_endpoint_kernel (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (reducedFamily L S) p.endpoint ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) p.endpoint)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (reducedFamily L S)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (reducedFamily L S) p, g • x.val = y.val) :
    ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype).pCoreIn 2 ≤
      (U (reducedFamily L S) p.endpoint).map (G₀ L S).subtype := by
  rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
  exact map_mono (reduced_path_core_le_endpoint_kernel h hbranch ht p hp e hnot)
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
