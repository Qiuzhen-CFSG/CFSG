module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NoncentralSimpleExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement

/-!
# Simple nonlinear replacement exclusions in the original reduced graph

The original F1.11 quotient markings supply the actual enlarged quotients
through the proved Suzuki and projective-unitary enlargement maps. Apply
the replacement-offender exclusion to the reduced triple, its actual
Borel two-core Sylow and both original endpoint cores. This removes the
noncentral neighboring-center branch under contrary relative normality
without a new kernel, offender, or model-recognition premise.

The conclusion concerns the literal full-neighbor closure in G₀. The
quotient maps used here retain the original starred inclusion and original
marking through their existing representative formulas. Neither the
central case nor the full adjacent-core obstruction is inferred.

Source: DGS, Groups and Graphs (1985), reduction p.95 and6.4, pp.120--121;
Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private def suzukiEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {m : ℕ} (hm : 0 < m) (e : (L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* SuzukiMatrixGroup m := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSuzukiQuotient h false hm e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSuzukiQuotient h true hm e)

private def projectiveUnitaryEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* ProjectiveSpecialUnitaryMatrixGroup J := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphProjectiveUnitaryQuotient h false J hn hcard hconj e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphProjectiveUnitaryQuotient h true J hn hcard hconj e)

/-- The original Suzuki quotient discharges all model and action premises of the noncentral replacement exclusion. -/
theorem reduced_suzuki_neighbor_center_central (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    {m : ℕ} (hm : 0 < m)
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* SuzukiMatrixGroup m) :
    sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S)) :=
  source_suzuki_neighbor_center_central (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    ((inter_core_local_normal_iff (reduced_triple h) i _).mp hn) hm
    (suzukiEnlargementQuotient h (other i) _ hm e)

/-- The original projective-unitary quotient gives the exclusion with full Borel and endpoint cores retained. -/
theorem reduced_projective_unitary_neighbor_center_central (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S)) :=
  source_projective_unitary_neighbor_center_central (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    ((inter_core_local_normal_iff (reduced_triple h) i _).mp hn) J hnpos hcard hconj
    (projectiveUnitaryEnlargementQuotient h (other i) _ J hnpos hcard hconj e)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
