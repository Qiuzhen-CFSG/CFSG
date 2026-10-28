module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NoncentralSpecialUnitaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryApplication

/-!
# Full special-unitary replacement exclusion on the reduced F1.11 triple

The actual original SU₃ quotient and its proved enlargement equality
supply the full special-unitary quotient map. Apply the replacement
exclusion with the original reduced endpoint cores and full-neighbor
closure. Cubic scalar centers are retained, including when they act
trivially on the selected simple section.

This discharges the noncentral neighboring-center alternative under
contrary relative normality for every fixed-field degree at least two.
The central case, degree-one enlargement and final 6.5 assembly remain.
Source: DGS, Groups and Graphs (1985), reduction p.95 and 6.4,
pp.120--121; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private def specialUnitaryEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* J.specialSubgroup := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSpecialUnitaryQuotient h false J hn hcard hconj e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSpecialUnitaryQuotient h true J hn hcard hconj e)

/-- The original special-unitary quotient gives the exclusion with full Borel and endpoint cores retained. -/
theorem reduced_special_unitary_neighbor_center_central (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* J.specialSubgroup) :
    sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S)) :=
  source_special_unitary_neighbor_center_central (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    ((inter_core_local_normal_iff (reduced_triple h) i _).mp hn) J hnpos hcard hconj
    (specialUnitaryEnlargementQuotient h (other i) _ J hnpos hcard hconj e)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
