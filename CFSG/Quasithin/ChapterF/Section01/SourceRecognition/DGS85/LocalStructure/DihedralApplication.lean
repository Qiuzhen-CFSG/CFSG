module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.DihedralEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
/-!
# Dihedral enlargement on the actual reduced F1.11 graph

The original quotient marking gives either equality of the full-Borel-core
enlargement with the original starred parabolic or a concrete Sz(2)
quotient. The actual graph actor embeds onto this same enlargement. Its
core quotient equivalence records the original completion inclusion on
representatives, and the dichotomy supplies a genuine rank-one model for
the Chapter 6 local actor. The original full Borel is retained in the
enlargement; no assumption that the original S equals its core is used.

Source: DGS, *Groups and Graphs* (1985), 6.1 and its remark, pp.118--119;
Aschbacher--Smith F.1.9, printed pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original marked dihedral quotient gives the source 6.1 alternative. -/
theorem reduced_dihedral_enlargement_alternatives (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) :
    enlargedEndpoint L S i = starredParabolic L S i ∨
      Nonempty ((enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_dihedral_alternatives (hh.starredLocalRankOneData i)
    ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  rcases he with he | he
  · exact Or.inl (he.trans (SuzukiContainment.reduced_starredParabolic h i))
  · exact Or.inr he

/-- The graph actor embeds onto the original full-Borel-core enlargement. -/
def reduced_enlargementActorEquiv (h : HypothesisF11 L S) (i : Bool) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (enlargedEndpoint L S) i :=
  ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_graphLocalGroup_image h i))

/-- The actor equivalence is the original completion inclusion. -/
theorem reduced_enlargementActorEquiv_coe (h : HypothesisF11 L S) (i : Bool)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_enlargementActorEquiv h i x : G) = (x : G₀ L S) := by rfl

/-- The two-core quotient equivalence induced by that inclusion. -/
def reduced_graphEnlargementQuotient (h : HypothesisF11 L S) (i : Bool) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        (family (enlargedEndpoint L S) i ⧸ pCore 2 (family (enlargedEndpoint L S) i)) :=
  QuotientGroup.congr _ _ (reduced_enlargementActorEquiv h i)
    (pCore_map_iso 2 _)

/-- Representatives retain the original actor inclusion. -/
theorem reduced_graphEnlargementQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphEnlargementQuotient h i (QuotientGroup.mk x) =
      QuotientGroup.mk (reduced_enlargementActorEquiv h i x) := by rfl

/-- The actual graph quotient is D₁₀ or the concrete Sz(2), with starred equality in the first branch. -/
theorem reduced_graph_dihedral_alternatives (h : HypothesisF11 L S) (i : Bool)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* DihedralGroup 5) :
    ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
        (G₀ L S).subtype = family (starredParabolic L S) i ∧
      Nonempty ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
        pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
          DihedralGroup 5)) ∨
    Nonempty ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  have hh : family (enlargedEndpoint L S) i = family (starredParabolic L S) i ∨
      Nonempty ((family (enlargedEndpoint L S) i ⧸ pCore 2 (family (enlargedEndpoint L S) i)) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
    cases i
    · exact reduced_dihedral_enlargement_alternatives h 0 e
    · exact reduced_dihedral_enlargement_alternatives h 1 e
  rcases hh with hh | hf
  · left
    refine ⟨(reduced_graphLocalGroup_image h i).trans hh,?_⟩
    let c := MulEquiv.subgroupCongr hh
    exact ⟨(reduced_graphEnlargementQuotient h i).trans
      ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
        ((originalStarredQuotientEquiv h i).symm.trans e))⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨(reduced_graphEnlargementQuotient h i).trans f⟩

/-- The dihedral source row supplies the rank-one premise for the Chapter 6 graph actor. -/
theorem reduced_graph_dihedral_rankOne (h : HypothesisF11 L S) (i : Bool)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* DihedralGroup 5) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) := by
  rcases reduced_graph_dihedral_alternatives h i e with ⟨_,he⟩ | he
  · exact .dihedral he
  · exact .suzuki 0 he

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
