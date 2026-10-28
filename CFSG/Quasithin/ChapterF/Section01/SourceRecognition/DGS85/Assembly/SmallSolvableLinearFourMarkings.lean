module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourDistance
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Literal local markings in the small-solvable / A₅ pair

Transport the original endpoint quotients to every vertex of the actual
reduced graph. A D₁₀ endpoint may enlarge to Sz(2); this alternative is
retained. The A₅ endpoint remains A₅ through its field-four linear marking.
Together these results discharge the earlier-local rank-one catalogue on
both the reduced actors and their literal images in the original group.

The Chapter 15 marked-five critical-edge consumer uses this catalogue without
choosing or reversing the directed critical edge. These transports do not
assert the remaining distance-one exclusion.
Source: DGS, *Groups and Graphs* (1985), reduction pp.95--96 and Chapter 11;
Aschbacher--Smith 15.2.4--8, printed pp.1106--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

/-- The original small-solvable endpoint gives precisely the two possible
small-solvable graph-local markings at every vertex of its type. -/
theorem small_solvable_graph_quotients (h : HypothesisF11 L S) (j : Bool)
    (hm : Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* DihedralGroup 5) ∨
      Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* SuzukiMatrixGroup 0))
    (v : Vertex F) (hv : v.type = j) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SuzukiMatrixGroup 0) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  rcases hm with hm | hm
  · rcases Reduction.reduced_graph_dihedral_alternatives h j hm.some with hd | hs
    · exact Or.inl ⟨f.symm.trans hd.2.some⟩
    · exact Or.inr ⟨f.symm.trans hs.some⟩
  · exact Or.inr ⟨f.symm.trans (Reduction.reduced_graphSuzukiQuotient_all h j 0 hm.some)⟩

/-- An original characteristic-two linear marking transports to the actual
graph-local actor at every vertex of that endpoint type. -/
theorem linear_graph_quotient (h : HypothesisF11 L S) (j : Bool)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (family L j ⧸ pCore 2 (family L j)) ≃* PSL(2,K))
    (v : Vertex F) (hv : v.type = j) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K)) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  exact ⟨f.symm.trans ((Reduction.reduced_graphLinearQuotient h j e).trans
    (Theory.PSL2.sl2QuotientEquiv K).symm)⟩

/-- The original A₅ quotient remains A₅ on every actual graph-local actor
of its type; the equivalence uses the field-four linear enlargement. -/
theorem a5_graph_quotient (h : HypothesisF11 L S) (j : Bool)
    (e : (family L j ⧸ pCore 2 (family L j)) ≃* alternatingGroup (Fin 5))
    (v : Vertex F) (hv : v.type = j) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      alternatingGroup (Fin 5)) := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  obtain ⟨ev⟩ := linear_graph_quotient h j (e.trans e₄.symm) v hv
  exact ⟨(ev.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2))).trans e₄⟩

/-- The complete canonical graph-local catalogue of the original mixed pair.
No separate earlier-local rank-one premise is required by its consumers. -/
theorem small_solvable_a5_graph_models (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)))
    (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  by_cases hv : v.type = true
  · have hc : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by decide)]
      norm_num
    obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
    exact .linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
      (by simpa using hc),⟨(a5_graph_quotient h true ha.some v hv).some.trans e₄.symm⟩⟩
  · rcases small_solvable_graph_quotients h false hm v (Bool.eq_false_iff.mpr hv) with hd | hs
    · exact .dihedral hd
    · exact .suzuki 0 hs

/-- The same complete catalogue on the literal actor images in the original
completion, along the actual reduced-to-original inclusion. -/
theorem small_solvable_a5_original_graph_models (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)))
    (v : Vertex F) :
    IsRankOneModel ((graphLocalGroup F v).map (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup F v).map (Reduction.G₀ L S).subtype)) := by
  let e := (graphLocalGroup F v).equivMapOfInjective
    (Reduction.G₀ L S).subtype (Reduction.G₀ L S).subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact (small_solvable_a5_graph_models h hm ha v).of_equiv eq.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
