module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSeedApplication

/-!
# The literal mixed A₅/S₃ graph markings

The original quotient markings determine SL₂(4) and SL₂(2) at every
vertex of the respective types in the reduced graph. They supply the
complete rank-one catalogue for the critical-distance alternatives and
the numerical mixed-pair source proof. The reduced-to-original actor
inclusion transports the same catalogue without identifying a completion.

Source: DGS, *Groups and Graphs* (1985), reduction pp.95--96;
Aschbacher--Smith F.1.12(I), printed pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The quintic vertex type carries the actual field-four linear quotient. -/
theorem graph_linear_four (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (v : Vertex F) (hv : v.type = false) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,GaloisField 2 2)) := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact Assembly.linear_graph_quotient h false (eK.trans e₄.symm) v hv

/-- The cubic vertex type carries the actual binary linear quotient. -/
theorem graph_linear_two (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) (hv : v.type = true) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,ZMod 2)) :=
  ⟨(Assembly.symmetricThree_graph_quotient h true eU v hv).some.trans
    SLTwoPermThree.sl2Two_equiv_perm_three.some.symm⟩

/-- Both literal endpoint markings discharge the full local catalogue. -/
theorem graph_models (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  by_cases hv : v.type = false
  · exact .linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),
      ⟨(graph_linear_four h eK v hv).some.trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2))⟩⟩
  · exact Assembly.symmetricThree_rankOne_model
      (Assembly.symmetricThree_graph_quotient h true eU v
        (by cases ht : v.type <;> simp_all)).some

/-- The complete catalogue on the literal actor images in the original group. -/
theorem original_graph_models (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) :
    IsRankOneModel ((graphLocalGroup F v).map (Reduction.G₀ ![K,U] S).subtype ⧸
      pCore 2 ((graphLocalGroup F v).map (Reduction.G₀ ![K,U] S).subtype)) := by
  let e := (graphLocalGroup F v).equivMapOfInjective
    (Reduction.G₀ ![K,U] S).subtype (Reduction.G₀ ![K,U] S).subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact (graph_models h eK eU v).of_equiv eq.symm

end CFSG.Quasithin.ChapterF.Source.MixedDGS
