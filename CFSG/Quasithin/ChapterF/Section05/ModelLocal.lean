module
public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Marks

/-!
# Literal local coordinates for the F.5 model

The standard triangle stabilizer is identified with `S₄ × S₄` through its
actual action on the two four point blocks.  The intersection with the model
vertex subgroup is the embedded `D₈ × S₄`; its first factor is the centralizer
of the displayed double transposition.  The two-core and the graph involution
are retained as literal marks for the local compatibility argument.

Source: Aschbacher--Smith F.5.3 and F.5.7, printed pp.300--303.
-/

public section

namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Theory.GroupTheory.GraphUniquenessSystem
open OmegaSixThree OrthogonalityGraph TriangleLocal

/-- The fully proved local coordinates of the literal model system. -/
noncomputable def modelLocalEquiv : modelSystem.H ≃* Four × Four := productEquiv

/-- The literal model vertex intersection and its embedded first dihedral factor. -/
noncomputable def modelLocalIntersectionEquiv :
    (modelSystem.H ⊓ modelSystem.vertexGroup : Subgroup omegaPlusSixThree) ≃* square × Four :=
  intersectionProductEquiv

/-- Membership in the original model vertex is precisely first-factor D₈
membership under the actual local coordinate map. -/
theorem modelLocal_vertex_iff (g : modelSystem.H) :
    (g : omegaPlusSixThree) ∈ modelSystem.vertexGroup ↔ (modelLocalEquiv g).1 ∈ square := by
  change g ∈ vertexLocal ↔ _
  rw [vertexLocal_eq]
  change (productEquiv g).1 ∈ square ∧ (productEquiv g).2 ∈ (⊤ : Subgroup Four) ↔ _
  simp only [Subgroup.mem_top,and_true]
  rfl

/-- The A₂ marking in the model is exactly the product of the two literal V₄ cores. -/
theorem modelLocal_core_map :
    (pCore 2 modelSystem.H).map modelLocalEquiv.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core.prod
        Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := core_map

variable {G V : Type*} [Group G] [MulAction G V] (W : System G V)

/-- The local-isomorphism field of F.5.7, using a source-side product marking.
The independent source owner constructs that marking on its actual normalizer. -/
noncomputable def localIsoOfProductMarking (e : W.H ≃* Four × Four) :
    modelSystem.H ≃* W.H := modelLocalEquiv.trans e.symm

/-- The local-vertex field of `Similarity` follows from the source-side
intersection marking, with all ambient inclusions preserved. -/
theorem localIsoOfProductMarking_vertex (e : W.H ≃* Four × Four)
    (he : ∀ h : W.H, (h : G) ∈ W.vertexGroup ↔ (e h).1 ∈ square)
    (g : modelSystem.H) :
    (g : omegaPlusSixThree) ∈ modelSystem.vertexGroup ↔
      (localIsoOfProductMarking W e g : G) ∈ W.vertexGroup := by
  rw [modelLocal_vertex_iff,he]
  change (modelLocalEquiv g).1 ∈ square ↔ (e (e.symm (modelLocalEquiv g))).1 ∈ square
  rw [e.apply_symm_apply]

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
