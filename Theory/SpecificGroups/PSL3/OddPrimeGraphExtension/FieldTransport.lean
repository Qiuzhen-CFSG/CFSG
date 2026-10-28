module

public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Field transport of the literal PSL₃ graph extension

Coefficientwise field transport commutes with inverse transpose, including
after passing from SL₃ to its central quotient. Conjugating automorphisms
by this projective equivalence therefore maps the actual inner-and-graph
join onto the corresponding join over the other field.

This supplies model transport for the order-three case of Aschbacher--Smith
E.1.14(7), printed p.214. The projective field equivalence is the existing
licensed ATLAS construction in `ExceptionalIsomorphisms/Support.lean`;
its source attribution and license are retained there.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeGraphExtension.FieldTransport
open OuterSolvable
variable {F K : Type*} [Field F] [Field K]

/-- Entrywise field transport intertwines the actual inverse-transpose actions. -/
theorem fieldEquivPSL_graph (e : F ≃+* K) (x : PSL(3,F)) :
    Atlas.fieldEquivPSL 3 e (graph F x) =
      graph K (Atlas.fieldEquivPSL 3 e x) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [graph_mk]
    change Atlas.fieldEquivPSL 3 e (QuotientGroup.mk' _ (x.transpose⁻¹)) =
      graph K (Atlas.fieldEquivPSL 3 e (QuotientGroup.mk' _ x))
    rw [Atlas.fieldEquivPSL_mk, Atlas.fieldEquivPSL_mk]
    change QuotientGroup.mk' _ (Atlas.fieldEquivSL 3 e (x.transpose⁻¹)) =
      graph K (QuotientGroup.mk (Atlas.fieldEquivSL 3 e x))
    rw [graph_mk]
    change QuotientGroup.mk' _ (Atlas.fieldEquivSL 3 e (x.transpose⁻¹)) =
      QuotientGroup.mk' _ ((Atlas.fieldEquivSL 3 e x).transpose⁻¹)
    apply congrArg (QuotientGroup.mk' _)
    rw [map_inv]
    congr 1

/-- Conjugation of automorphisms preserves the marked graph automorphism. -/
theorem congr_graph (e : F ≃+* K) :
    MulAut.congr (Atlas.fieldEquivPSL 3 e) (graph F) = graph K := by
  ext y
  obtain ⟨x, rfl⟩ := (Atlas.fieldEquivPSL 3 e).surjective y
  change Atlas.fieldEquivPSL 3 e
    (graph F ((Atlas.fieldEquivPSL 3 e).symm (Atlas.fieldEquivPSL 3 e x))) = _
  rw [MulEquiv.symm_apply_apply]
  exact fieldEquivPSL_graph e x

/-- The image is the literal inner-and-graph join over the new field. -/
theorem map_graphExtension (e : F ≃+* K) :
    (graphExtension F).map (MulAut.congr (Atlas.fieldEquivPSL 3 e)).toMonoidHom =
      graphExtension K := by
  unfold graphExtension
  rw [Subgroup.map_sup, MulAut.map_innerSubgroup_congr, MonoidHom.map_zpowers]
  change MulAut.innerSubgroup PSL(3,K) ⊔
    zpowers (MulAut.congr (Atlas.fieldEquivPSL 3 e) (graph F)) = _
  rw [congr_graph]

/-- An actual equivalence of graph extensions, with no semidirect model change. -/
noncomputable def graphExtensionEquiv (e : F ≃+* K) :
    graphExtension F ≃* graphExtension K :=
  ((MulAut.congr (Atlas.fieldEquivPSL 3 e)).subgroupMap (graphExtension F)).trans
    (MulEquiv.subgroupCongr (map_graphExtension e))

/-- The equivalence is the restriction of conjugation by projective field transport. -/
theorem graphExtensionEquiv_apply (e : F ≃+* K) (a : graphExtension F) :
    (graphExtensionEquiv e a : MulAut PSL(3,K)) =
      MulAut.congr (Atlas.fieldEquivPSL 3 e) (a : MulAut PSL(3,F)) := by rfl

end Matrix.PSL3.OddPrimeGraphExtension.FieldTransport
