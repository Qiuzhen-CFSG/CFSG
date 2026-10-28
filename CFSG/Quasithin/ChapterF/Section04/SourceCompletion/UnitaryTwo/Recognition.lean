module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.PointFaithfulness
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.EndpointAlignment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.NativePerfect
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ModelPointGraph
public import Theory.Combinatorics.PerfectGraphActionComparison

/-!
# U₄(2) recognition with the actual marked parabolic ranges

For an original faithful completion of order 25920, its plane-coset graph
and the native model graph are both SRG(27,10,1,5). Their faithful action
images agree in the graph automorphism group: the native image is perfect,
and the full automorphism group has order at most 51840. This gives an
equivariant group isomorphism. Aligning a standard incident flag then
identifies both original endpoint ranges with the native parabolics.

These are the U₄(2) cardinality-recognition and quasiequivalence conclusions
used in Aschbacher–Smith F.4.24 and F.4.44, printed pp.287 and293. The group
order is the earlier source input supplied by F.4.43. No extra geometry,
perfectness, action or endpoint-matching premise is assumed.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open GreenBook.LieModels.UnitaryFour
open Theory.Combinatorics
local notation "h1" => (Nat.le_refl 1)
namespace Completion
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- Recognition preserves the actual point action through a graph marking. -/
theorem exists_equivariant_native (hc : Nat.card G = 25920) :
    ∃ (q : c.pointGraph ≃g modelCompletion.pointGraph)
      (e : G ≃* ProjectiveGroup 1 h1), ∀ g x, e g • q x = q (g • x) := by
  have : Group.IsPerfect (ProjectiveGroup 1 h1) := native_projective_perfect
  exact PerfectGraphActionComparison.equivariant_of_srg
    (c.pointGraph_isSRG hc)
    (modelCompletion.pointGraph_isSRG BinaryCompletion.projective_card)
    (MulAction.toPermHom G c.Point)
    (MulAction.toPermHom (ProjectiveGroup 1 h1) modelCompletion.Point)
    (fun g x y => c.pointGraphAction.adj_iff g)
    (fun g x y => modelCompletion.pointGraphAction.adj_iff g)
    (c.point_action_injective hc)
    (modelCompletion.point_action_injective BinaryCompletion.projective_card)
    hc BinaryCompletion.projective_card

/-- The U₄(2) recognition with both endpoint ranges, as required by the source's
quasiequivalence conclusion. Pointwise equality of the endpoint injections is
neither asserted nor needed. -/
theorem exists_range_preserving_equiv (hc : Nat.card G = 25920) :
    ∃ e : G ≃* ProjectiveGroup 1 h1,
      c.left.range.map e.toMonoidHom = modelCompletion.left.range ∧
      c.right.range.map e.toMonoidHom = modelCompletion.right.range := by
  obtain ⟨q, e, he⟩ := c.exists_equivariant_native hc
  exact c.exists_range_aligned modelCompletion BinaryCompletion.projective_card q e he

/-- Literal parabolic formulation for the original F.4.24/F.4.44 consumers. -/
theorem exists_parabolic_preserving_equiv (hc : Nat.card G = 25920) :
    ∃ e : G ≃* ProjectiveGroup 1 h1,
      c.left.range.map e.toMonoidHom = pointParabolic 1 h1 ∧
      c.right.range.map e.toMonoidHom = planeParabolic 1 h1 := by
  obtain ⟨e, hl, hr⟩ := c.exists_range_preserving_equiv hc
  refine ⟨e, ?_, ?_⟩
  · exact hl.trans (Subgroup.range_subtype _)
  · exact hr.trans (Subgroup.range_subtype _)

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
