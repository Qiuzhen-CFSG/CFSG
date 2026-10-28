module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LocalGeometry

/-!
# Assembly of a marked Conway embedding from the local Leech action

The SL₃ blocks, short-root family and graph reflection generate the actual
split-octonion group by `OctonionLocals.generators_generate`. For a faithful
Leech action with the same generator formulas, taking generated images gives
an equivalence from that octonion group to the literal subgroup of the Conway
quotient. The specified conjugator then sends C(1) exactly to
`markedInvolution`.

This is the comparison and marking step of Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, printed pp.283–284/PDF147–148, used in
Aschbacher–Smith I.2.2(5), printed p.411/PDF422. The required
`CoordinateGeometry` has not been constructed. Thus the existential theorem
here is conditional and does not yet establish the source embedding.

The root `ConwayRootFour` module is deliberately not imported, so it may
later consume the completed embedding without a cycle.
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding
open OctonionLocals

namespace CoordinateGeometry
variable (D : CoordinateGeometry)

/-- The three generator formulas identify the full action images. -/
theorem range_eq : D.representation.range = (action (F := F)).range := by
  rw [MonoidHom.range_eq_map D.representation, ← localGeneratorIn_generate D.long D.short D.swap,
    MonoidHom.map_closure, ← Set.range_comp']
  simp_rw [D.on_generators]
  rw [Set.range_comp', ← MonoidHom.map_closure, generators_generate, ← MonoidHom.range_eq_map]

/-- Faithful actions with these generated images give an actual group equivalence. -/
noncomputable def comparison : FiniteCover.FourBase ≃* localGroup D.long D.short D.swap :=
  (MonoidHom.ofInjective action_four_injective).trans
    ((MulEquiv.subgroupCongr D.range_eq.symm).trans (MonoidHom.ofInjective D.faithful).symm)

theorem comparison_action (g : FiniteCover.FourBase) :
    D.representation (D.comparison g) = action g := by
  exact MonoidHom.apply_ofInjective_symm D.faithful _

/-- The induced homomorphism into the literal Leech central quotient. -/
noncomputable def hom : FiniteCover.FourBase →* LeechCentralQuotient :=
  (localGroup D.long D.short D.swap).subtype.comp D.comparison.toMonoidHom

theorem hom_injective : Function.Injective D.hom :=
  Subtype.val_injective.comp D.comparison.injective

theorem hom_generator (i : Generator F) : D.hom (generator i) =
    localGenerator D.long D.short D.swap i := by
  have h : D.comparison (generator i) = localGeneratorIn D.long D.short D.swap i := by
    apply D.faithful
    rw [D.comparison_action, D.on_generators]
  exact congrArg Subtype.val h

theorem hom_rootC (a : F) : D.hom (rootC a) = D.short a :=
  D.hom_generator (Sum.inl (Sum.inr a))

/-- Conditional assembly: a constructed local geometry supplies the exact marking. -/
theorem exists_marked_embedding (D : CoordinateGeometry) :
    ∃ f : FiniteCover.FourBase →* LeechCentralQuotient,
      Function.Injective f ∧ f (rootC 1) = markedInvolution := by
  obtain ⟨a, ha⟩ := isConj_iff.mp D.marked
  refine ⟨(MulAut.conj a).toMonoidHom.comp D.hom,
    (MulAut.conj a).injective.comp D.hom_injective, ?_⟩
  change MulAut.conj a (D.hom (rootC 1)) = markedInvolution
  rw [D.hom_rootC]
  exact ha

end CoordinateGeometry
end Atlas.G2.ConwayRootFour.Embedding
