module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Orthogonal
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph.Quotient
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.GroupTheory.IsPerfect

/-!
# The projective graph fixed-subgroup residual of PSL₃(4)

For the specified inverse-transpose graph automorphism of the actual
quotient SL₃(4)/Z(SL₃(4)), the fixed subgroup is PSL₂(4). The two supporting
modules prove both the projective fixed-representative assertion and the
change-of-basis calculation identifying fixed SL₃ matrices with SL₂.
In characteristic two, the canonical quotient SL₂ → PSL₂ is an isomorphism.

An element of GF(4) outside the binary field supplies the parameter in
Mathlib's SL₂ transvection commutator theorem. Thus the fixed subgroup is
perfect, every two-group quotient is trivial, and its two-residual is the
whole subgroup. No group-order, simplicity, or splitting premise is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of 15.3.38, printed pp.1136–1137. This is
the projective model for the assertion O²(C_L(τ)) ≅ L₂(4); lifting the model
to the perfect four-cover uses the separately proved injectivity of the
cover residual projection.
-/

public section
namespace Matrix.PSL3Four
noncomputable section

/-- The fixed subgroup of the specified graph automorphism on PSL₃(4) is PSL₂(4). -/
def projectiveGraphFixedEquiv :
    (PSL3.OuterSolvable.graph F).fixedSubgroup ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  (GraphFixed.projectiveGraphFixedEquivSpecial F).trans
    ((GraphFixed.graphSLFixedEquivSL2 F).trans (Theory.PSL2.sl2QuotientEquiv F))

private theorem sl2Four_isPerfect : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨t, ht⟩ := exists_fieldFrobenius_ne
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (map_zero _)
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    have ht1 : t = 1 := CharTwo.sq_injective (by simpa using h)
    exact ht (by rw [ht1, map_one])
  exact ⟨Matrix.SL2.commutator_eq_top ht0 ht2⟩

/-- Perfectness of the graph fixed subgroup follows from the SL₂ transvection
commutator formula over the actual field with four elements. -/
theorem projectiveGraphFixed_isPerfect :
    Group.IsPerfect (PSL3.OuterSolvable.graph F).fixedSubgroup := by
  let := sl2Four_isPerfect
  let e := (GraphFixed.projectiveGraphFixedEquivSpecial F).trans
    (GraphFixed.graphSLFixedEquivSL2 F)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The graph fixed subgroup has no nontrivial two-group quotient. -/
theorem projectiveGraphFixed_isPPerfect :
    IsPPerfect 2 (PSL3.OuterSolvable.graph F).fixedSubgroup := by
  let := projectiveGraphFixed_isPerfect
  intro N hN h
  let := hN
  have hs : Subsingleton ((PSL3.OuterSolvable.graph F).fixedSubgroup ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ h.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The two-residual of the graph fixed subgroup of the actual PSL₃(4) quotient
is PSL₂(4), as used in Aschbacher--Smith 15.3.38. -/
def projectiveGraphResidualEquiv :
    pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F :=
  (MulEquiv.subgroupCongr
    ((pResidual_eq_top_iff 2 _).mpr projectiveGraphFixed_isPPerfect)).trans
      (Subgroup.topEquiv.trans projectiveGraphFixedEquiv)

end
end Matrix.PSL3Four
