module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceTransport
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers

/-!
# The H.9.1 stabilizers in the original source group

The source comparison restricts to actual point stabilizers and their
embedded two-residuals. It therefore transports the proved pure-vector
parabolic and nonsingular automorphism-group identifications. The invariant
and moving modules use the original representation and the original residual.
The complementary actions remain marked by the constructed natural and dual
coordinates, so both their inclusions and their action formulas are retained.

Source: Aschbacher–Smith H.9.1(3–4), printed pp.389–390, with the corrected
nonsingular statement independent of the pure-vector Sylow marking.
-/

public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- The source point centralizer is identified by the restricted ambient map. -/
noncomputable def stabilizerEquiv (v : V) : S.stabilizer v ≃*
    fullStabilizer (AutomorphismModel.coordinateAction S.degree) (S.model.coordinates v) :=
  Transport.stabilizerEquiv S.representation _ S.model.group S.model.coordinates
    S.model.equivariant v

/-- The stabilizer comparison is the restriction of the constructed ambient map. -/
@[simp] theorem stabilizerEquiv_apply (v : V) (g : S.stabilizer v) :
    (S.stabilizerEquiv v g).val = S.model.group g :=
  Transport.stabilizerEquiv_apply S.representation _ S.model.group S.model.coordinates
    S.model.equivariant v g

/-- The source residual is identified using its actual embedding. -/
noncomputable def residualEquiv (v : V) : S.residual v ≃*
    innerResidual (AutomorphismModel.coordinateAction S.degree) (S.model.coordinates v) :=
  ((S.residual v).equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective).trans
    (MulEquiv.subgroupCongr (S.residual_map v))

/-- The nonsingular source residual and full stabilizer are respectively
L_(n−1)(2) and its full automorphism group. The fixed and moving modules
are identified by the original marked comparison. -/
theorem nonsingular_structure {v : V} (hv : S.quadratic v = 1) :
    S.residual v = S.innerStabilizer v ∧
    Nonempty (S.residual v ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) ∧
    Nonempty (S.stabilizer v ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2))) ∧
    (S.fixed (S.residual v)).map S.model.coordinates.toLinearMap =
      (Submodule.span (ZMod 2) {(S.model.coordinates v).1}).prod
        (Submodule.span (ZMod 2) {(S.model.coordinates v).2}) ∧
    (S.moving v).map S.model.coordinates.toLinearMap =
      AdaptedPair.movingSpace (S.model.coordinates v) := by
  have hv' : (S.model.coordinates v).2 (S.model.coordinates v).1 = 1 := by
    simpa only [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv
  let d := AutomorphismModel.coordinateAction S.degree
  refine ⟨S.residual_eq_innerStabilizer hv, ?_, ?_, ?_, S.moving_map_nonsingular hv⟩
  · exact ⟨(S.residualEquiv v).trans
      ((MulEquiv.subgroupCongr (innerResidual_eq_innerStabilizer S.degree d hv')).trans
        (innerStabilizerEquivProjective S.degree d hv'))⟩
  · exact ⟨(S.stabilizerEquiv v).trans (fullStabilizerEquivAutProjective S.degree d hv')⟩
  · rw [S.fixed_map, S.residual_map]
    exact residual_invariants S.degree d hv'

/-- The same source residual acts as the full natural group on the first
orthogonal complement and dually on the second. All equations use the
original representation before applying the constructed coordinates. -/
theorem nonsingular_complement_actions {v : V} (hv : S.quadratic v = 1) :
    let x := (S.model.coordinates v).1
    let f := (S.model.coordinates v).2
    IsCompl (Submodule.span (ZMod 2) {x}) f.ker ∧
    IsCompl (Submodule.span (ZMod 2) {f}) (annihilator x) ∧
    Module.finrank (ZMod 2) f.ker = n - 1 ∧
    Module.finrank (ZMod 2) (annihilator x) = n - 1 ∧
    ∃ (h : f x = 1) (e : S.residual v ≃* BinaryLinear.GL f.ker),
      (∀ (a : S.residual v) (w : f.ker),
        S.model.coordinates (S.representation a.val (S.model.coordinates.symm (w.val,0))) =
          ((e a w).val,0)) ∧
      (∀ (a : S.residual v) (q : annihilator x),
        S.model.coordinates (S.representation a.val (S.model.coordinates.symm (0,q.val))) =
          (0,((annihilatorEquivKernelDual h).symm
            ((e a).symm.dualMap (annihilatorEquivKernelDual h q))).val)) := by
  have h : (S.model.coordinates v).2 (S.model.coordinates v).1 = 1 := by
    simpa only [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv
  let d := AutomorphismModel.coordinateAction S.degree
  obtain ⟨hd₁,hd₂,_⟩ := NaturalDual.nonsingular_complement_actions S.degree d h
  refine ⟨line_isCompl_kernel h, dual_line_isCompl_annihilator h, hd₁, hd₂,
    h, (S.residualEquiv v).trans (residualEquivKernel S.degree d h), ?_, ?_⟩
  · intro a w
    rw [S.model.equivariant, S.model.coordinates.apply_symm_apply]
    exact residual_kernel_action S.degree d h (S.residualEquiv v a) w
  · intro a q
    rw [S.model.equivariant, S.model.coordinates.apply_symm_apply]
    exact residual_dual_action S.degree d h (S.residualEquiv v a) q

/-- A pure nonzero source vector has no outer stabilizer and its whole
stabilizer is exactly its embedded two-residual. -/
theorem pure_stabilizer_eq_residual (u : S.natural) (hu : (u : V) ≠ 0) :
    S.stabilizer u = S.residual u ∧ S.stabilizer u ≤ componentLayer M := by
  have hx : S.naturalCoordinates u ≠ 0 := by
    intro h
    have hz : u = 0 := S.naturalCoordinates.injective (h.trans (map_zero _).symm)
    exact hu (congrArg Subtype.val hz)
  constructor
  · apply Subgroup.map_injective (f := S.model.group.toMonoidHom) S.model.group.injective
    rw [S.stabilizer_map, S.residual_map, S.model.natural_marking]
    exact Pure.fullStabilizer_eq_innerResidual S.degree _ hx
  · intro g hg
    apply (S.model.inner_iff g).mp
    apply pure_fullStabilizer_le_inner S.degree (AutomorphismModel.coordinateAction S.degree) hx
    have hm := Subgroup.mem_map_of_mem S.model.group.toMonoidHom hg
    rw [S.stabilizer_map, S.model.natural_marking] at hm
    exact hm

/-- The source pure stabilizer is the actual elementary split extension.
The equivalence includes its complete natural and dual point-stabilizer
representation through `model.equivariant` and `model.natural_marking`. -/
theorem pure_split_extension (u : S.natural) (hu : (u : V) ≠ 0) :
    ∃ h : S.naturalCoordinates u ≠ 0,
      Nonempty (SemidirectProduct
        (Pure.innerRadical (AutomorphismModel.coordinateAction S.degree) (S.naturalCoordinates u))
        (BinaryLinear.GL (Pure.pointQuotient (S.naturalCoordinates u)))
        (Pure.splitAction (AutomorphismModel.coordinateAction S.degree) h) ≃* S.stabilizer u) ∧
      IsElementaryAbelian 2
        (Pure.innerRadical (AutomorphismModel.coordinateAction S.degree) (S.naturalCoordinates u)) ∧
      Nat.card (Pure.innerRadical (AutomorphismModel.coordinateAction S.degree)
        (S.naturalCoordinates u)) = 2 ^ (n - 1) := by
  have h : S.naturalCoordinates u ≠ 0 := by
    intro h
    have hz : u = 0 := S.naturalCoordinates.injective (h.trans (map_zero _).symm)
    exact hu (congrArg Subtype.val hz)
  let d := AutomorphismModel.coordinateAction S.degree
  let c := (S.stabilizerEquiv u).trans
    (MulEquiv.subgroupCongr (congrArg (fullStabilizer d) (S.model.natural_marking u)))
  refine ⟨h, ⟨(Pure.fullSemidirectEquiv S.degree d h).trans c.symm⟩, ?_, ?_⟩
  · exact Pure.innerRadical_elementary d (S.naturalCoordinates u)
  · exact Pure.innerRadical_card d h

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
