module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Reduction
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Subgroups fixing a projective point or dual point

Conjugate a fixed projective point to the first coordinate line using the
transitive SL₃ action. This gives an actual injection of the full SL₃ preimage
into the point parabolic. Its scalar kernel is abelian, and projection is
surjective onto the original subgroup. Applying the same argument after the
contragredient automorphism deals with a fixed dual point.

Source: the geometric alternative in GLS3, Theorem 6.5.3(a),
`refs/KGroup/GLS3/chapter6.tex`. No subgroup classification is used.
-/

open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

-- Select the standard action in the presence of inherited Huppert instances.
attribute [local instance] Matrix.instDistribMulActionSpecialLinearGroupForall
  Matrix.instSMulCommClassSpecialLinearGroupForall

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [Finite F]

omit [Finite F] in
private theorem axis_ne_zero : (![1,0,0] : Fin 3 → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

private def axisPoint : ℙ F (Fin 3 → F) :=
  Projectivization.mk F ![1,0,0] (axis_ne_zero F)

private theorem mem_pointParabolicSL_of_fix_axis (g : SL(3,F))
    (hg : g • axisPoint F = axisPoint F) : g ∈ pointParabolicSL F := by
  change g • Projectivization.mk F ![1,0,0] (axis_ne_zero F) =
    Projectivization.mk F ![1,0,0] (axis_ne_zero F) at hg
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨a,ha⟩ := hg
  change a • (![1,0,0] : Fin 3 → F) = g.val.mulVec ![1,0,0] at ha
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  rw [mem_pointParabolicSL_iff]
  constructor
  · simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three] using h1.symm
  · simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three] using h2.symm

private def parabolicKernelToCenter :
    ((projection F).subgroupMap (pointParabolicSL F)).ker →*
      Subgroup.center SL(3,F) :=
  (((pointParabolicSL F).subtype).comp
    ((projection F).subgroupMap (pointParabolicSL F)).ker.subtype).codRestrict
    (Subgroup.center SL(3,F)) (by
      intro g
      have h : g.val.val ∈ (projection F).ker := congrArg Subtype.val g.property
      change g.val.val ∈ Subgroup.center SL(3,F)
      simpa only [projection_ker] using h)

/-- The scalar cover of the point parabolic belongs to the same envelope. -/
public theorem pointParabolicSL_envelope (f : ℕ) : Envelope f (pointParabolicSL F) := by
  let : Group.IsSolvable (Subgroup.center SL(3,F)) :=
    Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  let : Group.IsSolvable ((projection F).subgroupMap (pointParabolicSL F)).ker :=
    Group.isSolvable_of_isSolvable_injective (f := parabolicKernelToCenter F) (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.center SL(3,F) => z.val) h)
  exact Envelope.of_solvable_kernel ((projection F).subgroupMap (pointParabolicSL F))
    (.pointParabolic F)

/-- A fixed projective point after an actual SL₃ automorphism gives a parabolic envelope. -/
public theorem envelope_of_projective_fixed_point (f : ℕ) (U : Subgroup PSL(3,F))
    (e : SL(3,F) ≃* SL(3,F)) (p : ℙ F (Fin 3 → F))
    (hp : ∀ g ∈ U.comap (projection F), e g • p = p) : Envelope f U := by
  let : MulAction.IsPretransitive SL(3,F) (ℙ F (Fin 3 → F)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨s,hs⟩ := MulAction.exists_smul_eq SL(3,F) p (axisPoint F)
  let c : SL(3,F) ≃* SL(3,F) := e.trans (MulAut.conj s)
  let i : U.comap (projection F) →* pointParabolicSL F :=
    (c.toMonoidHom.comp (U.comap (projection F)).subtype).codRestrict
      (pointParabolicSL F) (by
        intro g
        apply mem_pointParabolicSL_of_fix_axis
        change (s * e g * s⁻¹) • axisPoint F = axisPoint F
        rw [← hs]
        simpa only [mul_smul, inv_smul_smul] using congrArg (fun x => s • x) (hp g g.property))
  have hi : Function.Injective i := by
    intro a b h
    exact Subtype.ext (c.injective (congrArg Subtype.val h))
  have hen : Envelope f (U.comap (projection F)) :=
    .subgroup i hi (pointParabolicSL_envelope F f)
  let q : U.comap (projection F) →* U :=
    ((projection F).comp (U.comap (projection F)).subtype).codRestrict U (by
      intro g
      exact g.property)
  apply Envelope.quotient q _ hen
  intro u
  obtain ⟨g,hg⟩ := projection_surjective F u
  refine ⟨⟨g, ?_⟩, ?_⟩
  · change projection F g ∈ U
    rw [hg]
    exact u.property
  · exact Subtype.ext hg

/-- A fixed point of the natural projective action or its contragredient.
The preimage is taken under the actual scalar quotient SL₃ → PSL₃. -/
@[expose] public def FixesPointOrDual (U : Subgroup PSL(3,F)) : Prop :=
  (∃ p : ℙ F (Fin 3 → F), ∀ g ∈ U.comap (projection F), g • p = p) ∨
  (∃ p : ℙ F (Fin 3 → F), ∀ g ∈ U.comap (projection F),
    flagDuality F g • p = p)

/-- Both geometric fixed-point cases have envelopes without field restrictions. -/
public theorem envelope_of_fixesPointOrDual (f : ℕ) (U : Subgroup PSL(3,F))
    (hU : FixesPointOrDual F U) : Envelope f U := by
  rcases hU with ⟨p,hp⟩ | ⟨p,hp⟩
  · exact envelope_of_projective_fixed_point F f U (MulEquiv.refl _) p hp
  · exact envelope_of_projective_fixed_point F f U (flagDuality F) p hp

end CFSG.Quasithin.MainConverse.LinearThreeSections
