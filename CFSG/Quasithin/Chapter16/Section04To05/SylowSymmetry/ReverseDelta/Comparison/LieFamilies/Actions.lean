module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport

/-!
# The two model actions in the Lie-family comparison

One specified model of L/Z(L) also identifies the quotient of its conjugate.
The two induced actions have order two; the first is inner and the second
outer. Their fixed two-residuals are the actual central images provided by
`Comparison.Transport`. Solvability passes through both central kernels and
through the actual residual containment; their two images need not be
isomorphic.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 16.4.11(2), printed p.1193, and the tables 16.1.2--4, pp.1170--1171.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory LiePreliminaries

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
variable {S : Type*} [Group S]

/-- Transport the chosen quotient model along actual ambient conjugation. -/
noncomputable def conjugateModel (e : (L ⧸ center L) ≃* S) :
    ((L.conjBy g) ⧸ center (L.conjBy g)) ≃* S :=
  (centralQuotientCongr ((MulAut.conj g).subgroupMap L)).symm.trans e

/-- The inner action on the specified quotient model. -/
noncomputable def innerAction (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : MulAut S :=
  MulAut.centralQuotientAction e
    (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem)))

/-- The outer action on that same model, through the conjugate component. -/
noncomputable def outerAction (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : MulAut S :=
  MulAut.centralQuotientAction (conjugateModel e) (action d.z_normalizes)

theorem innerAction_order (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : orderOf (innerAction d e) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact (MulAut.orderOf_centralQuotientAction e _).trans d.inner_action_order

theorem outerAction_order (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : orderOf (outerAction d e) = 2 := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsQuasisimple (L.conjBy g) :=
    IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  exact (MulAut.orderOf_centralQuotientAction (conjugateModel e) _).trans
    d.outer_action_order

theorem innerAction_inner (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : ∃ s : S, innerAction d e = MulAut.conj s := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact (MulAut.centralQuotientAction_inner_iff e _).mpr d.inner_action

theorem outerAction_outer (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) : ¬ ∃ s : S, outerAction d e = MulAut.conj s := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsQuasisimple (L.conjBy g) :=
    IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  exact fun h => d.outer_action
    ((MulAut.centralQuotientAction_inner_iff (conjugateModel e) _).mp h)

/-- The inner image retains the actual central quotient map. -/
noncomputable def innerResidualEquiv (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) :
    centralImage L (residual L r) ≃* pResidual 2 (innerAction d e).fixedSubgroup := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  exact centralImageModelEquiv (component_oddCore d) e _

/-- The outer image uses the conjugate component's own central kernel. -/
noncomputable def outerResidualEquiv (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S) :
    centralImage (L.conjBy g) (residual (L.conjBy g) z) ≃*
      pResidual 2 (outerAction d e).fixedSubgroup := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsQuasisimple (L.conjBy g) :=
    IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  exact centralImageModelEquiv (conjugate_oddCore d) (conjugateModel e) _

/-- Solvable inner fixed points cannot contain a nonsolvable outer residual.
Only containment is needed in this case; the stronger relative normality
remains available for the other Lie rows. -/
theorem false_of_solvable_inner_nonsolvable_outer (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* S)
    (hi : Group.IsSolvable (innerAction d e).fixedSubgroup)
    (ho : ¬ Group.IsSolvable (pResidual 2 (outerAction d e).fixedSubgroup)) : False := by
  let := hi
  have hs : Group.IsSolvable (centralImage L (residual L r)) :=
    Group.isSolvable_of_surjective
      (f := (innerResidualEquiv d e).symm.toMonoidHom)
      (innerResidualEquiv d e).symm.surjective
  let : Group.IsSolvable (residual L r) :=
    (centralImage_solvable_iff ((residual_le L r).trans inf_le_left)).mp hs
  let : Group.IsSolvable (residual (L.conjBy g) z) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective d.residual_normal.1)
  let : Group.IsSolvable (centralImage (L.conjBy g) (residual (L.conjBy g) z)) :=
    (centralImage_solvable_iff
      ((residual_le (L.conjBy g) z).trans inf_le_left)).mpr inferInstance
  exact ho (Group.isSolvable_of_surjective
    (f := (outerResidualEquiv d e).toMonoidHom) (outerResidualEquiv d e).surjective)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
