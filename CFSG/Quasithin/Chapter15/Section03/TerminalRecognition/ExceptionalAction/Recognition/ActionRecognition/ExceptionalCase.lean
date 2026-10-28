module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Actor

/-!
# The exceptional constituent remaining after the FF exclusions

This interface separates two mathematical obligations in the last paragraph
of the proof of 15.3.1. The local exclusions must select the actual full
group Ŝ₆, identify its offender-generated subgroup with the even cover,
and prove that its binary module is irreducible of dimension six. Those
facts alone do not specify coordinates on that representation. Recognition
of the representation, including its extension across the odd coset,
remains a further obligation, using K.1.3.

From this intermediate witness we do prove the required group-theoretic
identification of the Thompson image: the even cover is perfect, and the
source residual identity forces it into the Thompson image. This does not
assert existence of the intermediate witness or of hexacode coordinates.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.1
and the final proof of 15.3.1, printed pp.99 and 1155; K.1.3, printed p.453.
-/

@[expose] public section

open Subgroup Atlas.Codes
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition

variable {H : Type*} [Group H] [Finite H]
  {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- An intermediate output of the ordinary-module exclusions. This record
has no vector equivalence or equivariance field. Its existence is a proof
obligation, distinct from the subsequent representation identification. -/
structure ExceptionalCase (d : SourceInput V) where
  actor : coreQuotient H ≃* HexAutomorphisms
  offender_image : d.offenderGroup.map actor.toMonoidHom = hexSign.ker
  irreducible : Representation.IsIrreducible d.offenderAction
  dimension : Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 6

namespace ExceptionalCase

variable {d : SourceInput V} (c : ExceptionalCase d)
include c

/-- The marked actor equivalence restricts to the actual offender group. -/
noncomputable def offenderEquiv : d.offenderGroup ≃* HexEvenAutomorphisms :=
  (d.offenderGroup.equivMapOfInjective c.actor.toMonoidHom c.actor.injective).trans
    (MulEquiv.subgroupCongr c.offender_image)

omit [Finite H] in
/-- Perfectness is transported through the actual subgroup equivalence. -/
theorem offender_perfect : Group.IsPerfect d.offenderGroup := by
  let _ : Group.IsPerfect HexEvenAutomorphisms := Representation.Hexacode.even_isPerfect
  exact Group.IsPerfect.ofSurjective (f := c.offenderEquiv.symm.toMonoidHom)
    c.offenderEquiv.symm.surjective

/-- A finite perfect group has no nontrivial two-group quotient. -/
theorem offender_twoPerfect : IsPPerfect 2 d.offenderGroup := by
  let _ := c.offender_perfect
  intro N hN hp
  let _ := hN
  have hs : Subsingleton (d.offenderGroup ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (d.offenderGroup ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The Thompson image equals the offender group in the exceptional branch. -/
theorem thompson_eq_offender : (thompsonGroup H).map coreProjection = d.offenderGroup :=
  d.thompson_image_eq_of_isPPerfect c.offender_twoPerfect

/-- The intermediate group identification already gives the desired image
of the actual Thompson subgroup; compatible vector coordinates remain. -/
theorem thompson_image :
    ((thompsonGroup H).map coreProjection).map c.actor.toMonoidHom = hexSign.ker := by
  rw [c.thompson_eq_offender, c.offender_image]

end ExceptionalCase

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
