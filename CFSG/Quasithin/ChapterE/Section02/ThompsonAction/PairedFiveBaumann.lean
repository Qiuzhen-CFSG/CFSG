module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Baumann
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.FullAction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveImages

/-!
# The original paired symmetric-five Baumann image

The class-sum section lifts every vector fixed by the actual Thompson image.
Its lift belongs to the central elementary part of the Thompson subgroup,
so the Baumann subgroup fixes it.  The faithful ambient action and the proved
paired pointwise-fixer theorem place the Baumann image in the same pair of
transposition four-groups.  The reverse inclusion is the genuine Thompson
containment, giving equality on the original quotient map.

Source: Aschbacher--Smith B.6.10, C.1.24 and E.2.3(3), pp.117,130--131,216--217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_thompson_baumann_of_symmetric_model
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (baumann (T : Subgroup G)).map q ∧
    ∃ a b : Equiv.Perm (Fin 5), (baumann (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
            c.action.groupEquiv.symm.toMonoidHom) := by
  exact ChapterC.SymmetricFive.Paired.thompson_baumann_of_source_model T hP U hU hJ q hq hker d c hexchange

end CFSG.Quasithin.ChapterE.ThompsonAction
