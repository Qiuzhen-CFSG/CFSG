module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Baumann
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Source

/-!
# The original E.2.3 paired symmetric-five Thompson image

The source pair and its actual Sylow exchanger give both transposition
four-groups in the image of the original Thompson subgroup. The literal
quotient embedding is retained, and the source marked-product construction
discharges the module comparison and factor activation hypotheses.

Source: Aschbacher–Smith E.2.3(3), pp.216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem paired_thompson_of_symmetric_model
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    ∃ a b : Equiv.Perm (Fin 5), (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
            c.action.groupEquiv.symm.toMonoidHom) := by
  exact ChapterC.SymmetricFive.Paired.thompson_of_source_model T U hU hJ q hq hker d c hexchange

end CFSG.Quasithin.ChapterE.ThompsonAction
