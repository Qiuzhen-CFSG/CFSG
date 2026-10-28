module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingSupport
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The simple model reduction in the deleted-five branch

The original alternating-five block has no fixed vectors in its literal
commutator layer. Its ambient center is therefore disjoint from that layer.
If the layer is self-centralizing, the center lies in it and is trivial.
The source quasisimple group is then simple, so the proved Theorem C gives
its model without changing the block, quotient or module marking.

Source: Aschbacher–Smith 13.5.15, printed p.921, applied to the image of K
in the quotient of the selected C-component by the involution subgroup D.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X]

theorem center_eq_bot (K : Subgroup X) (hK : ChapterC.IsAlternatingBlock K 5)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype) : center X = ⊥ := by
  have hd := ChapterC.Section05.ConjugateSource.alternatingModule_disjoint_of_commuting
    K (center X) hK (center_le_centralizer _)
  exact bot_unique ((le_inf ((center_le_centralizer _).trans hself) le_rfl).trans hd.le_bot)

theorem simple [IsQuasisimple X] (K : Subgroup X)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype) : IsSimpleGroup X := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  exact (((QuotientGroup.quotientMulEquivOfEq (center_eq_bot K hK hself)).trans
    QuotientGroup.quotientBot).symm).isSimpleGroup

theorem theoremC_model [Finite X] [IsQuasisimple X]
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (K : Subgroup X)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype) : ChapterA.Section02.IsTheoremCModel X := by
  let : IsSimpleGroup X := simple K hK hself
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative X) hsq.stronglyQuasithin hsq.isKGroup

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
