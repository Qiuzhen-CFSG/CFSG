module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Bounds
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Reduction
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.AlternatingModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.OddModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.BenderModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.EvenRankTwoModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.SporadicModels

/-!
# The complete deleted-five model obstruction in the normal branch

The actual alternating-five module and self-centralization make the source
quasisimple group centerless. The proved Theorem C applies directly. Its
alternating, odd, Bender, even rank-two, binary-linear and sporadic families
are all excluded by the literal block marking and the bound on the ambient
Sylow subgroup. That bound follows from the full module normalizer action
and the original local subgroup of index at most two in the chosen Sylow.

This discharges the inspection of Theorem C in Aschbacher–Smith 13.5.15,
printed p.921. In the source application X is the central quotient of the
selected C-component, K is the image of the original block, and P is the
image of the original local two-subgroup. Their construction is separate;
no unproved model-classification callback occurs in this obstruction.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X] [Finite X] [IsQuasisimple X]

/-- The exact marked normalizer configuration in the source quotient is impossible. -/
theorem no_deletedFive_normalizer (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    (K P : Subgroup X) (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      (ChapterC.blockU K).map K.subtype)
    (hctrl : normalizer ((ChapterC.blockU K).map K.subtype : Set X) ≤
      normalizer (K : Set X))
    (hPN : P ≤ normalizer ((ChapterC.blockU K).map K.subtype : Set X))
    (T : Sylow 2 X) (hPT : P ≤ T) (hi : P.relIndex T ≤ 2) :
    False := by
  have hT := sylow_card_le K P hK hc hself hctrl hPN T hPT hi
  let := hK.2.1.elementary
  have hE : IsElementaryAbelian 2 ((ChapterC.blockU K).map K.subtype) :=
    IsElementaryAbelian.map K.subtype
  have hm := theoremC_model hsq K hK hself
  cases hm with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    exact not_alternating_of_alternatingFive K hK hc hn e
  | odd hm => exact not_oddModel_of_elementary_sixteen _ hE hc hm
  | bender hm => exact not_benderModel K hK hself hm
  | rank_two f hm => exact not_evenRankTwoModel K hK hc hself T hT hm
  | linear_binary n hn hm =>
    exact not_linearBinary_of_alternatingFive K hK hc T hT hn hm
  | sporadic hm => exact not_sporadicModel_of_alternatingFive K hK hc hctrl T hT hm

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
