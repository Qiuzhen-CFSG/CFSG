module

public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.Alternating.proposition_5_2_4

/-!
# Involution fusion in A₅

Every involution in A₅ has cycle type (2,2). The general alternating-group
involution conjugacy theorem supplies an even conjugator. This structural
argument uses no enumeration of A₅ and retains actual conjugacy in A₅.

Source application: the A₅ component of the root-four normalizer in
Aschbacher, *Sporadic Groups* (1994), 47.1 and 47.5, printed pp.259–263.
-/

open Equiv.Perm
namespace alternatingGroup
/-- The double transpositions form one conjugacy class inside A₅. -/
public theorem five_involutions_isConj (a b : alternatingGroup (Fin 5)) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  apply GLS3.Chapter5.SchurPresentation.alternating_involution_isConj_of_card_support_eq
    (congrArg Subtype.val ha2) (congrArg Subtype.val hb2)
  · intro h
    simp [h] at ha
  · rw [← sum_cycleType, ← sum_cycleType,
      involution_cycleType_of_degree_le_six (by decide) a ha,
      involution_cycleType_of_degree_le_six (by decide) b hb]
end alternatingGroup
