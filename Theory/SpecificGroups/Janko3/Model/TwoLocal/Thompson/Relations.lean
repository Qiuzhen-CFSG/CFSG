module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations0
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations1
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations2
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations3
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations4
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations5
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations6
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations7
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations8
import Mathlib.Tactic.FinCases

/-!
# The certified collection relations for the J₃ order-1152 subgroup

The preceding files check power and conjugation relations of the actual model
generators. Here they are assembled into finite families for the normal-form
argument. Source: GLS 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate
public theorem power_relation (k : Fin 9) :
    gen k.val ^ radix k.val = representative k.val (powerIndex k.val) := by
  fin_cases k
  · exact power_relation_0
  · exact power_relation_1
  · exact power_relation_2
  · exact power_relation_3
  · exact power_relation_4
  · exact power_relation_5
  · exact power_relation_6
  · exact power_relation_7
  · exact power_relation_8

public theorem conjugate_relation (k : Fin 9) (i : Fin k.val) :
    gen k.val * gen i.val * (gen k.val)⁻¹ =
    representative (conjugateDepth k.val i.val) (conjugateIndex k.val i.val) := by
  fin_cases k
  · exact conjugate_relation_0 i
  · exact conjugate_relation_1 i
  · exact conjugate_relation_2 i
  · exact conjugate_relation_3 i
  · exact conjugate_relation_4 i
  · exact conjugate_relation_5 i
  · exact conjugate_relation_6 i
  · exact conjugate_relation_7 i
  · exact conjugate_relation_8 i

public theorem inverse_conjugate_relation (k : Fin 9) (i : Fin k.val) :
    (gen k.val)⁻¹ * gen i.val * gen k.val =
    representative (conjugateDepth k.val i.val) (inverseConjugateIndex k.val i.val) := by
  fin_cases k
  · exact inverse_conjugate_relation_0 i
  · exact inverse_conjugate_relation_1 i
  · exact inverse_conjugate_relation_2 i
  · exact inverse_conjugate_relation_3 i
  · exact inverse_conjugate_relation_4 i
  · exact inverse_conjugate_relation_5 i
  · exact inverse_conjugate_relation_6 i
  · exact inverse_conjugate_relation_7 i
  · exact inverse_conjugate_relation_8 i

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
