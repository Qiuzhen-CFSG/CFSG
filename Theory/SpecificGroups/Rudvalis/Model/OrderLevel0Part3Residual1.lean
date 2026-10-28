module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Check7

import Mathlib.Tactic.FinCases

/-!
# Rudvalis part 3, residual transitions 68--135

The checked composition trees evaluate both sides of each fixed forward transition.
Their root tables coincide, giving the original permutation identities.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

private theorem ofWords (i : Fin 2) (r : Fin 4060)
    (u v w : List (Fin 4))
    (hu : L0RepWord r = u)
    (hv : L0RepWord (L0Act (i.castLE (by decide)) r) = v)
    (hw : L0Factor (i.castLE (by decide)) r = w)
    (h : ∀ x, Part6Tables.gen0 (i.castLE (by decide)) (Part6Tables.eval Part6Tables.gen0 u x) =
      Part6Tables.eval Part6Tables.gen0 v (Part6Tables.eval Part6Tables.gen1 w x)) :
    stepCheck i r := by
  have ht : Part6Tables.check i r = true := by
    apply (checkFin_spec _).mpr
    intro x
    simp only [hu, hv, hw, decide_eq_true_eq]
    exact h x
  right
  apply (checkFin_spec _).mpr
  intro x
  simpa only [decide_eq_true_eq] using
    congrArg (fun p : Equiv.Perm (Fin 4060) => p x) (Part6Tables.ofCheck i r ht)

set_option maxHeartbeats 1600000 in
private theorem point68 : stepCheck 1 2027 := by
  apply ofWords 1 2027 [1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3] [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1] [1, 2, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map229 x = map235 x := rfl
    simp only [node235, node234, node233, node232, node231, node230, node229, node228, node158, node157, node116, node115, node80, node72, node65, node52, node48, node42, node35, node33, node31, node28, node27, node26, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point69 : stepCheck 1 2032 := by
  apply ofWords 1 2032 [0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3] [0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1] [3, 0, 3, 2, 1, 1, 0, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map237 x = map243 x := rfl
    simp only [node243, node242, node241, node240, node239, node238, node237, node236, node160, node159, node131, node105, node97, node96, node85, node74, node58, node57, node56, node53, node51, node49, node44, node33, node32, node30, node29, node28, node25, node22, node19, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point70 : stepCheck 1 2038 := by
  apply ofWords 1 2038 [0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3] [0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [3, 0, 1, 0, 1, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map244 x = map248 x := rfl
    simp only [node248, node247, node246, node245, node244, node162, node161, node134, node133, node132, node117, node116, node107, node106, node98, node81, node69, node65, node58, node56, node49, node42, node40, node35, node32, node31, node30, node28, node27, node26, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point71 : stepCheck 1 2039 := by
  apply ofWords 1 2039 [1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3] [0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0] [2, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map250 x = map256 x := rfl
    simp only [node256, node255, node254, node253, node252, node251, node250, node249, node163, node135, node132, node99, node97, node82, node81, node58, node56, node48, node42, node40, node35, node34, node32, node31, node30, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point72 : stepCheck 0 2164 := by
  apply ofWords 0 2164 [3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map257 x = map261 x := rfl
    simp only [node261, node260, node259, node258, node257, node166, node165, node164, node157, node135, node83, node75, node74, node72, node70, node67, node63, node62, node60, node55, node54, node52, node51, node44, node42, node31, node30, node29, node27, node26, node25, node24, node23, node21, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point73 : stepCheck 0 2166 := by
  apply ofWords 0 2166 [1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3] [0, 3, 0, 3, 2, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map263 x = map269 x := rfl
    simp only [node269, node268, node267, node266, node265, node264, node263, node262, node169, node168, node167, node160, node136, node131, node100, node86, node81, node75, node70, node67, node66, node65, node63, node62, node60, node55, node54, node52, node51, node44, node42, node35, node33, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point74 : stepCheck 0 2168 := by
  apply ofWords 0 2168 [1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] [0, 1, 1, 0, 0, 1, 0, 3, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map270 x = map277 x := rfl
    simp only [node277, node276, node275, node274, node273, node272, node271, node270, node172, node171, node170, node137, node118, node101, node97, node90, node89, node88, node87, node74, node68, node64, node58, node57, node54, node53, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point75 : stepCheck 0 2169 := by
  apply ofWords 0 2169 [3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0] [0, 0, 1, 2, 3, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map278 x = map285 x := rfl
    simp only [node285, node284, node283, node282, node281, node280, node279, node278, node177, node176, node175, node174, node173, node105, node102, node91, node74, node59, node55, node53, node51, node48, node44, node34, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point76 : stepCheck 0 2173 := by
  apply ofWords 0 2173 [1, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0] [0, 3, 2, 1, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map286 x = map293 x := rfl
    simp only [node293, node292, node291, node290, node289, node288, node287, node286, node179, node178, node119, node118, node108, node101, node99, node86, node83, node77, node76, node73, node57, node53, node50, node49, node48, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point77 : stepCheck 0 2179 := by
  apply ofWords 0 2179 [1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1, 0, 1, 1, 0, 3, 0, 1, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map294 x = map302 x := rfl
    simp only [node302, node301, node300, node299, node298, node297, node296, node295, node294, node181, node180, node109, node87, node76, node72, node70, node67, node65, node63, node62, node60, node55, node54, node52, node51, node44, node42, node35, node33, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point78 : stepCheck 1 2163 := by
  apply ofWords 1 2163 [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 3] [1, 0, 0, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map303 x = map311 x := rfl
    simp only [node311, node310, node309, node308, node307, node306, node305, node304, node303, node184, node183, node182, node139, node138, node110, node102, node91, node78, node77, node74, node73, node57, node53, node50, node49, node47, node46, node45, node43, node42, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point79 : stepCheck 1 2167 := by
  apply ofWords 1 2167 [0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map312 x = map314 x := rfl
    simp only [node314, node313, node312, node185, node120, node106, node84, node74, node61, node49, node28, node22, node19, node15, node12] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4] using h

set_option maxHeartbeats 1600000 in
private theorem point80 : stepCheck 1 2173 := by
  apply ofWords 1 2173 [1, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0] [3, 0, 3, 0, 1, 0, 1, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map315 x = map323 x := rfl
    simp only [node323, node322, node321, node320, node319, node318, node317, node316, node315, node187, node186, node178, node121, node116, node110, node100, node66, node65, node59, node57, node53, node49, node48, node35, node34, node31, node30, node28, node26, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point81 : stepCheck 1 2175 := by
  apply ofWords 1 2175 [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 3] [0, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map324 x = map332 x := rfl
    simp only [node332, node331, node330, node329, node328, node327, node326, node325, node324, node189, node188, node140, node122, node81, node80, node78, node77, node73, node56, node53, node52, node50, node49, node47, node46, node45, node44, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node21, node20, node19, node18, node17, node16, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point82 : stepCheck 0 2300 := by
  apply ofWords 0 2300 [1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0] [1, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0] [1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map333 x = map338 x := rfl
    simp only [node338, node337, node336, node335, node334, node333, node190, node162, node139, node134, node133, node120, node116, node103, node98, node92, node79, node76, node69, node68, node65, node64, node58, node35, node32, node31, node30, node28, node26, node24, node23, node22, node21, node20, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point83 : stepCheck 0 2303 := by
  apply ofWords 0 2303 [3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0] [3, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1] [0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map340 x = map343 x := rfl
    simp only [node343, node342, node341, node340, node339, node121, node104, node103, node61, node59, node48, node22, node15, node12] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4] using h

set_option maxHeartbeats 1600000 in
private theorem point84 : stepCheck 0 2307 := by
  apply ofWords 0 2307 [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] [3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3] [0, 1, 2, 1, 1, 2, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map345 x = map353 x := rfl
    simp only [node353, node352, node351, node350, node349, node348, node347, node346, node345, node344, node191, node123, node107, node93, node91, node90, node89, node81, node79, node78, node69, node65, node59, node58, node49, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point85 : stepCheck 0 2309 := by
  apply ofWords 0 2309 [1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0] [1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 1] [2, 1, 0, 0, 3, 2, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map354 x = map361 x := rfl
    simp only [node361, node360, node359, node358, node357, node356, node355, node354, node194, node193, node192, node142, node141, node137, node108, node99, node92, node76, node69, node64, node58, node50, node48, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point86 : stepCheck 1 2305 := by
  apply ofWords 1 2305 [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0] [3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3] [1, 1, 0, 1, 2, 1, 1, 0, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map363 x = map371 x := rfl
    simp only [node371, node370, node369, node368, node367, node366, node365, node364, node363, node362, node144, node143, node112, node111, node102, node98, node78, node77, node73, node65, node58, node50, node49, node48, node47, node46, node45, node43, node42, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point87 : stepCheck 1 2308 := by
  apply ofWords 1 2308 [0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] [0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3] [0, 0, 1, 2, 1, 1, 0, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map373 x = map381 x := rfl
    simp only [node381, node380, node379, node378, node377, node376, node375, node374, node373, node372, node175, node134, node133, node124, node123, node112, node98, node91, node90, node89, node81, node72, node69, node58, node50, node49, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point88 : stepCheck 1 2309 := by
  apply ofWords 1 2309 [1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0] [3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3] [0, 3, 0, 0, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map382 x = map392 x := rfl
    simp only [node392, node391, node390, node389, node388, node387, node386, node385, node384, node383, node382, node196, node195, node146, node145, node141, node115, node113, node92, node75, node72, node70, node67, node65, node63, node62, node60, node56, node55, node54, node52, node51, node48, node44, node42, node41, node35, node34, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point89 : stepCheck 1 2311 := by
  apply ofWords 1 2311 [0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0] [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [3, 2, 3, 0, 0, 1, 1, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map393 x = map401 x := rfl
    simp only [node401, node400, node399, node398, node397, node396, node395, node394, node393, node197, node188, node142, node141, node92, node85, node83, node78, node73, node57, node53, node50, node49, node48, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point90 : stepCheck 1 2317 := by
  apply ofWords 1 2317 [0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0] [0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0] [2, 1, 2, 3, 0, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map403 x = map410 x := rfl
    simp only [node410, node409, node408, node407, node406, node405, node404, node403, node402, node199, node198, node166, node135, node126, node125, node123, node83, node82, node75, node70, node67, node63, node62, node60, node55, node54, node52, node51, node44, node42, node40, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point91 : stepCheck 0 2440 := by
  apply ofWords 0 2440 [1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0] [3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0] [0, 3, 0, 1, 0, 3, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map412 x = map419 x := rfl
    simp only [node419, node418, node417, node416, node415, node414, node413, node412, node411, node202, node201, node200, node148, node147, node127, node98, node94, node82, node71, node59, node58, node48, node44, node42, node40, node39, node38, node37, node36, node33, node32, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point92 : stepCheck 0 2443 := by
  apply ofWords 0 2443 [3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0] [3, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0] [2, 3, 2, 1, 0, 1, 0, 1, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map420 x = map429 x := rfl
    simp only [node429, node428, node427, node426, node425, node424, node423, node422, node421, node420, node201, node128, node115, node114, node107, node103, node93, node72, node71, node67, node66, node63, node62, node60, node58, node55, node54, node52, node51, node48, node44, node42, node40, node32, node31, node30, node29, node27, node25, node24, node23, node22, node21, node19, node18, node17, node15, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point93 : stepCheck 0 2444 := by
  apply ofWords 0 2444 [1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0] [1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3] []
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map430 x = map432 x := rfl
    simp only [node432, node431, node430, node149, node76, node68, node56, node28, node22, node15, node12] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3] using h

set_option maxHeartbeats 1600000 in
private theorem point94 : stepCheck 0 2447 := by
  apply ofWords 0 2447 [1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] [0, 3, 0, 1, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map433 x = map438 x := rfl
    simp only [node438, node437, node436, node435, node434, node433, node204, node203, node148, node117, node113, node103, node97, node93, node75, node72, node70, node67, node65, node63, node62, node60, node58, node55, node54, node52, node51, node49, node44, node42, node40, node35, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point95 : stepCheck 0 2449 := by
  apply ofWords 0 2449 [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0] [2, 1, 2, 3, 2, 1, 1, 0, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map439 x = map445 x := rfl
    simp only [node445, node444, node443, node442, node441, node440, node439, node206, node205, node150, node129, node125, node112, node94, node69, node59, node49, node48, node42, node36, node33, node28, node26, node24, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point96 : stepCheck 0 2450 := by
  apply ofWords 0 2450 [3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] [0, 0, 1, 0, 3, 2, 1, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map447 x = map454 x := rfl
    simp only [node454, node453, node452, node451, node450, node449, node448, node447, node446, node207, node129, node105, node103, node88, node68, node59, node50, node49, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point97 : stepCheck 0 2455 := by
  apply ofWords 0 2455 [1, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0] [3, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3] [0, 3, 2, 3, 0, 1, 2, 3, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map456 x = map463 x := rfl
    simp only [node463, node462, node461, node460, node459, node458, node457, node456, node455, node209, node208, node130, node126, node111, node108, node85, node70, node67, node63, node62, node60, node59, node57, node56, node55, node54, node53, node52, node51, node49, node48, node44, node40, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point98 : stepCheck 0 2457 := by
  apply ofWords 0 2457 [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0] [1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [0, 3, 0, 1, 0, 0, 1, 2, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map464 x = map471 x := rfl
    simp only [node471, node470, node469, node468, node467, node466, node465, node464, node211, node210, node153, node152, node151, node148, node113, node101, node95, node91, node75, node74, node71, node70, node68, node67, node65, node64, node63, node62, node60, node57, node56, node55, node54, node53, node52, node51, node44, node40, node35, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point99 : stepCheck 1 2441 := by
  apply ofWords 1 2441 [0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0] [0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] [1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map473 x = map478 x := rfl
    simp only [node478, node477, node476, node475, node474, node473, node472, node212, node196, node191, node159, node123, node114, node105, node93, node90, node89, node66, node59, node58, node49, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point100 : stepCheck 1 2444 := by
  apply ofWords 1 2444 [1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0] [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3] [3, 0, 1, 1, 0, 1, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map479 x = map485 x := rfl
    simp only [node485, node484, node483, node482, node481, node480, node479, node214, node213, node211, node185, node161, node149, node113, node107, node106, node75, node71, node70, node68, node67, node65, node63, node62, node60, node56, node55, node54, node52, node51, node49, node48, node44, node35, node33, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point101 : stepCheck 1 2447 := by
  apply ofWords 1 2447 [1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3] [1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map486 x = map493 x := rfl
    simp only [node493, node492, node491, node490, node489, node488, node487, node486, node215, node132, node127, node117, node94, node79, node78, node69, node56, node53, node49, node40, node39, node38, node37, node36, node34, node33, node32, node29, node28, node26, node25, node24, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point102 : stepCheck 1 2449 := by
  apply ofWords 1 2449 [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 0] [1, 0, 1, 1, 2, 1, 2, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map494 x = map501 x := rfl
    simp only [node501, node500, node499, node498, node497, node496, node495, node494, node205, node124, node115, node110, node97, node90, node89, node59, node58, node57, node53, node50, node48, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point103 : stepCheck 1 2456 := by
  apply ofWords 1 2456 [0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0] [0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1] [0, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map502 x = map509 x := rfl
    simp only [node509, node508, node507, node506, node505, node504, node503, node502, node215, node199, node154, node151, node121, node117, node96, node85, node79, node59, node57, node53, node40, node30, node28, node25, node22, node16, node15, node14, node13, node12, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point104 : stepCheck 0 2583 := by
  apply ofWords 0 2583 [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1] [1, 1, 0, 1, 2, 1, 1, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map511 x = map519 x := rfl
    simp only [node519, node518, node517, node516, node515, node514, node513, node512, node511, node510, node216, node155, node144, node96, node86, node81, node71, node66, node63, node61, node55, node52, node51, node44, node42, node33, node30, node29, node28, node27, node25, node24, node23, node22, node21, node19, node18, node17, node15, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point105 : stepCheck 0 2586 := by
  apply ofWords 0 2586 [1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0] [2]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map521 x = map523 x := rfl
    simp only [node523, node522, node521, node520, node156, node120, node76, node72, node61, node42, node22, node19, node15, node12] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base6] using h

set_option maxHeartbeats 1600000 in
private theorem point106 : stepCheck 0 2588 := by
  apply ofWords 0 2588 [3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0] [0, 1, 2, 3, 0, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map525 x = map533 x := rfl
    simp only [node533, node532, node531, node530, node529, node528, node527, node526, node525, node524, node218, node217, node173, node126, node124, node105, node102, node91, node90, node89, node84, node69, node61, node50, node49, node48, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point107 : stepCheck 0 2591 := by
  apply ofWords 0 2591 [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [2, 1, 2, 3, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map534 x = map539 x := rfl
    simp only [node539, node538, node537, node536, node535, node534, node221, node220, node219, node216, node181, node177, node176, node155, node87, node84, node71, node70, node67, node65, node64, node63, node62, node61, node60, node55, node54, node53, node52, node51, node49, node44, node42, node35, node34, node31, node30, node29, node28, node27, node26, node25, node24, node23, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point108 : stepCheck 0 2594 := by
  apply ofWords 0 2594 [1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0] [2]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map540 x = map542 x := rfl
    simp only [node542, node541, node540, node200, node180, node120, node84, node76, node72, node61, node42, node22, node19, node15, node12] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base6] using h

set_option maxHeartbeats 1600000 in
private theorem point109 : stepCheck 0 2597 := by
  apply ofWords 0 2597 [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0] [0, 1, 0, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map544 x = map553 x := rfl
    simp only [node553, node552, node551, node550, node549, node548, node547, node546, node545, node544, node543, node214, node139, node104, node93, node88, node87, node78, node71, node67, node63, node62, node61, node60, node58, node55, node54, node52, node51, node49, node48, node44, node42, node32, node30, node29, node28, node27, node25, node24, node23, node22, node21, node19, node18, node17, node15, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point110 : stepCheck 1 2581 := by
  apply ofWords 1 2581 [0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1] [0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0] [0, 1, 1, 2, 1, 1, 0, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map554 x = map561 x := rfl
    simp only [node561, node560, node559, node558, node557, node556, node555, node554, node223, node222, node149, node137, node125, node119, node112, node83, node79, node77, node73, node68, node66, node64, node54, node50, node47, node46, node45, node43, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point111 : stepCheck 1 2584 := by
  apply ofWords 1 2584 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0] [0, 1, 0, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map562 x = map570 x := rfl
    simp only [node570, node569, node568, node567, node566, node565, node564, node563, node562, node223, node164, node156, node119, node109, node92, node88, node83, node79, node77, node73, node71, node61, node59, node50, node47, node46, node45, node44, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point112 : stepCheck 1 2585 := by
  apply ofWords 1 2585 [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] [0, 3, 0, 0, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map571 x = map578 x := rfl
    simp only [node578, node577, node576, node575, node574, node573, node572, node571, node156, node146, node106, node94, node92, node82, node61, node49, node40, node34, node28, node22, node21, node20, node19, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point113 : stepCheck 1 2592 := by
  apply ofWords 1 2592 [0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0] [2]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map580 x = map582 x := rfl
    simp only [node582, node581, node580, node579, node192, node84, node78, node76, node66, node61, node49, node28, node22, node19, node15, node12] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base6] using h

set_option maxHeartbeats 1600000 in
private theorem point114 : stepCheck 1 2594 := by
  apply ofWords 1 2594 [1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0] [3, 0, 1, 0, 3, 0, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map584 x = map590 x := rfl
    simp only [node590, node589, node588, node587, node586, node585, node584, node583, node194, node193, node152, node147, node111, node99, node93, node84, node72, node71, node61, node58, node50, node48, node47, node46, node45, node44, node43, node42, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point115 : stepCheck 1 2596 := by
  apply ofWords 1 2596 [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [3, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [2, 1, 1, 0, 3, 2, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map591 x = map599 x := rfl
    simp only [node599, node598, node597, node596, node595, node594, node593, node592, node591, node207, node206, node165, node150, node106, node104, node87, node69, node61, node50, node49, node48, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point116 : stepCheck 1 2598 := by
  apply ofWords 1 2598 [0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1] [1, 1, 2, 3, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map600 x = map608 x := rfl
    simp only [node608, node607, node606, node605, node604, node603, node602, node601, node600, node198, node187, node186, node129, node110, node104, node100, node96, node79, node73, node71, node61, node57, node53, node50, node49, node48, node47, node46, node45, node44, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point117 : stepCheck 1 2599 := by
  apply ofWords 1 2599 [0, 3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1] [3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0] [3, 0, 1, 2, 3, 2, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map609 x = map618 x := rfl
    simp only [node618, node617, node616, node615, node614, node613, node612, node611, node610, node609, node195, node142, node126, node119, node104, node85, node83, node77, node74, node73, node61, node57, node53, node50, node48, node47, node46, node45, node43, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point118 : stepCheck 0 2726 := by
  apply ofWords 0 2726 [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1] [1, 0, 1, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map620 x = map627 x := rfl
    simp only [node627, node626, node625, node624, node623, node622, node621, node620, node619, node154, node153, node140, node127, node96, node94, node82, node80, node79, node56, node52, node51, node44, node40, node39, node38, node37, node36, node33, node32, node30, node29, node28, node27, node26, node25, node23, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point119 : stepCheck 0 2728 := by
  apply ofWords 0 2728 [3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0] [1, 0, 0, 3, 2, 1, 2, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map628 x = map634 x := rfl
    simp only [node634, node633, node632, node631, node630, node629, node628, node225, node224, node218, node217, node204, node128, node124, node108, node102, node95, node90, node89, node72, node69, node66, node64, node56, node50, node47, node46, node45, node43, node42, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point120 : stepCheck 0 2731 := by
  apply ofWords 0 2731 [1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 3, 0, 1, 0] [0, 3, 0, 0, 1, 2, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map635 x = map642 x := rfl
    simp only [node642, node641, node640, node639, node638, node637, node636, node635, node226, node225, node222, node172, node152, node146, node125, node101, node95, node71, node68, node64, node57, node56, node54, node53, node45, node44, node43, node41, node40, node34, node31, node30, node29, node28, node27, node25, node24, node23, node22, node21, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point121 : stepCheck 0 2732 := by
  apply ofWords 0 2732 [3, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3] [3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map643 x = map646 x := rfl
    simp only [node646, node645, node644, node643, node224, node121, node95, node82, node64, node59, node56, node40, node28, node22, node19, node15, node12] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point122 : stepCheck 0 2733 := by
  apply ofWords 0 2733 [1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0] [0, 1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map648 x = map655 x := rfl
    simp only [node655, node654, node653, node652, node651, node650, node649, node648, node647, node210, node150, node109, node101, node95, node88, node83, node76, node74, node69, node68, node64, node57, node56, node53, node40, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point123 : stepCheck 0 2734 := by
  apply ofWords 0 2734 [3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3] [1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3] [1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map656 x = map664 x := rfl
    simp only [node664, node663, node662, node661, node660, node659, node658, node657, node656, node136, node128, node122, node100, node86, node66, node59, node53, node50, node47, node46, node45, node44, node43, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point124 : stepCheck 0 2735 := by
  apply ofWords 0 2735 [3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3] [1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1] [0, 1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map666 x = map673 x := rfl
    simp only [node673, node672, node671, node670, node669, node668, node667, node666, node665, node212, node171, node154, node151, node143, node138, node114, node96, node93, node74, node58, node55, node51, node44, node40, node36, node33, node32, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point125 : stepCheck 0 2739 := by
  apply ofWords 0 2739 [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3] [3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0] [1, 1, 0, 0, 1, 1, 0, 1, 2, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map675 x = map683 x := rfl
    simp only [node683, node682, node681, node680, node679, node678, node677, node676, node675, node674, node179, node158, node144, node143, node128, node112, node86, node66, node63, node60, node55, node54, node52, node51, node44, node33, node30, node29, node27, node25, node24, node23, node22, node21, node19, node18, node17, node15, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point126 : stepCheck 1 2720 := by
  apply ofWords 1 2720 [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 3] [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [2, 3, 0, 3, 2, 3, 0, 1, 2, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map684 x = map693 x := rfl
    simp only [node693, node692, node691, node690, node689, node688, node687, node686, node685, node684, node203, node184, node140, node131, node118, node104, node102, node101, node80, node77, node73, node61, node57, node56, node53, node50, node49, node48, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point127 : stepCheck 1 2726 := by
  apply ofWords 1 2726 [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0] [0, 3, 0, 1, 1, 0, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map695 x = map705 x := rfl
    simp only [node705, node704, node703, node702, node701, node700, node699, node698, node697, node696, node695, node694, node213, node145, node127, node111, node94, node80, node64, node56, node51, node48, node44, node41, node40, node39, node38, node37, node36, node34, node33, node32, node30, node29, node28, node26, node25, node23, node22, node20, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point128 : stepCheck 1 2729 := by
  apply ofWords 1 2729 [0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0] [3, 2, 3, 0, 0, 1, 1, 2, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map707 x = map715 x := rfl
    simp only [node715, node714, node713, node712, node711, node710, node709, node708, node707, node706, node197, node183, node110, node95, node92, node77, node73, node68, node64, node59, node57, node56, node53, node50, node48, node47, node46, node45, node43, node41, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point129 : stepCheck 1 2733 := by
  apply ofWords 1 2733 [1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3] [3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3] [1]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map716 x = map718 x := rfl
    simp only [node718, node717, node716, node136, node111, node95, node86, node66, node64, node56, node48, node40, node28, node22, node19, node15, node12] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base5] using h

set_option maxHeartbeats 1600000 in
private theorem point130 : stepCheck 1 2736 := by
  apply ofWords 1 2736 [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 3] [0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0] [1, 2, 1, 0, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map720 x = map726 x := rfl
    simp only [node726, node725, node724, node723, node722, node721, node720, node719, node208, node169, node168, node167, node138, node129, node99, node88, node75, node70, node67, node65, node63, node62, node60, node55, node54, node52, node51, node49, node44, node40, node35, node34, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (1 : Fin 2).castLE (by decide) = (1 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point131 : stepCheck 0 2860 := by
  apply ofWords 0 2860 [1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0] [3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1] [1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map728 x = map737 x := rfl
    simp only [node737, node736, node735, node734, node733, node732, node731, node730, node729, node728, node727, node227, node147, node130, node122, node109, node107, node97, node84, node82, node66, node61, node58, node50, node48, node47, node46, node45, node44, node43, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point132 : stepCheck 0 2862 := by
  apply ofWords 0 2862 [1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0] [1, 0, 1, 0, 1, 0, 0, 1, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map739 x = map746 x := rfl
    simp only [node746, node745, node744, node743, node742, node741, node740, node739, node738, node227, node226, node202, node182, node174, node153, node114, node98, node91, node86, node82, node64, node59, node58, node57, node53, node51, node50, node47, node46, node45, node44, node43, node41, node40, node39, node38, node37, node36, node35, node34, node33, node32, node31, node30, node29, node28, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point133 : stepCheck 0 2863 := by
  apply ofWords 0 2863 [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0] [2, 1, 2, 3, 0, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map748 x = map753 x := rfl
    simp only [node753, node752, node751, node750, node749, node748, node747, node209, node190, node118, node103, node94, node85, node81, node68, node57, node53, node49, node48, node42, node30, node28, node26, node25, node22, node20, node19, node16, node15, node14, node13, node12, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point134 : stepCheck 0 2865 := by
  apply ofWords 0 2865 [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] [0, 1, 0, 0, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map754 x = map760 x := rfl
    simp only [node760, node759, node758, node757, node756, node755, node754, node221, node220, node219, node163, node155, node108, node99, node88, node87, node84, node71, node64, node61, node52, node49, node44, node42, node35, node34, node31, node30, node28, node27, node24, node23, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

set_option maxHeartbeats 1600000 in
private theorem point135 : stepCheck 0 2869 := by
  apply ofWords 0 2869 [1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] [1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3] [1, 2, 1, 0, 0, 1, 1, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro x
    have h : map761 x = map769 x := rfl
    simp only [node769, node768, node767, node766, node765, node764, node763, node762, node761, node189, node170, node145, node130, node122, node113, node109, node87, node75, node70, node68, node67, node65, node63, node62, node60, node56, node55, node54, node52, node51, node48, node44, node42, node35, node33, node31, node30, node29, node28, node27, node26, node25, node24, node23, node22, node21, node20, node19, node18, node17, node16, node15, node14, node13, node12, node11, node10, node9, node8] at h
    simpa only [show (0 : Fin 2).castLE (by decide) = (0 : Fin 4) from rfl,
      Part6Tables.eval, base0, base1, base3, base4, base5, base6, base7] using h

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual

/-- The fixed residual interval 68--135 is certified by shared composition tables. -/
public theorem residuals1 : residualBatch 1 := by
  intro s hs
  fin_cases s
  · exact Certificate1.point68
  · exact Certificate1.point69
  · exact Certificate1.point70
  · exact Certificate1.point71
  · exact Certificate1.point72
  · exact Certificate1.point73
  · exact Certificate1.point74
  · exact Certificate1.point75
  · exact Certificate1.point76
  · exact Certificate1.point77
  · exact Certificate1.point78
  · exact Certificate1.point79
  · exact Certificate1.point80
  · exact Certificate1.point81
  · exact Certificate1.point82
  · exact Certificate1.point83
  · exact Certificate1.point84
  · exact Certificate1.point85
  · exact Certificate1.point86
  · exact Certificate1.point87
  · exact Certificate1.point88
  · exact Certificate1.point89
  · exact Certificate1.point90
  · exact Certificate1.point91
  · exact Certificate1.point92
  · exact Certificate1.point93
  · exact Certificate1.point94
  · exact Certificate1.point95
  · exact Certificate1.point96
  · exact Certificate1.point97
  · exact Certificate1.point98
  · exact Certificate1.point99
  · exact Certificate1.point100
  · exact Certificate1.point101
  · exact Certificate1.point102
  · exact Certificate1.point103
  · exact Certificate1.point104
  · exact Certificate1.point105
  · exact Certificate1.point106
  · exact Certificate1.point107
  · exact Certificate1.point108
  · exact Certificate1.point109
  · exact Certificate1.point110
  · exact Certificate1.point111
  · exact Certificate1.point112
  · exact Certificate1.point113
  · exact Certificate1.point114
  · exact Certificate1.point115
  · exact Certificate1.point116
  · exact Certificate1.point117
  · exact Certificate1.point118
  · exact Certificate1.point119
  · exact Certificate1.point120
  · exact Certificate1.point121
  · exact Certificate1.point122
  · exact Certificate1.point123
  · exact Certificate1.point124
  · exact Certificate1.point125
  · exact Certificate1.point126
  · exact Certificate1.point127
  · exact Certificate1.point128
  · exact Certificate1.point129
  · exact Certificate1.point130
  · exact Certificate1.point131
  · exact Certificate1.point132
  · exact Certificate1.point133
  · exact Certificate1.point134
  · exact Certificate1.point135

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual
