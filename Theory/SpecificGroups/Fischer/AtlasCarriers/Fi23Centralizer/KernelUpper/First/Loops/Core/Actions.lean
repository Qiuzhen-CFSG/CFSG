module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word7
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word9
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word16
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word18
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word20
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word35
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word48
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word49
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word50
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word52
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word54
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word66
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word67
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word72
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word74
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word76
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word91
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word101
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word102
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word103
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word105
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word107
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word116
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word117
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word128
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word137
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word138
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word139
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word141
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word143
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word154
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word158
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word159
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word179
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word181
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word182
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word192
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word193
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word202
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word203
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word214
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word217
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Core.Checks.Word218

/-!
# Actions of the actual shared Fi23 subgroup registers

Each short numerical equation is transported through multiplication in the
unchanged subgroup. A left inverse equation suffices for an inverse register,
since its preceding word is already a genuine permutation. Only the stretches
between shared registers are unfolded. The pointwise multiplication lemma
keeps elaboration and kernel checking from expanding the stored words.

Source: retained ATLAS F23G1-p31671B0 in the inverse-cycle convention;
GLS3 Table 5.3u. The registers and numerical candidates are unchanged.
-/

set_option Elab.async false

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Core

private theorem one_action (x : Fin 31671) : x = (1 : KernelUpperData.first).val x := rfl

private theorem mul_actions {u v : KernelUpperData.first} {f g : Fin 31671 → Fin 31671}
    (hf : ∀ x, f x = u.val x) (hg : ∀ x, g x = v.val x) (x : Fin 31671) :
    f (g x) = (u * v).val x :=
  (hf (g x)).trans (congrArg u.val (hg x))

private theorem action_of_relation (f : Fin 31671 → Fin 31671)
    (l w r : KernelUpperData.first) (hr : l * w = r)
    (h : ∀ x, l.val (f x) = r.val x) (x : Fin 31671) : f x = w.val x := by
  apply l.val.injective
  have hw := congrArg (fun v : KernelUpperData.first => v.val x) hr
  exact (h x).trans hw.symm

theorem action1 (x : Fin 31671) : KernelUpperData.One0.forward x = word1.val x := rfl

theorem action2 (x : Fin 31671) : KernelUpperData.One1.forward x = word2.val x := rfl

theorem action3 (x : Fin 31671) : KernelUpperData.lookup blocks3 x = word3.val x := rfl

theorem action4 (x : Fin 31671) : KernelUpperData.lookup blocks4 x = word4.val x := rfl

theorem action7 (x : Fin 31671) : KernelUpperData.lookup blocks7 x = word7.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks7) ((1 : KernelUpperData.first)) word7 (word3 * word3 * word3 * word3) ?_ ?_ x
  · simp only [word7, word6, word5, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check7.equation y).trans ((mul_actions (mul_actions (mul_actions action3 action3) action3) action3) _))

theorem action9 (x : Fin 31671) : KernelUpperData.lookup blocks9 x = word9.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks9) (word7) word9 (word1) ?_ ?_ x
  · simp only [word9, word8, mul_inv_cancel_left]
  · intro y
    exact (action7 _).symm.trans ((Check9.equation y).trans (action1 _))

theorem action11 (x : Fin 31671) : KernelUpperData.lookup blocks11 x = word11.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks11) (word1) word11 (word7) ?_ ?_ x
  · simp only [word11, word10, mul_inv_cancel_left]
  · intro y
    exact (action1 _).symm.trans ((Check11.equation y).trans (action7 _))

theorem action16 (x : Fin 31671) : KernelUpperData.lookup blocks16 x = word16.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks16) ((1 : KernelUpperData.first)) word16 (word3 * word3 * word4 * word3 * word3 * word3) ?_ ?_ x
  · simp only [word16, word15, word14, word13, word12, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check16.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action3 action3) action4) action3) action3) action3) _))

theorem action18 (x : Fin 31671) : KernelUpperData.lookup blocks18 x = word18.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks18) (word16) word18 (word2) ?_ ?_ x
  · simp only [word18, word17, mul_inv_cancel_left]
  · intro y
    exact (action16 _).symm.trans ((Check18.equation y).trans (action2 _))

theorem action20 (x : Fin 31671) : KernelUpperData.lookup blocks20 x = word20.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks20) (word2) word20 (word16) ?_ ?_ x
  · simp only [word20, word19, mul_inv_cancel_left]
  · intro y
    exact (action2 _).symm.trans ((Check20.equation y).trans (action16 _))

theorem action35 (x : Fin 31671) : KernelUpperData.lookup blocks35 x = word35.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks35) ((1 : KernelUpperData.first)) word35 (word2 * word11 * word1 * word4 * word20) ?_ ?_ x
  · simp only [word35, word34, word33, word32, word31, word30, word29, word28, word27, word26, word25, word24, word23, word22, word21, mul_assoc, one_mul, mul_one]
  · intro y
    exact (one_action _).symm.trans ((Check35.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions action2 action11) action1) action4) action20) _))

theorem action48 (x : Fin 31671) : KernelUpperData.lookup blocks48 x = word48.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks48) ((1 : KernelUpperData.first)) word48 (word1 * word4 * word20 * word1 * word20 * word2 * word9 * word35 * word2 * word9 * word2 * word1 * word18 * word1) ?_ ?_ x
  · simp only [word48, word47, word46, word45, word44, word43, word42, word41, word40, word39, word38, word37, word36, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check48.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action1 action4) action20) action1) action20) action2) action9) action35) action2) action9) action2) action1) action18) action1) _))

theorem action49 (x : Fin 31671) : KernelUpperData.lookup blocks49 x = word49.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks49) (word48) word49 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word49, mul_inv_cancel]
  · intro y
    exact (action48 _).symm.trans ((Check49.equation y).trans (one_action _))

theorem action50 (x : Fin 31671) : KernelUpperData.lookup blocks50 x = word50.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks50) ((1 : KernelUpperData.first)) word50 (word49 * word49) ?_ ?_ x
  · simp only [word50, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check50.equation y).trans ((mul_actions action49 action49) _))

theorem action52 (x : Fin 31671) : KernelUpperData.lookup blocks52 x = word52.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks52) (word50) word52 (word48) ?_ ?_ x
  · simp only [word52, word51, mul_inv_cancel_left]
  · intro y
    exact (action50 _).symm.trans ((Check52.equation y).trans (action48 _))

theorem action54 (x : Fin 31671) : KernelUpperData.lookup blocks54 x = word54.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks54) (word48) word54 (word50) ?_ ?_ x
  · simp only [word54, word53, mul_inv_cancel_left]
  · intro y
    exact (action48 _).symm.trans ((Check54.equation y).trans (action50 _))

theorem action66 (x : Fin 31671) : KernelUpperData.lookup blocks66 x = word66.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks66) ((1 : KernelUpperData.first)) word66 (word1 * word4 * word20 * word4 * word20 * word20 * word35 * word4 * word4 * word3 * word4 * word11 * word4) ?_ ?_ x
  · simp only [word66, word65, word64, word63, word62, word61, word60, word59, word58, word57, word56, word55, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check66.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action1 action4) action20) action4) action20) action20) action35) action4) action4) action3) action4) action11) action4) _))

theorem action67 (x : Fin 31671) : KernelUpperData.lookup blocks67 x = word67.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks67) (word66) word67 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word67, mul_inv_cancel]
  · intro y
    exact (action66 _).symm.trans ((Check67.equation y).trans (one_action _))

theorem action72 (x : Fin 31671) : KernelUpperData.lookup blocks72 x = word72.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks72) ((1 : KernelUpperData.first)) word72 (word49 * word49 * word67 * word54 * word49 * word49) ?_ ?_ x
  · simp only [word72, word71, word70, word69, word68, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check72.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action49 action49) action67) action54) action49) action49) _))

theorem action74 (x : Fin 31671) : KernelUpperData.lookup blocks74 x = word74.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks74) (word72) word74 (word66) ?_ ?_ x
  · simp only [word74, word73, mul_inv_cancel_left]
  · intro y
    exact (action72 _).symm.trans ((Check74.equation y).trans (action66 _))

theorem action76 (x : Fin 31671) : KernelUpperData.lookup blocks76 x = word76.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks76) (word66) word76 (word72) ?_ ?_ x
  · simp only [word76, word75, mul_inv_cancel_left]
  · intro y
    exact (action66 _).symm.trans ((Check76.equation y).trans (action72 _))

theorem action91 (x : Fin 31671) : KernelUpperData.lookup blocks91 x = word91.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks91) ((1 : KernelUpperData.first)) word91 (word52 * word67 * word49 * word54) ?_ ?_ x
  · simp only [word91, word90, word89, word88, word87, word86, word85, word84, word83, word82, word81, word80, word79, word78, word77, mul_assoc, one_mul, mul_one]
  · intro y
    exact (one_action _).symm.trans ((Check91.equation y).trans ((mul_actions (mul_actions (mul_actions action52 action67) action49) action54) _))

theorem action101 (x : Fin 31671) : KernelUpperData.lookup blocks101 x = word101.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks101) ((1 : KernelUpperData.first)) word101 (word48 * word54 * word74 * word48 * word76 * word66 * word91 * word52 * word49 * word76 * word49) ?_ ?_ x
  · simp only [word101, word100, word99, word98, word97, word96, word95, word94, word93, word92, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check101.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action48 action54) action74) action48) action76) action66) action91) action52) action49) action76) action49) _))

theorem action102 (x : Fin 31671) : KernelUpperData.lookup blocks102 x = word102.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks102) (word101) word102 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word102, mul_inv_cancel]
  · intro y
    exact (action101 _).symm.trans ((Check102.equation y).trans (one_action _))

theorem action103 (x : Fin 31671) : KernelUpperData.lookup blocks103 x = word103.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks103) ((1 : KernelUpperData.first)) word103 (word102 * word102) ?_ ?_ x
  · simp only [word103, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check103.equation y).trans ((mul_actions action102 action102) _))

theorem action105 (x : Fin 31671) : KernelUpperData.lookup blocks105 x = word105.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks105) (word103) word105 (word101) ?_ ?_ x
  · simp only [word105, word104, mul_inv_cancel_left]
  · intro y
    exact (action103 _).symm.trans ((Check105.equation y).trans (action101 _))

theorem action107 (x : Fin 31671) : KernelUpperData.lookup blocks107 x = word107.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks107) (word101) word107 (word103) ?_ ?_ x
  · simp only [word107, word106, mul_inv_cancel_left]
  · intro y
    exact (action101 _).symm.trans ((Check107.equation y).trans (action103 _))

theorem action116 (x : Fin 31671) : KernelUpperData.lookup blocks116 x = word116.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks116) ((1 : KernelUpperData.first)) word116 (word52 * word74 * word66 * word76 * word49 * word91 * word52 * word76 * word52 * word48) ?_ ?_ x
  · simp only [word116, word115, word114, word113, word112, word111, word110, word109, word108, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check116.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action52 action74) action66) action76) action49) action91) action52) action76) action52) action48) _))

theorem action117 (x : Fin 31671) : KernelUpperData.lookup blocks117 x = word117.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks117) (word116) word117 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word117, mul_inv_cancel]
  · intro y
    exact (action116 _).symm.trans ((Check117.equation y).trans (one_action _))

theorem action128 (x : Fin 31671) : KernelUpperData.lookup blocks128 x = word128.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks128) ((1 : KernelUpperData.first)) word128 (word116 * word105 * word117 * word101 * word102) ?_ ?_ x
  · simp only [word128, word127, word126, word125, word124, word123, word122, word121, word120, word119, word118, mul_assoc, one_mul, mul_one]
  · intro y
    exact (one_action _).symm.trans ((Check128.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions action116 action105) action117) action101) action102) _))

theorem action137 (x : Fin 31671) : KernelUpperData.lookup blocks137 x = word137.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks137) ((1 : KernelUpperData.first)) word137 (word117 * word107 * word116 * word116 * word128 * word105 * word116 * word107 * word117 * word102) ?_ ?_ x
  · simp only [word137, word136, word135, word134, word133, word132, word131, word130, word129, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check137.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action117 action107) action116) action116) action128) action105) action116) action107) action117) action102) _))

theorem action138 (x : Fin 31671) : KernelUpperData.lookup blocks138 x = word138.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks138) (word137) word138 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word138, mul_inv_cancel]
  · intro y
    exact (action137 _).symm.trans ((Check138.equation y).trans (one_action _))

theorem action139 (x : Fin 31671) : KernelUpperData.lookup blocks139 x = word139.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks139) ((1 : KernelUpperData.first)) word139 (word138 * word138) ?_ ?_ x
  · simp only [word139, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check139.equation y).trans ((mul_actions action138 action138) _))

theorem action141 (x : Fin 31671) : KernelUpperData.lookup blocks141 x = word141.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks141) (word139) word141 (word137) ?_ ?_ x
  · simp only [word141, word140, mul_inv_cancel_left]
  · intro y
    exact (action139 _).symm.trans ((Check141.equation y).trans (action137 _))

theorem action143 (x : Fin 31671) : KernelUpperData.lookup blocks143 x = word143.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks143) (word137) word143 (word139) ?_ ?_ x
  · simp only [word143, word142, mul_inv_cancel_left]
  · intro y
    exact (action137 _).symm.trans ((Check143.equation y).trans (action139 _))

theorem action154 (x : Fin 31671) : KernelUpperData.lookup blocks154 x = word154.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks154) ((1 : KernelUpperData.first)) word154 (word105 * word117 * word117 * word101 * word128 * word102 * word117 * word105 * word117 * word102 * word138 * word138) ?_ ?_ x
  · simp only [word154, word153, word152, word151, word150, word149, word148, word147, word146, word145, word144, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check154.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action105 action117) action117) action101) action128) action102) action117) action105) action117) action102) action138) action138) _))

theorem action158 (x : Fin 31671) : KernelUpperData.lookup blocks158 x = word158.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks158) (word154) word158 (word143) ?_ ?_ x
  · simp only [word158, word157, mul_inv_cancel_left]
  · intro y
    exact (action154 _).symm.trans ((Check158.equation y).trans (action143 _))

theorem action159 (x : Fin 31671) : KernelUpperData.lookup blocks159 x = word159.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks159) (word154) word159 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word159, mul_inv_cancel]
  · intro y
    exact (action154 _).symm.trans ((Check159.equation y).trans (one_action _))

theorem action179 (x : Fin 31671) : KernelUpperData.lookup blocks179 x = word179.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks179) ((1 : KernelUpperData.first)) word179 (word141 * word158 * word141 * word137 * word154 * word138 * word138 * word154 * word154) ?_ ?_ x
  · simp only [word179, word178, word177, word176, word175, word174, word173, word172, word171, word170, word169, word168, word167, word166, word165, word164, word163, word162, word161, word160, mul_assoc, one_mul, mul_one]
  · intro y
    exact (one_action _).symm.trans ((Check179.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action141 action158) action141) action137) action154) action138) action138) action154) action154) _))

theorem action181 (x : Fin 31671) : KernelUpperData.lookup blocks181 x = word181.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks181) (word179) word181 (word159) ?_ ?_ x
  · simp only [word181, word180, mul_inv_cancel_left]
  · intro y
    exact (action179 _).symm.trans ((Check181.equation y).trans (action159 _))

theorem action182 (x : Fin 31671) : KernelUpperData.lookup blocks182 x = word182.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks182) (word179) word182 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word182, mul_inv_cancel]
  · intro y
    exact (action179 _).symm.trans ((Check182.equation y).trans (one_action _))

theorem action192 (x : Fin 31671) : KernelUpperData.lookup blocks192 x = word192.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks192) ((1 : KernelUpperData.first)) word192 (word101 * word101 * word116 * word107 * word128 * word105 * word117 * word117 * word138 * word159 * word159) ?_ ?_ x
  · simp only [word192, word191, word190, word189, word188, word187, word186, word185, word184, word183, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check192.equation y).trans ((mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions (mul_actions action101 action101) action116) action107) action128) action105) action117) action117) action138) action159) action159) _))

theorem action193 (x : Fin 31671) : KernelUpperData.lookup blocks193 x = word193.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks193) (word192) word193 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word193, mul_inv_cancel]
  · intro y
    exact (action192 _).symm.trans ((Check193.equation y).trans (one_action _))

theorem action200 (x : Fin 31671) : KernelUpperData.lookup blocks200 x = word200.val x := by
  have hm : KernelUpperData.lookup blocks200 = KernelUpperData.lookup blocks192 := rfl
  rw [hm]
  simpa only [word200, word198, word196, word194, word195, word197, word199, one_mul, mul_one] using action192 x

theorem action202 (x : Fin 31671) : KernelUpperData.lookup blocks202 x = word202.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks202) ((1 : KernelUpperData.first)) word202 (word179 * word200 * word179) ?_ ?_ x
  · simp only [word202, word201, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check202.equation y).trans ((mul_actions (mul_actions action179 action200) action179) _))

theorem action203 (x : Fin 31671) : KernelUpperData.lookup blocks203 x = word203.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks203) (word202) word203 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word203, mul_inv_cancel]
  · intro y
    exact (action202 _).symm.trans ((Check203.equation y).trans (one_action _))

theorem action214 (x : Fin 31671) : KernelUpperData.lookup blocks214 x = word214.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks214) (word192 * word203 * word203 * word193 * word203) word214 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word214, word213, word212, word211, word210, word209, word208, word207, word206, word205, word204, mul_assoc, one_mul, mul_one, mul_inv_rev,
      mul_inv_cancel_left, mul_inv_cancel]
  · intro y
    exact ((mul_actions (mul_actions (mul_actions (mul_actions action192 action203) action203) action193) action203) _).symm.trans ((Check214.equation y).trans (one_action _))

theorem action217 (x : Fin 31671) : KernelUpperData.lookup blocks217 x = word217.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks217) ((1 : KernelUpperData.first)) word217 (word182 * word200 * word182 * word193) ?_ ?_ x
  · simp only [word217, word216, word215, mul_assoc, one_mul]
  · intro y
    exact (one_action _).symm.trans ((Check217.equation y).trans ((mul_actions (mul_actions (mul_actions action182 action200) action182) action193) _))

theorem action218 (x : Fin 31671) : KernelUpperData.lookup blocks218 x = word218.val x := by
  apply action_of_relation (KernelUpperData.lookup blocks218) (word217) word218 ((1 : KernelUpperData.first)) ?_ ?_ x
  · simp only [word218, mul_inv_cancel]
  · intro y
    exact (action217 _).symm.trans ((Check218.equation y).trans (one_action _))

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Core
