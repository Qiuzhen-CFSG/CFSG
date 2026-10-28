module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elements
public import Theory.GroupTheory.WordSubgroup
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# An elementary eight in the actual McL permutation carrier

Three words in the published ATLAS generators are involutions and commute.
Their eight products move a marked point independently. The word identities
and permutation relations are checked on the actual 275-point carrier;
GAP is used only to discover the words, not as a mathematical premise.
Source: ATLAS McLG1-p275B0; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Sporadic.LeechRelated.McL.TwoRank
open ThreeRank Theory.GroupTheory
set_option maxRecDepth 20000

private def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)
private theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi
private def packedMap (v : Nat) (i : Fin 275) : Fin 275 :=
  ⟨(v >>> (9 * i.val)) % 512 % 275, Nat.mod_lt _ (by decide)⟩
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))

private def xWord : List (Fin 3) := [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]
private def x : Carrier := evalWord ![a,b,b⁻¹] xWord
private def xTable : Equiv.Perm (Fin 275) :=
  tablePerm (packedMap 5807563885600300802262440409932209675294108690736229204010873776277491696897102728720682649014317025927964463409718187487163641293446845988826488977046542824700317606769641770743612965008362904220364767113034585076310641839307323355227079400177090411480446761500102659156099682720888081518549622002528115846709077453530928210401490630960755312580989130856353986848865032045663095588332262608902923677620607325986245729261366922221385541553728451929865947825993381510876753299124385538197556836053090920835689226253618060742628661671067039234826273631936539812998122043934682179489287510166003976880794819033382853249821727397320066208700819401200654652079060448846599887589661669590841199624169720874905481618153236368254021788623623926873711104) (packedMap 5807563885600300802262440409932209675294108690736229204010873776277491696897102728720682649014317025927964463409718187487163641293446845988826488977046542824700317606769641770743612965008362904220364767113034585076310641839307323355227079400177090411480446761500102659156099682720888081518549622002528115846709077453530928210401490630960755312580989130856353986848865032045663095588332262608902923677620607325986245729261366922221385541553728451929865947825993381510876753299124385538197556836053090920835689226253618060742628661671067039234826273631936539812998122043934682179489287510166003976880794819033382853249821727397320066208700819401200654652079060448846599887589661669590841199624169720874905481618153236368254021788623623926873711104)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem x_table : inclusion x = xTable := by
  change evalWord ![aPerm, bPerm, bPerm⁻¹] xWord = xTable
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem x_sq : x ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private def yWord : List (Fin 3) := [2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
private def y : Carrier := evalWord ![a,b,b⁻¹] yWord
private def yTable : Equiv.Perm (Fin 275) :=
  tablePerm (packedMap 4291346900403284655861908017424091484484955181311227005258585938340678077197019169710940198440799057493308073595599602769236207191908921328664216767129654980091954144451571122271832938952660390481252343255867848865822128437754581858780006806706728182928428023747869612863823236450827675918933623669421570312023110399882016904820430556408301331686084961437973004824845654100253600969826819368143435145026278405067455740507189386921908439406730729152252909427779301417259695009736075861485121261580793612499647001562430263933065816950894022198580543076379945304771663646182465505721985288128560000910149396764897311695428054819319485720080989694833507710056790365012113468490251655301047286567529976925780921582316389471511807952999491055213710848) (packedMap 4291346900403284655861908017424091484484955181311227005258585938340678077197019169710940198440799057493308073595599602769236207191908921328664216767129654980091954144451571122271832938952660390481252343255867848865822128437754581858780006806706728182928428023747869612863823236450827675918933623669421570312023110399882016904820430556408301331686084961437973004824845654100253600969826819368143435145026278405067455740507189386921908439406730729152252909427779301417259695009736075861485121261580793612499647001562430263933065816950894022198580543076379945304771663646182465505721985288128560000910149396764897311695428054819319485720080989694833507710056790365012113468490251655301047286567529976925780921582316389471511807952999491055213710848)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem y_table : inclusion y = yTable := by
  change evalWord ![aPerm, bPerm, bPerm⁻¹] yWord = yTable
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem y_sq : y ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private def zWord : List (Fin 3) := [2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2]
private def z : Carrier := evalWord ![a,b,b⁻¹] zWord
private def zTable : Equiv.Perm (Fin 275) :=
  tablePerm (packedMap 4989170036413348035933770037778319373798884554604341776839198538000996827108345452058123272572146046288180796607600508064321483292240654018550133609957820901566626783818197682991267452516915403948216761902093965320500878447845502202575109550156943287461397623673451650516764572770159922796216009067722454258703709058367250959478579887560730763209800544347670057706341721137942412197177031126508690002835981746131206244441659044172523327771155945471366512848971102311020037172056712995036761972029342115234522179084481144641341084565966334451236888957579099594366907573089934163865970543787084783470607840514466338082318187113901241980097552950197487482352914783940718587209544381820631066335633928340592489294505169489682744578807733045293744640) (packedMap 4989170036413348035933770037778319373798884554604341776839198538000996827108345452058123272572146046288180796607600508064321483292240654018550133609957820901566626783818197682991267452516915403948216761902093965320500878447845502202575109550156943287461397623673451650516764572770159922796216009067722454258703709058367250959478579887560730763209800544347670057706341721137942412197177031126508690002835981746131206244441659044172523327771155945471366512848971102311020037172056712995036761972029342115234522179084481144641341084565966334451236888957579099594366907573089934163865970543787084783470607840514466338082318187113901241980097552950197487482352914783940718587209544381820631066335633928340592489294505169489682744578807733045293744640)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem z_table : inclusion z = zTable := by
  change evalWord ![aPerm, bPerm, bPerm⁻¹] zWord = zTable
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem z_sq : z ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, z_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem xy : Commute x y := by
  apply inclusion_injective
  rw [map_mul, map_mul, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem xz : Commute x z := by
  apply inclusion_injective
  rw [map_mul, map_mul, x_table, z_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem yz : Commute y z := by
  apply inclusion_injective
  rw [map_mul, map_mul, y_table, z_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private def embedding : E →* Carrier := tripleHom x y z x_sq y_sq z_sq xy xz yz
private theorem image (a : E) :
    inclusion (embedding a) =
      (if a.1.1 = 1 then 1 else xTable) *
      (if a.1.2 = 1 then 1 else yTable) *
      (if a.2 = 1 then 1 else zTable) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
  split_ifs <;> simp [x_table, y_table, z_table]
private theorem detected : ∀ a : E,
    ((if a.1.1 = 1 then 1 else xTable) *
      (if a.1.2 = 1 then 1 else yTable) *
      (if a.2 = 1 then 1 else zTable)) 2 = 2 → a = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply detected
  have he := congrArg (fun g => inclusion g 2) ha
  simpa only [image, map_one, Equiv.Perm.one_apply] using he
/-- The literal McL carrier has an elementary subgroup of order eight. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Carrier := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ a : E, a ^ 2 = 1)
  · simp [E, C2, Nat.card_eq_fintype_card]
  · exact embedding_injective
end Sporadic.LeechRelated.McL.TwoRank
