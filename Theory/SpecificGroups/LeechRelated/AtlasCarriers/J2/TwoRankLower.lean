module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.WordSubgroup
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# An elementary eight in the actual J₂ permutation carrier

Three words in the published ATLAS generators are involutions and commute.
Their eight products move a marked point independently. The word identities
and permutation relations are checked on the actual hundred-point carrier;
GAP is used only to discover the words, not as a mathematical premise.
Source: ATLAS J2G1-p100B0; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Sporadic.LeechRelated.J2.TwoRank
open GeneratorPair Theory.GroupTheory
set_option maxRecDepth 20000

private def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)
private theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi
private def packedMap (v : Nat) (i : Fin 100) : Fin 100 :=
  ⟨(v >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def fastA : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547) (packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)

private theorem tableA_fast : tableA = fastA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def fastB : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 3234967701574023288017704270913789399548845676982065206373928870228913752386975839948414443758577378205229365791802719998856417312117905715024748407215049785228781853510609863692219811450715825262485969147626773) (packedMap 3377862216939204608209019933455681426219024363596881756892669536352030827785925351345362563460844105849526589246761354822075856259740605599629990671129056314103711580268098197814694108667979975332570640941909071)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)

private theorem tableB_fast : tableB = fastB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

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

private def xWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]
private def x : Carrier := evalWord ![a,b,b⁻¹] xWord
private def xTable : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 454416606253691057018871383465857075101002599417482171154296771944991787470839205585989492771490077650016320367022436765162200891589853341790763205852098255542646508517737253003649574955072594705965332137503791) (packedMap 454416606253691057018871383465857075101002599417482171154296771944991787470839205585989492771490077650016320367022436765162200891589853341790763205852098255542646508517737253003649574955072594705965332137503791)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem x_table : inclusion x = xTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] xWord = xTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem x_sq : x ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private def yWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0]
private def y : Carrier := evalWord ![a,b,b⁻¹] yWord
private def yTable : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 1443350153861425575071604825441116369716739560747265366741003785334979380805824735557418693108811106240572069853103084999189892069787167977215870788769622914662199855108018622543723732271884075508375538732426880) (packedMap 1443350153861425575071604825441116369716739560747265366741003785334979380805824735557418693108811106240572069853103084999189892069787167977215870788769622914662199855108018622543723732271884075508375538732426880)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem y_table : inclusion y = yTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] yWord = yTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem y_sq : y ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel
private def zWord : List (Fin 3) := [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2]
private def z : Carrier := evalWord ![a,b,b⁻¹] zWord
private def zTable : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 2758269291152170231215452096224784898267592889913870994445564188681398514339334322478166884387009379758591396387279625247996116263378491362263014069406218678806879334377371943018738678219497771465443370110346624) (packedMap 2758269291152170231215452096224784898267592889913870994445564188681398514339334322478166884387009379758591396387279625247996116263378491362263014069406218678806879334377371943018738678219497771465443370110346624)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem z_table : inclusion z = zTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] zWord = zTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
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
      (if a.2 = 1 then 1 else zTable)) 1 = 1 → a = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply detected
  have he := congrArg (fun g => inclusion g 1) ha
  simpa only [image, map_one, Equiv.Perm.one_apply] using he
/-- The literal J₂ carrier has an elementary subgroup of order eight. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Carrier := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ a : E, a ^ 2 = 1)
  · simp [E, C2, Nat.card_eq_fintype_card]
  · exact embedding_injective
end Sporadic.LeechRelated.J2.TwoRank
