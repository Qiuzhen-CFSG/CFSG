module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.Data
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Checked words and the subgroup lower bound

Every table is compared pointwise with its word in the actual ATLAS generators.
The 128 subgroup words have strictly increasing codes for their images of
points 0 and 1. Thus they are distinct elements of `Seed.s`, giving the only
subgroup cardinality bound needed by the cover argument.

Source: the fixed words documented in `Data`; Aschbacher–Smith, printed p.511,
and GLS3 Table 5.3g. All finite comparisons use kernel reduction.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Theory.GroupTheory

def seedMap (i : Fin 7) : Fin 100 → Fin 100 := packedMap seedCodes[i.val]!
def representativeMap (i : Fin 72) : Fin 100 → Fin 100 :=
  packedMap representativeCodes[i.val]!
def wordMap {n : Nat} (gen : Fin n → Fin 100 → Fin 100)
    (w : List (Fin n)) (x : Fin 100) : Fin 100 := w.foldr (fun i y => gen i y) x
def subgroupMap (i : Fin 128) : Fin 100 → Fin 100 :=
  wordMap seedMap subgroupWords[i.val]!
def subgroupElement (i : Fin 128) : Carrier :=
  evalWord Seed.sGenerator subgroupWords[i.val]!

theorem inclusion_word_apply {n : Nat} (gen : Fin n → Carrier)
    (maps : Fin n → Fin 100 → Fin 100)
    (h : ∀ i x, inclusion (gen i) x = maps i x) (w : List (Fin n)) (x : Fin 100) :
    inclusion (evalWord gen w) x = wordMap maps w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [evalWord, map_mul, Equiv.Perm.mul_apply, ih, h,
      wordMap, List.foldr_cons]

def localMaps (i : Fin 3) : Fin 100 → Fin 100 :=
  packedMap (match i.val with
  | 0 => 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547
  | 1 => 3234967701574023288017704270913789399548845676982065206373928870228913752386975839948414443758577378205229365791802719998856417312117905715024748407215049785228781853510609863692219811450715825262485969147626773
  | _ => 3377862216939204608209019933455681426219024363596881756892669536352030827785925351345362563460844105849526589246761354822075856259740605599629990671129056314103711580268098197814694108667979975332570640941909071)

set_option maxRecDepth 100000 in
theorem localMaps_check : ∀ i x,
    ![tableAValues, tableBValues, tableBInvValues] i x = localMaps i x := by
  decide +kernel

theorem localWord_apply (w : List (Fin 3)) (x : Fin 100) :
    inclusion (Seed.localWord w) x = wordMap localMaps w x := by
  apply inclusion_word_apply
  intro i y
  rw [← localMaps_check]
  fin_cases i
  · change generatorA y = tableAValues y
    rw [generatorA_eq_table]
    rfl
  · change generatorB y = tableBValues y
    rw [generatorB_eq_table]
    rfl
  · change (generatorB⁻¹) y = tableBInvValues y
    rw [generatorB_eq_table]
    rfl

set_option maxRecDepth 100000 in
theorem seedMap_check : ∀ i x, wordMap localMaps (Seed.sWords i) x = seedMap i x := by
  apply allFin
  decide +kernel

theorem seedGenerator_apply (i : Fin 7) (x : Fin 100) :
    inclusion (Seed.sGenerator i) x = seedMap i x := by
  rw [Seed.sGenerator, localWord_apply, seedMap_check]

private def representativeBlockIndex (a : Fin 9) (b : Fin 8) : Fin 72 :=
  ⟨a.val * 8 + b.val, by omega⟩

set_option maxRecDepth 100000 in
private theorem representative_check_0 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 0 b).val]! x =
      representativeMap (representativeBlockIndex 0 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_1 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 1 b).val]! x =
      representativeMap (representativeBlockIndex 1 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_2 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 2 b).val]! x =
      representativeMap (representativeBlockIndex 2 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_3 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 3 b).val]! x =
      representativeMap (representativeBlockIndex 3 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_4 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 4 b).val]! x =
      representativeMap (representativeBlockIndex 4 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_5 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 5 b).val]! x =
      representativeMap (representativeBlockIndex 5 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_6 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 6 b).val]! x =
      representativeMap (representativeBlockIndex 6 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_7 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 7 b).val]! x =
      representativeMap (representativeBlockIndex 7 b) x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem representative_check_8 : ∀ b : Fin 8, ∀ x,
    wordMap localMaps representativeWords[(representativeBlockIndex 8 b).val]! x =
      representativeMap (representativeBlockIndex 8 b) x := by
  apply allFin
  decide +kernel

theorem representativeMap_check (i : Fin 72) (x : Fin 100) :
    wordMap localMaps representativeWords[i.val]! x = representativeMap i x := by
  let a : Fin 9 := ⟨i.val / 8, by omega⟩
  let b : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have hi : representativeBlockIndex a b = i := by
    apply Fin.ext
    dsimp [representativeBlockIndex, a, b]
    omega
  rw [← hi]
  have h (j : Fin 9) : ∀ k y,
      wordMap localMaps representativeWords[(representativeBlockIndex j k).val]! y =
        representativeMap (representativeBlockIndex j k) y := by
    fin_cases j
    · exact representative_check_0
    · exact representative_check_1
    · exact representative_check_2
    · exact representative_check_3
    · exact representative_check_4
    · exact representative_check_5
    · exact representative_check_6
    · exact representative_check_7
    · exact representative_check_8
  exact h a b x

theorem representative_apply (i : Fin 72) (x : Fin 100) :
    inclusion (representative i) x = representativeMap i x := by
  rw [representative, localWord_apply, representativeMap_check]

set_option maxRecDepth 100000 in
theorem subgroupElement_apply (i : Fin 128) (x : Fin 100) :
    inclusion (subgroupElement i) x = subgroupMap i x :=
  inclusion_word_apply Seed.sGenerator seedMap seedGenerator_apply subgroupWords[i.val]! x

theorem subgroupElement_mem (i : Fin 128) : subgroupElement i ∈ Seed.s := by
  apply SubgroupEnumeration.evalWord_mem
  intro j
  exact Subgroup.subset_closure ⟨j, rfl⟩

def subgroupKey (i : Fin 128) : Nat :=
  (subgroupMap i 0).val * 100 + (subgroupMap i 1).val

set_option maxRecDepth 100000 in
theorem subgroupKey_strictMono : StrictMono subgroupKey := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_seed_lower : 128 ≤ Nat.card Seed.s := by
  let f (i : Fin 128) : Seed.s := ⟨subgroupElement i, subgroupElement_mem i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply subgroupKey_strictMono.injective
    have hv : subgroupElement i = subgroupElement j := congrArg Subtype.val h
    have h0 := congrArg (fun g : Carrier => (inclusion g 0).val) hv
    have h1 := congrArg (fun g : Carrier => (inclusion g 1).val) hv
    simpa only [subgroupElement_apply, subgroupKey] using congrArg₂ (fun a b => a * 100 + b) h0 h1
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
