module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.Witnesses
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.Coverage
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# An upper bound for the entire representative fixed subgroup

An element fixing the point 0 has normal form `rep1 * rep2 * rep3`.
Commuting with the displayed involution at points 1, 2, 3 leaves at most
24 possibilities. A compact, kernel-checked decoder proves that bound;
orbit--stabilizer on the fourteen fixed points then bounds the entire fixed
subgroup by 14·24 = 336. No assertion that the two chosen elements generate
the fixed subgroup is used here.

Source: the checked ATLAS J₂ normal forms in `SecondOrbits.Coverage`;
GLS3 Table 5.3g, class 2C; Aschbacher--Smith 16.1.5(8), p.1172.
The packed witnesses only accelerate kernel reduction; they are not axioms.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open GeneratorPair ExceptionalParabolics GeneratorPair.SecondOrbitCertificate

private def rawMap (n p : Nat) : Nat := (n >>> (7*p)) % 128 % 100

private def rawNormal (i : Index) (p : Nat) : Nat :=
  rawMap (rep0Code i.1) (rawMap (rep1Code i.2.1)
    (rawMap (rep2Code i.2.2.1) (rawMap (rep3Code i.2.2.2) p)))

private def outerCode : Nat := 1857439445384269109468976444126678193941844942289369177058064008258798481882774277783000724688826383095680818570801574287800319093145900863073690913744732557567702232652118335285771056395830527514873235564332032

private def tailIndex (j : Fin 24) : Fin 63 × Fin 24 × Fin 4 :=
  let n := (6130137090950705638906787107134554392644510579129584391154377486129360992177615893278087471104 >>> (13*j.val)) % 8192
  (⟨n/96 % 63, Nat.mod_lt _ (by decide)⟩,
   ⟨n/4 % 24, Nat.mod_lt _ (by decide)⟩,
   ⟨n%4, Nat.mod_lt _ (by decide)⟩)

private def secondDecode (j : Fin 63) : Fin 24 :=
  ⟨((47976315119908610986152849140790942693500152558117616475830313564079108400676081336044602000384 >>> (5*j.val)) % 32) % 24, Nat.mod_lt _ (by decide)⟩

private def commuteTest (i : Index) : Prop :=
  rawNormal i 8 = rawMap outerCode (rawNormal i 1) ∧
  rawNormal i 28 = rawMap outerCode (rawNormal i 2) ∧
  rawNormal i 22 = rawMap outerCode (rawNormal i 3)

private instance (i : Index) : Decidable (commuteTest i) := inferInstanceAs (Decidable (_ ∧ _))

private def checkTail : Bool :=
  checkFin fun j : Fin 63 => checkFin fun k : Fin 24 => checkFin fun l : Fin 4 =>
    decide (commuteTest (0, j, k, l) → tailIndex (secondDecode j) = (j, k, l))

set_option maxRecDepth 100000 in
private theorem tail_checked : checkTail = true := by decide +kernel

private theorem tail_check (j : Fin 63) (k : Fin 24) (l : Fin 4)
    (h : commuteTest (0, j, k, l)) : tailIndex (secondDecode j) = (j, k, l) := by
  have hj := allFin (fun j : Fin 63 => (checkFin fun k : Fin 24 => checkFin fun l : Fin 4 =>
    decide (commuteTest (0,j,k,l) → tailIndex (secondDecode j) = (j,k,l))) = true)
    (by simpa only [checkTail, Bool.decide_eq_true] using tail_checked) j
  have hk := allFin (fun k : Fin 24 => (checkFin fun l : Fin 4 =>
    decide (commuteTest (0,j,k,l) → tailIndex (secondDecode j) = (j,k,l))) = true)
    (by simpa only [Bool.decide_eq_true] using hj) k
  exact allFin (fun l : Fin 4 => commuteTest (0,j,k,l) →
    tailIndex (secondDecode j) = (j,k,l)) hk l h

private theorem normal_val (i : Index) (p : Fin 100) :
    (normalForm i p).val = rawNormal i p.val := rfl

private theorem outer_val : ∀ p : Fin 100, (involution p).val = rawMap outerCode p.val := by
  apply allFin
  decide +kernel

private theorem fixed_test (g : involutionAut.fixedSubgroup) (i : Index)
    (hi : normalForm i = inclusion g.val) : commuteTest i := by
  have hh (p : Fin 100) := congrArg Fin.val (fixed_commutes g p).symm
  rw [← hi] at hh
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change (normalForm i 8).val = (involution (normalForm i 1)).val at h1
  change (normalForm i 28).val = (involution (normalForm i 2)).val at h2
  change (normalForm i 22).val = (involution (normalForm i 3)).val at h3
  simp only [normal_val, outer_val] at h1 h2 h3
  exact ⟨h1,h2,h3⟩

private theorem normal_zero : ∀ i : Index, normalForm i 0 = rep0 i.1 0 := by
  have h1 : ∀ j : Fin 63, rep1 j 0 = 0 := by apply allFin; decide +kernel
  have h2 : ∀ j : Fin 24, rep2 j 0 = 0 := by apply allFin; decide +kernel
  have h3 : ∀ j : Fin 4, rep3 j 0 = 0 := by apply allFin; decide +kernel
  intro i
  simp only [normalForm, Equiv.Perm.mul_apply, h1, h2, h3]

private theorem rep0_zero : ∀ j : Fin 100, rep0 j 0 = 0 → j = 0 := by
  apply allFin
  decide +kernel

private noncomputable def fixedIndex (g : involutionAut.fixedSubgroup) : Index :=
  Classical.choose (normalForm_cover g.val)

private theorem fixedIndex_spec (g : involutionAut.fixedSubgroup) :
    normalForm (fixedIndex g) = inclusion g.val := (Classical.choose_spec (normalForm_cover g.val)).symm

local instance : MulAction involutionAut.fixedSubgroup (Fin 14) :=
  MulAction.compHom (Fin 14) action

private theorem stabilizer_fixes (g : MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) :
    inclusion g.val.val 0 = 0 := by
  have h : action g.val 0 = 0 := g.property
  have hp := action_point g.val 0
  rw [h] at hp
  exact hp.symm

private theorem stabilizer_index_first (g : MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) :
    (fixedIndex g.val).1 = 0 := by
  apply rep0_zero
  rw [← normal_zero, fixedIndex_spec]
  exact stabilizer_fixes g

private theorem stabilizer_recover (g : MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) :
    (0, tailIndex (secondDecode (fixedIndex g.val).2.1)) = fixedIndex g.val := by
  have hfirst := stabilizer_index_first g
  have hrest := fixed_test g.val (fixedIndex g.val) (fixedIndex_spec g.val)
  have he : ((0 : Fin 100), (fixedIndex g.val).2) = fixedIndex g.val :=
    Prod.ext hfirst.symm rfl
  have ht := tail_check (fixedIndex g.val).2.1 (fixedIndex g.val).2.2.1
    (fixedIndex g.val).2.2.2 (he.symm ▸ hrest)
  rw [ht, ← hfirst]

private theorem card_stabilizer_le :
    Nat.card (MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) ≤ 24 := by
  let f : MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14) → Fin 24 :=
    fun g => secondDecode (fixedIndex g.val).2.1
  have hf : Function.Injective f := by
    intro g h heq
    have hi := congrArg (fun p : Fin 24 => ((0 : Fin 100), tailIndex p)) heq
    change (0, tailIndex (secondDecode (fixedIndex g.val).2.1)) =
      (0, tailIndex (secondDecode (fixedIndex h.val).2.1)) at hi
    rw [stabilizer_recover, stabilizer_recover] at hi
    apply Subtype.ext
    apply Subtype.ext
    apply inclusion_injective
    rw [← fixedIndex_spec, ← fixedIndex_spec, hi]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- A bound for all fixed elements, obtained from the actual point stabilizer. -/
theorem card_fixed_le : Nat.card involutionAut.fixedSubgroup ≤ 336 := by
  have ho : Nat.card (MulAction.orbit involutionAut.fixedSubgroup (0 : Fin 14)) ≤ 14 := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      (Subtype.val : MulAction.orbit involutionAut.fixedSubgroup (0 : Fin 14) → Fin 14)
      Subtype.val_injective
  calc
    Nat.card involutionAut.fixedSubgroup = Nat.card
        (MulAction.orbit involutionAut.fixedSubgroup (0 : Fin 14) ×
          MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) :=
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup involutionAut.fixedSubgroup
        (0 : Fin 14)).symm
    _ = Nat.card (MulAction.orbit involutionAut.fixedSubgroup (0 : Fin 14)) *
        Nat.card (MulAction.stabilizer involutionAut.fixedSubgroup (0 : Fin 14)) := Nat.card_prod _ _
    _ ≤ 14 * 24 := Nat.mul_le_mul ho card_stabilizer_le
    _ = 336 := rfl

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
