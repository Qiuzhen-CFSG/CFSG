module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.GroupTheory.WordSubgroup
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Explicit candidates for the HS Sylow-containing two-local cover

Six words in the exact degree-100 ATLAS generators specify a candidate
Sylow subgroup and three nested elementary abelian two-subgroups. Packed
permutations are identified with those words by kernel-checked identities.
The elementary subgroups really lie in the candidate Sylow subgroup.

Source: Aschbacher–Smith, condition E, printed pp.3–4; GLS volume 3,
Table 5.3m, printed p.274. GAP discovery data and an encoding script are
retained in `EvenLocalCandidates/source/`. GAP is not a proof oracle.

This module does not assert that the candidate subgroup is Sylow, that the
three elementary subgroups exhaust its normal elementary subgroups, or that
their ambient normalizers have characteristic two. Those are separate model
obligations; no local-structure certificate is assumed here.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates
open Subgroup

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

private theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

private def aMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def aInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem aLeft : ∀ i, aInvMap (aMap i) = i := by
  apply allFin
  decide +kernel

private def aPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm aMap aInvMap aLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin aLeft)

private theorem aPerm_eq_generator : aPerm = generatorA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def a : Carrier := ⟨aPerm, aPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def bMap (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def bInvMap (i : Fin 100) : Fin 100 :=
  ⟨(852881488533531112336995551220226122361210863663080587750664607485875722147280441807057556633165462885474069200795003754517913050689892735891088239319177696223676845175972313037682728934689958756512102884170325 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem bLeft : ∀ i, bInvMap (bMap i) = i := by
  apply allFin
  decide +kernel

private def bPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm bMap bInvMap bLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin bLeft)

private theorem bPerm_eq_generator : bPerm = generatorB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def b : Carrier := ⟨bPerm, bPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

def s0Map (i : Fin 100) : Fin 100 :=
  ⟨(4095557383497070696779903571476665225518081543405432243328487047762726791453587274265970130516223422473241849601580374919172652531124262275777534893770803521910206543063804260440457101384061910069248211009175693 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def s0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(4095557383497070696779903571476665225518081543405432243328487047762726791453587274265970130516223422473241849601580374919172652531124262275777534893770803521910206543063804260440457101384061910069248211009175693 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem s0Left : ∀ i, s0InvMap (s0Map i) = i := by
  apply allFin
  decide +kernel

private def s0Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm s0Map s0InvMap s0Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin s0Left)

private def s0Word : Carrier := b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * b * (a ^ 2) * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * (b ^ 2) * a⁻¹

private theorem s0Perm_eq_word : s0Perm = (s0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def s0 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm s0Map s0InvMap (by exact s0Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin s0Left),
    by
      change s0Perm ∈ generated
      rw [s0Perm_eq_word]
      exact s0Word.property⟩

def s1Map (i : Fin 100) : Fin 100 :=
  ⟨(1797500939867120030829988023855123100301053793670848400830861093983690684911251372946091991115508271420169088233759069192873789167193890897055915918510344905121837166818484715094749806894442106339549569517715584 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def s1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1797500939867120030829988023855123100301053793670848400830861093983690684911251372946091991115508271420169088233759069192873789167193890897055915918510344905121837166818484715094749806894442106339549569517715584 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem s1Left : ∀ i, s1InvMap (s1Map i) = i := by
  apply allFin
  decide +kernel

private def s1Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm s1Map s1InvMap s1Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin s1Left)

private def s1Word : Carrier := (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * (a⁻¹ ^ 2) * b * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a * (b⁻¹ ^ 2) * a * b * a * b * a * (b⁻¹ ^ 2) * a * b * a * b⁻¹ * a * (b ^ 2) * a * (b⁻¹ ^ 4) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b ^ 2) * a * b⁻¹ * a * (b ^ 2) * a * (b⁻¹ ^ 2)

private theorem s1Perm_eq_word : s1Perm = (s1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def s1 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm s1Map s1InvMap (by exact s1Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin s1Left),
    by
      change s1Perm ∈ generated
      rw [s1Perm_eq_word]
      exact s1Word.property⟩

def s2Map (i : Fin 100) : Fin 100 :=
  ⟨(1092360375748203114993258622667650980588093157732533090094115930361864199645407237223213912104115898610540646471381388910475276213376924136936715322689008714335777258724215683087206280978848336679669998517523380 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def s2InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1335410200555437304055058816916506865123627756657522879044556548407488195736881709814274490065498191529805327713081945804138539578950859937751499125307105302537493559115204614799950271411701690682981364619322292 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem s2Left : ∀ i, s2InvMap (s2Map i) = i := by
  apply allFin
  decide +kernel

private def s2Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm s2Map s2InvMap s2Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin s2Left)

private def s2Word : Carrier := b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 3) * a⁻¹ * (b ^ 2) * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a * (b⁻¹ ^ 3) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 3) * a⁻¹ * b * a⁻¹

private theorem s2Perm_eq_word : s2Perm = (s2Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def s2 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm s2Map s2InvMap (by exact s2Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin s2Left),
    by
      change s2Perm ∈ generated
      rw [s2Perm_eq_word]
      exact s2Word.property⟩

def e0Map (i : Fin 100) : Fin 100 :=
  ⟨(3026984416623807514037421486037685165332139105862958415717555544756392779160369263474112799204921920550971277239182540036866654321299324877247599757941908561351206062958912081397510383685975094968042824153466752 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def e0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3026984416623807514037421486037685165332139105862958415717555544756392779160369263474112799204921920550971277239182540036866654321299324877247599757941908561351206062958912081397510383685975094968042824153466752 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem e0Left : ∀ i, e0InvMap (e0Map i) = i := by
  apply allFin
  decide +kernel

private def e0Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm e0Map e0InvMap e0Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin e0Left)

private def e0Word : Carrier := (s2⁻¹ ^ 2)

private theorem e0Perm_eq_word : e0Perm = (e0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def e0 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm e0Map e0InvMap (by exact e0Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin e0Left),
    by
      change e0Perm ∈ generated
      rw [e0Perm_eq_word]
      exact e0Word.property⟩

theorem e0_eq_word : e0 = (s2⁻¹ ^ 2) :=
  Subtype.ext e0Perm_eq_word

def e1Map (i : Fin 100) : Fin 100 :=
  ⟨(1771767769005599571029866413165295060722796179525516721745553255105757235997357221470258319563509761136970001256346735296341176647649777639740238967440879283481128362527398045650472985349424824397992188724543872 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def e1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1771767769005599571029866413165295060722796179525516721745553255105757235997357221470258319563509761136970001256346735296341176647649777639740238967440879283481128362527398045650472985349424824397992188724543872 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem e1Left : ∀ i, e1InvMap (e1Map i) = i := by
  apply allFin
  decide +kernel

private def e1Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm e1Map e1InvMap e1Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin e1Left)

private def e1Word : Carrier := s0⁻¹ * s1⁻¹ * s0⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹ * s1⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹

private theorem e1Perm_eq_word : e1Perm = (e1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def e1 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm e1Map e1InvMap (by exact e1Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin e1Left),
    by
      change e1Perm ∈ generated
      rw [e1Perm_eq_word]
      exact e1Word.property⟩

theorem e1_eq_word : e1 = s0⁻¹ * s1⁻¹ * s0⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹ * s1⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹ :=
  Subtype.ext e1Perm_eq_word

def e2Map (i : Fin 100) : Fin 100 :=
  ⟨(1439454015074357110549840806739116828815883856340695269732636899676769822773197138262638251935753679206373112901598423110748848841494661648195348398597301329540558184794512001248254991452080867640584082640897805 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def e2InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1439454015074357110549840806739116828815883856340695269732636899676769822773197138262638251935753679206373112901598423110748848841494661648195348398597301329540558184794512001248254991452080867640584082640897805 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem e2Left : ∀ i, e2InvMap (e2Map i) = i := by
  apply allFin
  decide +kernel

private def e2Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm e2Map e2InvMap e2Left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin e2Left)

private def e2Word : Carrier := s0⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹

private theorem e2Perm_eq_word : e2Perm = (e2Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- An explicit word in the defining ATLAS carrier. -/
def e2 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm e2Map e2InvMap (by exact e2Left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin e2Left),
    by
      change e2Perm ∈ generated
      rw [e2Perm_eq_word]
      exact e2Word.property⟩

theorem e2_eq_word : e2 = s0⁻¹ * s2⁻¹ * s0⁻¹ * s2⁻¹ :=
  Subtype.ext e2Perm_eq_word

/-- Three explicit generators of the candidate Sylow subgroup. -/
def sylowGenerator : Fin 3 → Carrier := ![s0, s1, s2]

/-- The subgroup whose Sylow order and intrinsic catalogue remain to be certified. -/
def subgroup : Subgroup Carrier := closure (Set.range sylowGenerator)

/-- Three commuting involutions used for the elementary candidates. -/
def elementaryGenerator : Fin 3 → Carrier := ![e0, e1, e2]

/-- Successive initial segments generate the three elementary candidates. -/
def elementary (i : Fin 3) : Subgroup Carrier :=
  closure (elementaryGenerator '' {j | j ≤ i})

/-- The full normalizers in the exact ATLAS carrier. -/
def localGroup (i : Fin 3) : Subgroup Carrier :=
  normalizer (elementary i : Set Carrier)

private theorem sylowGenerator_mem (i : Fin 3) : sylowGenerator i ∈ subgroup :=
  subset_closure ⟨i, rfl⟩

private theorem elementaryGenerator_mem (i : Fin 3) : elementaryGenerator i ∈ subgroup := by
  have hs0 : s0 ∈ subgroup := sylowGenerator_mem 0
  have hs1 : s1 ∈ subgroup := sylowGenerator_mem 1
  have hs2 : s2 ∈ subgroup := sylowGenerator_mem 2
  fin_cases i
  · change e0 ∈ subgroup
    rw [e0_eq_word]
    exact subgroup.pow_mem (subgroup.inv_mem hs2) 2
  · change e1 ∈ subgroup
    rw [e1_eq_word]
    repeat first | apply subgroup.mul_mem | exact subgroup.inv_mem hs0 |
      exact subgroup.inv_mem hs1 | exact subgroup.inv_mem hs2
  · change e2 ∈ subgroup
    rw [e2_eq_word]
    repeat first | apply subgroup.mul_mem | exact subgroup.inv_mem hs0 |
      exact subgroup.inv_mem hs2

/-- All three candidates are actual subgroups of the same candidate Sylow subgroup. -/
theorem elementary_le_subgroup (i : Fin 3) : elementary i ≤ subgroup := by
  apply (closure_le _).mpr
  rintro x ⟨j, _, rfl⟩
  exact elementaryGenerator_mem j

private theorem elementaryGenerator_pow (i : Fin 3) : elementaryGenerator i ^ 2 = 1 := by
  have h : ∀ j : Fin 3, ∀ x : Fin 100,
      (elementaryGenerator j ^ 2 : Equiv.Perm (Fin 100)) x = x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

private theorem elementaryGenerator_commute (i j : Fin 3) :
    elementaryGenerator i * elementaryGenerator j = elementaryGenerator j * elementaryGenerator i := by
  have h : ∀ i j : Fin 3, ∀ x : Fin 100,
      (elementaryGenerator i * elementaryGenerator j : Equiv.Perm (Fin 100)) x =
        (elementaryGenerator j * elementaryGenerator i : Equiv.Perm (Fin 100)) x := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j))

/-- The candidate elementary subgroups have exponent dividing two. -/
theorem elementary_isElementaryAbelian (i : Fin 3) : IsElementaryAbelian 2 (elementary i) := by
  change IsElementaryAbelian 2 (closure (elementaryGenerator '' {j | j ≤ i}))
  let : IsMulCommutative (closure (elementaryGenerator '' {j | j ≤ i})) := Subgroup.isMulCommutative_closure (by
    rintro x ⟨j, _, rfl⟩ y ⟨k, _, rfl⟩
    exact elementaryGenerator_commute j k)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨j, _, rfl⟩
  exact elementaryGenerator_pow j

/-- Each candidate is a two-group, without any ambient order assumption. -/
theorem elementary_isPGroup (i : Fin 3) : IsPGroup 2 (elementary i) := by
  let := elementary_isElementaryAbelian i
  exact IsElementaryAbelian.isPGroup 2 (elementary i)

private theorem e0_ne_one : e0 ≠ 1 := by
  intro h
  have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 1) h
  have hn : (e0 : Equiv.Perm (Fin 100)) 1 ≠ 1 := by decide +kernel
  exact hn he

/-- All three candidate elementary subgroups are nontrivial. -/
theorem elementary_ne_bot (i : Fin 3) : elementary i ≠ ⊥ := by
  intro h
  have he : e0 ∈ elementary i := subset_closure ⟨0, by simp, rfl⟩
  rw [h, mem_bot] at he
  exact e0_ne_one he

end Sporadic.LeechRelated.HS.EvenLocalCandidates
