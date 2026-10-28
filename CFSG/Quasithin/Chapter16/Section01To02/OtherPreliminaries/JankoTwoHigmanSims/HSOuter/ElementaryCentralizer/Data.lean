module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base

/-!
# Word witnesses for the elementary outer HS centralizer

Four commuting kernel candidates and five centralizer generators are specified
by their actual degree-100 permutations and words in the two ATLAS generators.
Every word identity and commutation with the fixed outer involution is checked
in Lean's kernel. No centralizer order or exhaustive generation is assumed.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
class 2C. Reproducible GAP discovery and the word orientation convention are
retained in `source/`. These are witnesses in the existing HS carrier.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer
open Sporadic.LeechRelated.HS Subgroup
open Sporadic.LeechRelated.HS.OrderCertificate (allFin p0 p1 a_eq_generator b_eq_generator)

set_option maxRecDepth 100000
set_option Elab.async false

/-- The centralizer inside the exact HS carrier. -/
abbrev C := permutationCentralizer elementaryPermutation

private def a : Carrier := ⟨p0, a_eq_generator.symm ▸ subset_closure (by simp)⟩
private def b : Carrier := ⟨p1, b_eq_generator.symm ▸ subset_closure (by simp)⟩

def q0Map (x : Fin 100) : Fin 100 :=
  ⟨(1675330314779068693714700583707532259400964940572826544374136458541059555826767577028168303556712201510925843888055581302324992243499380321915174039557177065862810606840795197114891006442013699487582075690582206 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem q0_left : ∀ x, q0Map (q0Map x) = x := by
  apply allFin
  decide +kernel

private def q0Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q0Map q0Map q0_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q0_left)

private def q0Word : Carrier := a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b * (a⁻¹ ^ 2) * (b⁻¹ ^ 3) * a * b * a * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b ^ 3) * a * b * a * b * a * (b⁻¹ ^ 2) * a * b * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 3) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b⁻¹

private theorem q0_word : q0Perm = (q0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def q0 : C := ⟨⟨Theory.GroupTheory.tablePerm q0Map q0Map
    (by exact q0_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q0_left), by
  change q0Perm ∈ generated
  rw [q0_word]
  exact q0Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * q0Perm = q0Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def q1Map (x : Fin 100) : Fin 100 :=
  ⟨(1921879842883680949394128876243423382333256415507645276790598025603170938348326535361137128103922286173671761286909234921920560599852174049673354920195896268176644635887972330192536535620991493104291641758494494 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem q1_left : ∀ x, q1Map (q1Map x) = x := by
  apply allFin
  decide +kernel

private def q1Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q1Map q1Map q1_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q1_left)

private def q1Word : Carrier := (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b ^ 2) * a * b * a * b * a * b * a * (b⁻¹ ^ 2) * a * b * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b⁻¹

private theorem q1_word : q1Perm = (q1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def q1 : C := ⟨⟨Theory.GroupTheory.tablePerm q1Map q1Map
    (by exact q1_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q1_left), by
  change q1Perm ∈ generated
  rw [q1_word]
  exact q1Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * q1Perm = q1Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def q2Map (x : Fin 100) : Fin 100 :=
  ⟨(483625921203830520314363254102132153964433599928892181669812847335194078788807674961787853807643477101519111465740631651512432536496269379695589852617100932777346852069525823366477458673094097429718896412110615 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem q2_left : ∀ x, q2Map (q2Map x) = x := by
  apply allFin
  decide +kernel

private def q2Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q2Map q2Map q2_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q2_left)

private def q2Word : Carrier := b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 4) * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2)

private theorem q2_word : q2Perm = (q2Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def q2 : C := ⟨⟨Theory.GroupTheory.tablePerm q2Map q2Map
    (by exact q2_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q2_left), by
  change q2Perm ∈ generated
  rw [q2_word]
  exact q2Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * q2Perm = q2Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def q3Map (x : Fin 100) : Fin 100 :=
  ⟨(935665421067161539114550600214174953050318104797167433249222864111937910019260773096276025881393980988181514347013943429142299099853983321340991830744532202059188139278615345794789719095453037589656567794275857 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem q3_left : ∀ x, q3Map (q3Map x) = x := by
  apply allFin
  decide +kernel

private def q3Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q3Map q3Map q3_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q3_left)

private def q3Word : Carrier := b * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 4) * a * b * a * b * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b⁻¹ * a * b⁻¹ * a * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2)

private theorem q3_word : q3Perm = (q3Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def q3 : C := ⟨⟨Theory.GroupTheory.tablePerm q3Map q3Map
    (by exact q3_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q3_left), by
  change q3Perm ∈ generated
  rw [q3_word]
  exact q3Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * q3Perm = q3Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def c0Map (x : Fin 100) : Fin 100 :=
  ⟨(932143057991537627731039120938127112855207792840755636631935539759564760637564231863074305624172521246038655859438697596406630588527025455362546655292599409067364012029830436213952176835951977935579701304058302 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def c0InvMap (x : Fin 100) : Fin 100 :=
  ⟨(1651613618130063444867853982715731397691246779245365864827494858775051790928228256347229802273637988112130313613296651610154823234640487657451666554687572611077115313144564338984788667306888080686847301493533898 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c0_left : ∀ x, c0InvMap (c0Map x) = x := by
  apply allFin
  decide +kernel

private def c0Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm c0Map c0InvMap c0_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin c0_left)

private def c0Word : Carrier := a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b ^ 3) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * (b ^ 2) * a * (b ^ 2) * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a⁻¹ * (b⁻¹ ^ 3) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 3) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b⁻¹

private theorem c0_word : c0Perm = (c0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def c0 : C := ⟨⟨Theory.GroupTheory.tablePerm c0Map c0InvMap
    (by exact c0_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin c0_left), by
  change c0Perm ∈ generated
  rw [c0_word]
  exact c0Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * c0Perm = c0Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def c1Map (x : Fin 100) : Fin 100 :=
  ⟨(1921926207754755729985725194014766236660315014351165522231817371720862688430045063439046512833119740387074837836437001646926461356598436487972904459330186814401253004395672994383995701139228065566789577980068938 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c1_left : ∀ x, c1Map (c1Map x) = x := by
  apply allFin
  decide +kernel

private def c1Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm c1Map c1Map c1_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin c1_left)

private def c1Word : Carrier := (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a * b⁻¹ * a * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * b * a * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹

private theorem c1_word : c1Perm = (c1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def c1 : C := ⟨⟨Theory.GroupTheory.tablePerm c1Map c1Map
    (by exact c1_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin c1_left), by
  change c1Perm ∈ generated
  rw [c1_word]
  exact c1Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * c1Perm = c1Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def c2Map (x : Fin 100) : Fin 100 :=
  ⟨(544883106487000609279949487116194723688945395007359782619710632629715414589247842855667690485066873233817989591483695303379331807274158665898883351777658419557957798380140434562369273272070298266182684832597965 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def c2InvMap (x : Fin 100) : Fin 100 :=
  ⟨(932144233769483193184123956216193020078346655173718230759077865189138319916696282296209437226653725153354532782247486160922517097137854024765956359547716831991218547080618249392578761673821843915494229578731484 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c2_left : ∀ x, c2InvMap (c2Map x) = x := by
  apply allFin
  decide +kernel

private def c2Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm c2Map c2InvMap c2_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin c2_left)

private def c2Word : Carrier := (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * b * a * (b ^ 2) * a * b * a * b⁻¹ * a * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * (b ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * b⁻¹ * a * (b ^ 3) * a * b * a * b * a * b * a

private theorem c2_word : c2Perm = (c2Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def c2 : C := ⟨⟨Theory.GroupTheory.tablePerm c2Map c2InvMap
    (by exact c2_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin c2_left), by
  change c2Perm ∈ generated
  rw [c2_word]
  exact c2Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * c2Perm = c2Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def c3Map (x : Fin 100) : Fin 100 :=
  ⟨(1711733370374198390056655339832082129218977219187742759325782388718427677918643508921730376995503027879080972243094912534114240284861479839654521020209625963413457362681784526580588742448229437057229139607380927 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def c3InvMap (x : Fin 100) : Fin 100 :=
  ⟨(930766392056140912343928177133762816947247127151118312393220776124694996404377974265352718604913676599374129223385368884373191014978594136176364990883477603428206266267607296225585267621167536925700785611003281 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c3_left : ∀ x, c3InvMap (c3Map x) = x := by
  apply allFin
  decide +kernel

private def c3Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm c3Map c3InvMap c3_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin c3_left)

private def c3Word : Carrier := b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b * a * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * (b ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 4) * a * b * a * b⁻¹ * a * b

private theorem c3_word : c3Perm = (c3Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def c3 : C := ⟨⟨Theory.GroupTheory.tablePerm c3Map c3InvMap
    (by exact c3_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin c3_left), by
  change c3Perm ∈ generated
  rw [c3_word]
  exact c3Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * c3Perm = c3Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

def c4Map (x : Fin 100) : Fin 100 :=
  ⟨(2555788462298627675209404441745120767352918218909955609883128597532730664083670652256041121109177702644464106352078707986774069064844900848520666130642377385500181306056093962378438901238835088225163315322656040 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def c4InvMap (x : Fin 100) : Fin 100 :=
  ⟨(829794892254367253403563492166250271365480919281162889248187418854058848081735207393713366711042715517300670896508015414116849272685359217416463844351890761582866573917377655017337625879727489005462720546528219 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c4_left : ∀ x, c4InvMap (c4Map x) = x := by
  apply allFin
  decide +kernel

private def c4Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm c4Map c4InvMap c4_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin c4_left)

private def c4Word : Carrier := b * a * (b⁻¹ ^ 2) * a * b * a * b⁻¹ * a * b * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * (b ^ 3) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b ^ 4) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * b * a * b

private theorem c4_word : c4Perm = (c4Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A concrete word in HS centralizing the specified outer involution. -/
def c4 : C := ⟨⟨Theory.GroupTheory.tablePerm c4Map c4InvMap
    (by exact c4_left) (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin c4_left), by
  change c4Perm ∈ generated
  rw [c4_word]
  exact c4Word.property⟩, by
  change ∀ x ∈ ({elementaryPermutation} : Set (Equiv.Perm (Fin 100))),
    x * c4Perm = c4Perm * x
  rintro x rfl
  apply Equiv.ext
  apply allFin
  decide +kernel⟩

/-- The four ordered kernel generators. -/
def kernelGenerator : Fin 4 → C := ![q0, q1, q2, q3]

/-- Generators of the candidate centralizer, including the kernel generators. -/
def candidateGenerator : Fin 9 → C := ![q0, q1, q2, q3, c0, c1, c2, c3, c4]

/-- A concrete subgroup of the actual centralizer. Exhaustivity is a separate
stabilizer-chain calculation. -/
def candidate : Subgroup C := closure (Set.range candidateGenerator)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer
