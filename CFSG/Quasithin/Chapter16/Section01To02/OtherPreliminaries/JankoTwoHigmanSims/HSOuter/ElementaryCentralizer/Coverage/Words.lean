module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage.Pruning

/-!
# Candidate words for all surviving outer centralizer permutations

Finite witnesses for the centralizer of the specified outer HS involution.
The existing HS order certificate supplies a stabilizer chain. Orbit colors
of its residual groups restrict each successive representative. All finite
identities are checked by Lean's kernel; the generator supplies no trusted facts.

Source: ATLAS HSG1-p100B0; GLS volume 3, Table 5.3m, printed p.274;
Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 class 2C.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
open Theory.GroupTheory Sporadic.LeechRelated.HS.OrderCertificate
set_option maxRecDepth 100000
set_option Elab.async false

/-- Binary coordinates in the kernel already constructed in `Kernel`. -/
def coordinates (code : Fin 16) : E16 :=
  fun i => Multiplicative.ofAdd ((code.val >>> i.val : Nat) : ZMod 2)

/-- The nine candidate generators and their inverses, in witness-file order. -/
def signedGenerator (i : Fin 18) : C :=
  let j : Fin 9 := ⟨i.val / 2, by omega⟩
  if i.val % 2 = 0 then candidateGenerator j else (candidateGenerator j)⁻¹

theorem signedGenerator_mem (i : Fin 18) : signedGenerator i ∈ candidate := by
  have h (j : Fin 9) : candidateGenerator j ∈ candidate :=
    Subgroup.subset_closure ⟨j, rfl⟩
  unfold signedGenerator
  split
  · exact h _
  · exact candidate.inv_mem (h _)

/-- Fast packed tables for the same nine certified permutations. -/
def fastForward (i : Fin 9) : Nat :=
  if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
(1675330314779068693714700583707532259400964940572826544374136458541059555826767577028168303556712201510925843888055581302324992243499380321915174039557177065862810606840795197114891006442013699487582075690582206) else
(1921879842883680949394128876243423382333256415507645276790598025603170938348326535361137128103922286173671761286909234921920560599852174049673354920195896268176644635887972330192536535620991493104291641758494494)) else
(if i.val < 3 then
(483625921203830520314363254102132153964433599928892181669812847335194078788807674961787853807643477101519111465740631651512432536496269379695589852617100932777346852069525823366477458673094097429718896412110615) else
(935665421067161539114550600214174953050318104797167433249222864111937910019260773096276025881393980988181514347013943429142299099853983321340991830744532202059188139278615345794789719095453037589656567794275857))) else
(if i.val < 6 then
(if i.val < 5 then
(932143057991537627731039120938127112855207792840755636631935539759564760637564231863074305624172521246038655859438697596406630588527025455362546655292599409067364012029830436213952176835951977935579701304058302) else
(1921926207754755729985725194014766236660315014351165522231817371720862688430045063439046512833119740387074837836437001646926461356598436487972904459330186814401253004395672994383995701139228065566789577980068938)) else
(if i.val < 7 then
(544883106487000609279949487116194723688945395007359782619710632629715414589247842855667690485066873233817989591483695303379331807274158665898883351777658419557957798380140434562369273272070298266182684832597965) else
(if i.val < 8 then
(1711733370374198390056655339832082129218977219187742759325782388718427677918643508921730376995503027879080972243094912534114240284861479839654521020209625963413457362681784526580588742448229437057229139607380927) else
(2555788462298627675209404441745120767352918218909955609883128597532730664083670652256041121109177702644464106352078707986774069064844900848520666130642377385500181306056093962378438901238835088225163315322656040))))

def fastBackward (i : Fin 9) : Nat :=
  if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
(1675330314779068693714700583707532259400964940572826544374136458541059555826767577028168303556712201510925843888055581302324992243499380321915174039557177065862810606840795197114891006442013699487582075690582206) else
(1921879842883680949394128876243423382333256415507645276790598025603170938348326535361137128103922286173671761286909234921920560599852174049673354920195896268176644635887972330192536535620991493104291641758494494)) else
(if i.val < 3 then
(483625921203830520314363254102132153964433599928892181669812847335194078788807674961787853807643477101519111465740631651512432536496269379695589852617100932777346852069525823366477458673094097429718896412110615) else
(935665421067161539114550600214174953050318104797167433249222864111937910019260773096276025881393980988181514347013943429142299099853983321340991830744532202059188139278615345794789719095453037589656567794275857))) else
(if i.val < 6 then
(if i.val < 5 then
(1651613618130063444867853982715731397691246779245365864827494858775051790928228256347229802273637988112130313613296651610154823234640487657451666554687572611077115313144564338984788667306888080686847301493533898) else
(1921926207754755729985725194014766236660315014351165522231817371720862688430045063439046512833119740387074837836437001646926461356598436487972904459330186814401253004395672994383995701139228065566789577980068938)) else
(if i.val < 7 then
(932144233769483193184123956216193020078346655173718230759077865189138319916696282296209437226653725153354532782247486160922517097137854024765956359547716831991218547080618249392578761673821843915494229578731484) else
(if i.val < 8 then
(930766392056140912343928177133762816947247127151118312393220776124694996404377974265352718604913676599374129223385368884373191014978594136176364990883477603428206266267607296225585267621167536925700785611003281) else
(829794892254367253403563492166250271365480919281162889248187418854058848081735207393713366711042715517300670896508015414116849272685359217416463844351890761582866573917377655017337625879727489005462720546528219))))

def fastImage (i : Fin 9) (x : Fin 100) : Fin 100 :=
  ⟨(fastForward i / 2 ^ (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def fastPreimage (i : Fin 9) (x : Fin 100) : Fin 100 :=
  ⟨(fastBackward i / 2 ^ (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem fast_inverse : ∀ i x, fastPreimage i (fastImage i x) = x := by
  apply allFin
  decide +kernel

def fastGenerator (i : Fin 9) : Perm :=
  tablePerm (fastImage i) (fastPreimage i) (fast_inverse i)
    (rightInverse_of_leftInverse_fin (fast_inverse i))

/-- The fast tables are identified with the actual candidate generators. -/
theorem fastGenerator_eq (i : Fin 9) : fastGenerator i = (candidateGenerator i).val.val := by
  have h : ∀ (i : Fin 9) (x : Fin 100),
      fastGenerator i x = (candidateGenerator i).val.val x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

def fastSigned (i : Fin 18) : Perm :=
  let j : Fin 9 := ⟨i.val / 2, by omega⟩
  if i.val % 2 = 0 then fastGenerator j else (fastGenerator j)⁻¹

theorem fastSigned_eq (i : Fin 18) : fastSigned i = (signedGenerator i).val.val := by
  unfold fastSigned signedGenerator
  split
  · exact fastGenerator_eq _
  · exact congrArg Inv.inv (fastGenerator_eq _)

def representativeWord (j : Fin 120) : List (Fin 18) :=
  if j.val < 60 then
(if j.val < 30 then
(if j.val < 15 then
(if j.val < 7 then
(if j.val < 3 then
(if j.val < 1 then
([]) else
(if j.val < 2 then
([8]) else
([9]))) else
(if j.val < 5 then
(if j.val < 4 then
([10]) else
([12])) else
(if j.val < 6 then
([13]) else
([14])))) else
(if j.val < 11 then
(if j.val < 9 then
(if j.val < 8 then
([16]) else
([10, 8])) else
(if j.val < 10 then
([12, 8]) else
([13, 8]))) else
(if j.val < 13 then
(if j.val < 12 then
([16, 8]) else
([10, 9])) else
(if j.val < 14 then
([12, 9]) else
([16, 9]))))) else
(if j.val < 22 then
(if j.val < 18 then
(if j.val < 16 then
([12, 10]) else
(if j.val < 17 then
([13, 10]) else
([14, 10]))) else
(if j.val < 20 then
(if j.val < 19 then
([16, 10]) else
([9, 12])) else
(if j.val < 21 then
([10, 12]) else
([12, 12])))) else
(if j.val < 26 then
(if j.val < 24 then
(if j.val < 23 then
([14, 12]) else
([16, 12])) else
(if j.val < 25 then
([8, 13]) else
([10, 13]))) else
(if j.val < 28 then
(if j.val < 27 then
([13, 13]) else
([16, 13])) else
(if j.val < 29 then
([13, 14]) else
([16, 14])))))) else
(if j.val < 45 then
(if j.val < 37 then
(if j.val < 33 then
(if j.val < 31 then
([8, 16]) else
(if j.val < 32 then
([9, 16]) else
([10, 16]))) else
(if j.val < 35 then
(if j.val < 34 then
([12, 16]) else
([13, 16])) else
(if j.val < 36 then
([14, 16]) else
([12, 10, 8])))) else
(if j.val < 41 then
(if j.val < 39 then
(if j.val < 38 then
([16, 10, 8]) else
([10, 12, 8])) else
(if j.val < 40 then
([12, 12, 8]) else
([14, 12, 8]))) else
(if j.val < 43 then
(if j.val < 42 then
([16, 12, 8]) else
([8, 13, 8])) else
(if j.val < 44 then
([13, 13, 8]) else
([16, 13, 8]))))) else
(if j.val < 52 then
(if j.val < 48 then
(if j.val < 46 then
([8, 16, 8]) else
(if j.val < 47 then
([9, 16, 8]) else
([10, 16, 8]))) else
(if j.val < 50 then
(if j.val < 49 then
([12, 16, 8]) else
([13, 16, 8])) else
(if j.val < 51 then
([14, 16, 8]) else
([12, 10, 9])))) else
(if j.val < 56 then
(if j.val < 54 then
(if j.val < 53 then
([16, 10, 9]) else
([10, 12, 9])) else
(if j.val < 55 then
([12, 12, 9]) else
([14, 12, 9]))) else
(if j.val < 58 then
(if j.val < 57 then
([16, 12, 9]) else
([8, 16, 9])) else
(if j.val < 59 then
([9, 16, 9]) else
([10, 16, 9]))))))) else
(if j.val < 90 then
(if j.val < 75 then
(if j.val < 67 then
(if j.val < 63 then
(if j.val < 61 then
([12, 16, 9]) else
(if j.val < 62 then
([13, 16, 9]) else
([14, 16, 9]))) else
(if j.val < 65 then
(if j.val < 64 then
([12, 12, 10]) else
([14, 12, 10])) else
(if j.val < 66 then
([16, 12, 10]) else
([13, 13, 10])))) else
(if j.val < 71 then
(if j.val < 69 then
(if j.val < 68 then
([16, 13, 10]) else
([13, 14, 10])) else
(if j.val < 70 then
([16, 14, 10]) else
([9, 16, 10]))) else
(if j.val < 73 then
(if j.val < 72 then
([10, 16, 10]) else
([12, 16, 10])) else
(if j.val < 74 then
([14, 16, 10]) else
([12, 9, 12]))))) else
(if j.val < 82 then
(if j.val < 78 then
(if j.val < 76 then
([16, 9, 12]) else
(if j.val < 77 then
([12, 10, 12]) else
([16, 10, 12]))) else
(if j.val < 80 then
(if j.val < 79 then
([9, 12, 12]) else
([10, 12, 12])) else
(if j.val < 81 then
([14, 12, 12]) else
([16, 12, 12])))) else
(if j.val < 86 then
(if j.val < 84 then
(if j.val < 83 then
([13, 14, 12]) else
([16, 14, 12])) else
(if j.val < 85 then
([8, 16, 12]) else
([13, 16, 12]))) else
(if j.val < 88 then
(if j.val < 87 then
([12, 8, 13]) else
([16, 8, 13])) else
(if j.val < 89 then
([13, 10, 13]) else
([16, 10, 13])))))) else
(if j.val < 105 then
(if j.val < 97 then
(if j.val < 93 then
(if j.val < 91 then
([10, 13, 13]) else
(if j.val < 92 then
([16, 13, 13]) else
([8, 16, 13]))) else
(if j.val < 95 then
(if j.val < 94 then
([9, 16, 13]) else
([12, 16, 13])) else
(if j.val < 96 then
([14, 16, 13]) else
([8, 13, 14])))) else
(if j.val < 101 then
(if j.val < 99 then
(if j.val < 98 then
([8, 16, 14]) else
([9, 16, 14])) else
(if j.val < 100 then
([14, 16, 14]) else
([10, 8, 16]))) else
(if j.val < 103 then
(if j.val < 102 then
([16, 8, 16]) else
([16, 9, 16])) else
(if j.val < 104 then
([13, 10, 16]) else
([16, 12, 16]))))) else
(if j.val < 112 then
(if j.val < 108 then
(if j.val < 106 then
([16, 13, 16]) else
(if j.val < 107 then
([16, 14, 16]) else
([12, 12, 10, 8]))) else
(if j.val < 110 then
(if j.val < 109 then
([16, 12, 10, 8]) else
([12, 10, 12, 8])) else
(if j.val < 111 then
([10, 12, 12, 8]) else
([14, 12, 12, 8])))) else
(if j.val < 116 then
(if j.val < 114 then
(if j.val < 113 then
([13, 14, 12, 8]) else
([16, 14, 12, 8])) else
(if j.val < 115 then
([10, 13, 13, 8]) else
([16, 13, 13, 8]))) else
(if j.val < 118 then
(if j.val < 117 then
([16, 13, 16, 8]) else
([16, 12, 10, 9])) else
(if j.val < 119 then
([12, 10, 12, 9]) else
([16, 14, 12, 9])))))))

/-- Representatives evaluated directly in C; no quotient facts are needed. -/
def representative (j : Fin 120) : C := evalWord signedGenerator (representativeWord j)

theorem representative_mem (j : Fin 120) : representative j ∈ candidate := by
  unfold representative
  generalize representativeWord j = w
  induction w with
  | nil => exact candidate.one_mem
  | cons i w ih => exact candidate.mul_mem (signedGenerator_mem i) ih

def fastRepresentative (j : Fin 120) : Perm :=
  evalWord fastSigned (representativeWord j)

theorem fastRepresentative_eq (j : Fin 120) :
    fastRepresentative j = (representative j).val.val := by
  unfold fastRepresentative representative
  generalize representativeWord j = w
  induction w with
  | nil => rfl
  | cons i w ih =>
    change fastSigned i * evalWord fastSigned w =
      (signedGenerator i).val.val * (evalWord signedGenerator w).val.val
    rw [fastSigned_eq, ih]

def fastKernel (code : Fin 16) : Perm :=
  fastGenerator 0 ^ (coordinates code 0).toAdd.val *
    fastGenerator 1 ^ (coordinates code 1).toAdd.val *
    fastGenerator 2 ^ (coordinates code 2).toAdd.val *
    fastGenerator 3 ^ (coordinates code 3).toAdd.val

theorem fastKernel_eq (code : Fin 16) :
    fastKernel code = (kernelHom (coordinates code)).val.val := by
  simp only [fastKernel, fastGenerator_eq]
  rfl

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
