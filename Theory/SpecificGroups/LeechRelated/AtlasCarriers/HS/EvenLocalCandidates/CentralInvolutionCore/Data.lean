module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates
/-!
# Finite graph data for the first HS local

A graph preserved by the two defining ATLAS permutations separates the 100
letters into pairs according to their neighbors among the fixed letters of
`e0`. Five explicit words in `s0`, `s1`, `s2` distinguish the ten pairs of
fixed letters by their fixed-point patterns.

All tables are checked against the actual word permutations in Lean's kernel.
The graph and words are witnesses discovered by GAP, with reproducible inputs
in `source/`; neither GAP nor a graph automorphism identification is assumed.
Source: GLS volume 3, Table 5.3m, printed p.274, and Aschbacher–Smith,
condition E, printed pp.3–4. ATLAS provenance is inherited from the carrier.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open Subgroup
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)
theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi
def row (i : Fin 100) : ℕ := (1559251907115872018392097211863610601264465706396073649877301471758307923103721942384469774973189480598974258644536197444262701693712011130806870359091487951032334983544536629237089852262361929277338424011448862489356900835625805599608479374989329619770039045421279266519453264123341641553541512442323386650355197810635871926025032933912927615683668941878049279594429918445113429515734922873353725525089613549745709595660369040832842015285271397159426668825660469543581615476556047258117220691023307960701474041091021288497136761017376426994416805931438644736147795398117023160359722822695004948816697801279804990014742410298843495133157982927455461454005589524909766734218910112363020801606715483586649206715648563041569140694912509171586819160687183604056835149648799451830404973868450717673000553699711017666125560619681816952287810557373614827310026192349094732707527530586319341851738859593012611881375208624155594807407445204312238018817978681955055093315614967429650297821338434191185412139299792796665276236812833736618687343321616098578406494728550474577131496009147502373326739973822378787759683789794763245605327677667135221665559752359676167451567777623766179055036338935472639622156750283539394906628003036955534426682962463253742865946954832276665942465781827210743007568007102291013883694991734086671263802263519105132312981631589602589886186249452551047134197746072521385264945925479518585652363590962487377091660229609615095160373499103310284095439210270407163414658676139298736170300417045391417805913973846500721863496976890401548729079462469829039480877211140018461593750553944604582214584916854250685171480608562608168027349332943547999220743354324492656138916532519889451012446896187467279037235489791842335741873024005583776279570718338150046305660065978354450056799579325527284666593141778527420010121026014734842026667028430140722507142291775791456163891055560670458697974351446129803425236649859641383727344747603948840148450469176551098054935560593507538664824360113019297219020403323173960162367710315319436831025984126453215842223104124988870754051461595928941762149617486770498689625247911769561188731657122295456571953520820357448284554733031867319696742662649553496804757275427107781003223680912395069633862333966838161524635691201830050539523735417592506449801811968512639581936556167281308824118968669017762784039341881628175197240258379859301701371839583735705737873364135895172069289285068849532648307743062186146199606243205566380025131855289357485187408514996329589952872197178758203055141508451926226126803142804271783458664269264210621464934316155464088460821643345850664740636757944834345354978003768110361153731276154730335542526359454773991907653106711261663327586207966216092885858395783484961824574174700830320972486310528902348527245168395851506792983185429073714495548054266748341418847457870037974781405695056653475021378051824971408597190027673457233289218819637304314401556327994695331319634075725673557924684558383664598396595718874435609027203267134171914000 >>> (100 * i.val)) % (2^100)
def adj (i j : Fin 100) : Bool := (row i).testBit j.val
def signature (i : Fin 100) : ℕ := row i &&& 79615170040137994149472252165
def twin (i : Fin 100) : Fin 100 :=
  ⟨(3026983005745414044722787134864859627385026074477306620660865292331261536617404580396299169592507950501070716997216459284113405960041228190430875165045642322317642637938323190841960093090555654560080590659291021 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def ab0Map (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def ab0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem ab0_left : ∀ i, ab0InvMap (ab0Map i) = i := by
  apply allFin
  decide +kernel
def ab0 : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm ab0Map ab0InvMap (by exact ab0_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin ab0_left)
theorem ab0_eq : ab0 = generatorA := by
  apply Equiv.ext
  apply allFin
  decide +kernel
theorem ab0_adj : ∀ i j, adj (ab0 i) (ab0 j) = adj i j := by
  apply allFin
  decide +kernel
def ab1Map (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def ab1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(852881488533531112336995551220226122361210863663080587750664607485875722147280441807057556633165462885474069200795003754517913050689892735891088239319177696223676845175972313037682728934689958756512102884170325 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem ab1_left : ∀ i, ab1InvMap (ab1Map i) = i := by
  apply allFin
  decide +kernel
def ab1 : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm ab1Map ab1InvMap (by exact ab1_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin ab1_left)
theorem ab1_eq : ab1 = generatorB := by
  apply Equiv.ext
  apply allFin
  decide +kernel
theorem ab1_adj : ∀ i j, adj (ab1 i) (ab1 j) = adj i j := by
  apply allFin
  decide +kernel
def q0Map (i : Fin 100) : Fin 100 :=
  ⟨(4095557383497070696779903571476665225518081543405432243328487047762726791453587274265970130516223422473241849601580374919172652531124262275777534893770803521910206543063804260440457101384061910069248211009175693 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def q0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(4095557383497070696779903571476665225518081543405432243328487047762726791453587274265970130516223422473241849601580374919172652531124262275777534893770803521910206543063804260440457101384061910069248211009175693 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem q0_left : ∀ i, q0InvMap (q0Map i) = i := by
  apply allFin
  decide +kernel
private def q0Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q0Map q0InvMap q0_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q0_left)
private def q0Word : Carrier := (s0⁻¹ ^ 1)
private theorem q0_word : q0Perm = (q0Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
def q0 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm q0Map q0InvMap (by exact q0_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q0_left), by
      change q0Perm ∈ generated
      rw [q0_word]
      exact q0Word.property⟩
def q1Map (i : Fin 100) : Fin 100 :=
  ⟨(47395963843353240707548276388156876400662262214014272105573688142593050488516239040139835172027450539579788449968462915202621820251515943317531718671581401852241879733772590776373196618534273978869214032736640 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def q1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(47395963843353240707548276388156876400662262214014272105573688142593050488516239040139835172027450539579788449968462915202621820251515943317531718671581401852241879733772590776373196618534273978869214032736640 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem q1_left : ∀ i, q1InvMap (q1Map i) = i := by
  apply allFin
  decide +kernel
private def q1Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q1Map q1InvMap q1_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q1_left)
private def q1Word : Carrier := (s1⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s1⁻¹ ^ 1)
private theorem q1_word : q1Perm = (q1Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
def q1 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm q1Map q1InvMap (by exact q1_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q1_left), by
      change q1Perm ∈ generated
      rw [q1_word]
      exact q1Word.property⟩
def q2Map (i : Fin 100) : Fin 100 :=
  ⟨(781303545876410909711851659946931519859577167598337451288265702171930890699619480261551535799912171185148126000184271580339795704681986026525934484538156467221568796247281071869165375499533705576103590930460928 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def q2InvMap (i : Fin 100) : Fin 100 :=
  ⟨(781303545876410909711851659946931519859577167598337451288265702171930890699619480261551535799912171185148126000184271580339795704681986026525934484538156467221568796247281071869165375499533705576103590930460928 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem q2_left : ∀ i, q2InvMap (q2Map i) = i := by
  apply allFin
  decide +kernel
private def q2Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q2Map q2InvMap q2_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q2_left)
private def q2Word : Carrier := (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s0⁻¹ ^ 1)
private theorem q2_word : q2Perm = (q2Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
def q2 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm q2Map q2InvMap (by exact q2_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q2_left), by
      change q2Perm ∈ generated
      rw [q2_word]
      exact q2Word.property⟩
def q3Map (i : Fin 100) : Fin 100 :=
  ⟨(1771815422433901666727809986638358736545786216485253257201162018237091810378641110866711281716011224037134772908974978243434808771548970748705538516319054857504522770469889478470363466622813860682201540618915968 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def q3InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1771815422433901666727809986638358736545786216485253257201162018237091810378641110866711281716011224037134772908974978243434808771548970748705538516319054857504522770469889478470363466622813860682201540618915968 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem q3_left : ∀ i, q3InvMap (q3Map i) = i := by
  apply allFin
  decide +kernel
private def q3Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q3Map q3InvMap q3_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q3_left)
private def q3Word : Carrier := (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s2⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s2⁻¹ ^ 1)
private theorem q3_word : q3Perm = (q3Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
def q3 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm q3Map q3InvMap (by exact q3_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q3_left), by
      change q3Perm ∈ generated
      rw [q3_word]
      exact q3Word.property⟩
def q4Map (i : Fin 100) : Fin 100 :=
  ⟨(3026959337250137020114146919765714089706287628942964704714852677632651742029106572469538504812631057497403480919326917700450085948026360277108820323509844286251325832858141117914522852435035501942905534604542080 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
def q4InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3026959337250137020114146919765714089706287628942964704714852677632651742029106572469538504812631057497403480919326917700450085948026360277108820323509844286251325832858141117914522852435035501942905534604542080 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem q4_left : ∀ i, q4InvMap (q4Map i) = i := by
  apply allFin
  decide +kernel
private def q4Perm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm q4Map q4InvMap q4_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin q4_left)
private def q4Word : Carrier := (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1) * (s0⁻¹ ^ 1) * (s1⁻¹ ^ 1)
private theorem q4_word : q4Perm = (q4Word : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
def q4 : Carrier :=
  ⟨Theory.GroupTheory.tablePerm q4Map q4InvMap (by exact q4_left)
    (by exact Theory.GroupTheory.rightInverse_of_leftInverse_fin q4_left), by
      change q4Perm ∈ generated
      rw [q4_word]
      exact q4Word.property⟩
def q (k : Fin 5) : Carrier := ![q0, q1, q2, q3, q4] k
theorem e0_mul : e0 * e0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel
theorem e0_nontrivial : e0 ≠ 1 := by
  intro h
  have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 1) h
  have hn : (e0 : Equiv.Perm (Fin 100)) 1 ≠ 1 := by decide +kernel
  exact hn he

theorem signature_bits : ∀ i j : Fin 100,
    (signature i).testBit j.val =
      if (e0 : Equiv.Perm (Fin 100)) j = j then adj i j else false := by
  apply allFin
  decide +kernel

theorem signature_bound : ∀ i : Fin 100, signature i < 2^100 := by
  apply allFin
  decide +kernel

theorem signature_class : ∀ i j : Fin 100,
    signature i = signature j ↔ j = i ∨ j = twin i := by
  apply allFin
  decide +kernel

theorem twin_square : ∀ i, twin (twin i) = i := by
  apply allFin
  decide +kernel

theorem twin_ne : ∀ i, twin i ≠ i := by
  apply allFin
  decide +kernel

theorem twin_fixed : ∀ i : Fin 100,
    (e0 : Equiv.Perm (Fin 100)) i = i →
      (e0 : Equiv.Perm (Fin 100)) (twin i) = twin i := by
  apply allFin
  decide +kernel

theorem q_commutes : ∀ k, q k * e0 = e0 * q k := by
  have h : ∀ k : Fin 5, ∀ i : Fin 100,
      ((q k * e0 : Carrier) : Equiv.Perm (Fin 100)) i =
        ((e0 * q k : Carrier) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  intro k
  exact Subtype.ext (Equiv.ext (h k))

theorem q_pair : ∀ k (i : Fin 100),
    (e0 : Equiv.Perm (Fin 100)) i = i →
      (q k : Equiv.Perm (Fin 100)) i = i ∨
        (q k : Equiv.Perm (Fin 100)) i = twin i := by
  apply allFin
  decide +kernel

theorem q_separates : ∀ i j : Fin 100,
    (e0 : Equiv.Perm (Fin 100)) i = i →
    (e0 : Equiv.Perm (Fin 100)) j = j →
    (∀ k : Fin 5, ((q k : Equiv.Perm (Fin 100)) i = i ↔
      (q k : Equiv.Perm (Fin 100)) j = j)) → signature i = signature j := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
