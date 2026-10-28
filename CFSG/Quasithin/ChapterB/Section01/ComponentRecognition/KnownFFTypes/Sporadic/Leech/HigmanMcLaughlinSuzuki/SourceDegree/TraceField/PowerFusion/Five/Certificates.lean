module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Certificates for the HS five-subgroup

The 125 products of the existing certified generators exhaust their subgroup.
Ten explicit words in the ATLAS generators conjugate these products to their
squares. All word, conjugation and fixed-point calculations use kernel reduction.
The source action is inverted, preserving multiplication of words.
The internal `import all` continues the existing packed-table certificates
without making their private implementation part of the public interface.

Source: ATLAS HSG1-p100B0. Candidate discovery and the table encoder are retained
in `source/`; their output is not a mathematical premise.
-/

public section
namespace Sporadic.LeechRelated.HS.FiveFusion
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000

/-- The standard 125 products in the certified five-subgroup. -/
@[expose] def normalForm (t : Fin 125) : Carrier :=
  FiveSubgroup.x ^ (t.val % 5) * FiveSubgroup.y ^ (t.val / 5 % 5) *
    FiveSubgroup.z ^ (t.val / 25)

/-- The already certified normal forms exhaust the literal five-subgroup. -/
theorem normalForm_cover {g : Carrier} (hg : g ∈ FiveSubgroup.subgroup) :
    ∃ t, normalForm t = g := FiveSubgroup.normalForm_cover hg

private def a : Carrier := ⟨p0, by rw [a_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
private def b : Carrier := ⟨p1, by rw [b_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
private def letter (i : Fin 3) : Carrier := if i = 0 then a else if i = 1 then b else b⁻¹

private def c0Map (i : Fin 100) : Fin 100 :=
  ⟨(2124456835706051283611712405793044714497948472090146499582827123977716455422307215308161215727985362679687031323637195530553446262050820680462588505493926055396184011363452021540148003465140685581840253520972416 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c0InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1199592814762536341514058346239317161247076134491597683647475553002309419013485963749714621602084652425461056971227991457062583174770895979737159756580660124154169319118976958621948256590202471951880819335235200 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c0Left : ∀ i, c0InvMap (c0Map i) = i := by
  apply allFin
  decide +kernel
private def c0Perm : Equiv.Perm (Fin 100) :=
  tablePerm c0Map c0InvMap c0Left (rightInverse_of_leftInverse_fin c0Left)
private def c0Word : Carrier := evalWord letter [1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]
private theorem c0Perm_eq : c0Perm = inclusion c0Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c0 : Carrier := ⟨c0Perm, c0Perm_eq.symm ▸ c0Word.property⟩

private def c1Map (i : Fin 100) : Fin 100 :=
  ⟨(149503303638690160982851003778586275851256194574716665741572678547445618815499265487004072022081978942537032469973664687839607203545664244610208722632922398438115871297839518361889738350291528700327626415396480 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c1InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3064666434862933187438031311387106928488068924451047643735069854896622009934708743376358201224087604899247181172055750541457806628127721305490318205539553913541788764889848739471540624175389642897914392363263488 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c1Left : ∀ i, c1InvMap (c1Map i) = i := by
  apply allFin
  decide +kernel
private def c1Perm : Equiv.Perm (Fin 100) :=
  tablePerm c1Map c1InvMap c1Left (rightInverse_of_leftInverse_fin c1Left)
private def c1Word : Carrier := evalWord letter [2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2]
private theorem c1Perm_eq : c1Perm = inclusion c1Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c1 : Carrier := ⟨c1Perm, c1Perm_eq.symm ▸ c1Word.property⟩

private def c2Map (i : Fin 100) : Fin 100 :=
  ⟨(3064592812607459307602865624666604602188551083671861817348287931656604006585631974143774974757760910253046570028201628747692723956171007634034851996266297470262895970109471566094630198184196227938755442933852672 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c2InvMap (i : Fin 100) : Fin 100 :=
  ⟨(2124650757083364176318567498902790446252127580208251392406634374437802207979124328880110691424612435781709841824427962488012363578444683608728282988416670026712740107002074226838213484102892703190529998271597440 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c2Left : ∀ i, c2InvMap (c2Map i) = i := by
  apply allFin
  decide +kernel
private def c2Perm : Equiv.Perm (Fin 100) :=
  tablePerm c2Map c2InvMap c2Left (rightInverse_of_leftInverse_fin c2Left)
private def c2Word : Carrier := evalWord letter [1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 1]
private theorem c2Perm_eq : c2Perm = inclusion c2Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c2 : Carrier := ⟨c2Perm, c2Perm_eq.symm ▸ c2Word.property⟩

private def c3Map (i : Fin 100) : Fin 100 :=
  ⟨(4059094208284929059916381497598111220489381520256111746147664322386508324228016008829593365684051784631996007908485670207506647838501533823080851304992582506669013028296017189333484930375813695587034474031147904 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c3InvMap (i : Fin 100) : Fin 100 :=
  ⟨(4059123832903938962314326859448331032446959694332111834587174036554100749807180731223500433870745257965675061017618514238820547313590078633262506042413303982495485163151636846118727052311726462362645974273350656 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c3Left : ∀ i, c3InvMap (c3Map i) = i := by
  apply allFin
  decide +kernel
private def c3Perm : Equiv.Perm (Fin 100) :=
  tablePerm c3Map c3InvMap c3Left (rightInverse_of_leftInverse_fin c3Left)
private def c3Word : Carrier := evalWord letter [2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 1]
private theorem c3Perm_eq : c3Perm = inclusion c3Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c3 : Carrier := ⟨c3Perm, c3Perm_eq.symm ▸ c3Word.property⟩

private def c4Map (i : Fin 100) : Fin 100 :=
  ⟨(1199695889869925833344629690745302816464643376520366406677160750155545255080275434223429704075859745734375959223449672708005076564974406035096409381650254173949583645093089837456032084268214891932320242609286400 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c4InvMap (i : Fin 100) : Fin 100 :=
  ⟨(149309210494282977566025979330327565866925985772756369748501523645198400348400703165546051595254875002355124091188936011726031219490152601023261543798728303604311134546315449980706571112045480495246924276122368 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c4Left : ∀ i, c4InvMap (c4Map i) = i := by
  apply allFin
  decide +kernel
private def c4Perm : Equiv.Perm (Fin 100) :=
  tablePerm c4Map c4InvMap c4Left (rightInverse_of_leftInverse_fin c4Left)
private def c4Word : Carrier := evalWord letter [0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2]
private theorem c4Perm_eq : c4Perm = inclusion c4Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c4 : Carrier := ⟨c4Perm, c4Perm_eq.symm ▸ c4Word.property⟩

private def c5Map (i : Fin 100) : Fin 100 :=
  ⟨(1372606515335620341237738219951074301140058395118924708465034809023758933482975729444377840350123931816974091090116260921821416726237263392315112029596358054855458618251958354587464416313564367101974346744496897 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c5InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1199557937304451323781588117442242193245367601327270458814588627187252863874999061855253245972761917461561130252408948358364140884099067136368527649294877171028422778423301217575625182733095564354444724110475354 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c5Left : ∀ i, c5InvMap (c5Map i) = i := by
  apply allFin
  decide +kernel
private def c5Perm : Equiv.Perm (Fin 100) :=
  tablePerm c5Map c5InvMap c5Left (rightInverse_of_leftInverse_fin c5Left)
private def c5Word : Carrier := evalWord letter [2, 2, 0, 2, 2, 0, 1, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2]
private theorem c5Perm_eq : c5Perm = inclusion c5Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c5 : Carrier := ⟨c5Perm, c5Perm_eq.symm ▸ c5Word.property⟩

private def c6Map (i : Fin 100) : Fin 100 :=
  ⟨(2635047581962732398454759804187598942315429144213229960456018793213143002975345181306507784476216967799750088136510479321196934278947586204767105245194648610170402241669178431772621260582202260435181279401969410 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c6InvMap (i : Fin 100) : Fin 100 :=
  ⟨(2350484056304769094077785796314956929043779155668452267721551931875049864972067340625334550797513083719711352562262487750504376189697580477683429391332206081248648298904422289183365587068373756241224164922365092 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c6Left : ∀ i, c6InvMap (c6Map i) = i := by
  apply allFin
  decide +kernel
private def c6Perm : Equiv.Perm (Fin 100) :=
  tablePerm c6Map c6InvMap c6Left (rightInverse_of_leftInverse_fin c6Left)
private def c6Word : Carrier := evalWord letter [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]
private theorem c6Perm_eq : c6Perm = inclusion c6Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c6 : Carrier := ⟨c6Perm, c6Perm_eq.symm ▸ c6Word.property⟩

private def c7Map (i : Fin 100) : Fin 100 :=
  ⟨(149424588973330676134585860192169507818258760155349476337224217758385110815812867820922798695569112390328632289954878524152280311631111865883726204278707178347673267471095946992690744409849913759445431258267654 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c7InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1412555118957631442954466112033842514273373900327329059102657652007461585714370861633146989436587695729225404150405705857390699444896034546135514751454466651239645411036774630312198749000195728134547187361221377 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c7Left : ∀ i, c7InvMap (c7Map i) = i := by
  apply allFin
  decide +kernel
private def c7Perm : Equiv.Perm (Fin 100) :=
  tablePerm c7Map c7InvMap c7Left (rightInverse_of_leftInverse_fin c7Left)
private def c7Word : Carrier := evalWord letter [2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 1, 0, 2, 0, 1, 1, 0, 1, 1]
private theorem c7Perm_eq : c7Perm = inclusion c7Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c7 : Carrier := ⟨c7Perm, c7Perm_eq.symm ▸ c7Word.property⟩

private def c8Map (i : Fin 100) : Fin 100 :=
  ⟨(3338542148426837810063994642218067265622261808323420232847114341386652424563273008030191461878405069526571005021048595188856389094688386413142004287364076352587056927357693628936355730089908164095095324005630096 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c8InvMap (i : Fin 100) : Fin 100 :=
  ⟨(1412348259957313600139316344394551310062397577394228570339672078996249400204402869693404414602210774685664705528975543704494646210077833951334697218894595122134098360778676543680816989624678418758564032296779917 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c8Left : ∀ i, c8InvMap (c8Map i) = i := by
  apply allFin
  decide +kernel
private def c8Perm : Equiv.Perm (Fin 100) :=
  tablePerm c8Map c8InvMap c8Left (rightInverse_of_leftInverse_fin c8Left)
private def c8Word : Carrier := evalWord letter [1, 0, 1, 0, 1, 0, 2, 2, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]
private theorem c8Perm_eq : c8Perm = inclusion c8Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c8 : Carrier := ⟨c8Perm, c8Perm_eq.symm ▸ c8Word.property⟩

private def c9Map (i : Fin 100) : Fin 100 :=
  ⟨(3094416292443573547450624719420833365352454308747983025456081548511283522629149530952846736139758957481629737618952270222843474484702640243378217513217588029434509552458042577653381758889609033187653545574795285 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def c9InvMap (i : Fin 100) : Fin 100 :=
  ⟨(3094476489840305270189699762575470545685151629145855742189312445699562513067629386928009477945675282141955191681859895605602752790038549325640681235200959391260907067678322916404031227480134421695910327539468944 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem c9Left : ∀ i, c9InvMap (c9Map i) = i := by
  apply allFin
  decide +kernel
private def c9Perm : Equiv.Perm (Fin 100) :=
  tablePerm c9Map c9InvMap c9Left (rightInverse_of_leftInverse_fin c9Left)
private def c9Word : Carrier := evalWord letter [2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2]
private theorem c9Perm_eq : c9Perm = inclusion c9Word := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def c9 : Carrier := ⟨c9Perm, c9Perm_eq.symm ▸ c9Word.property⟩

private def actor (i : Fin 10) : Carrier :=
  match i.val with
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | 4 => c4
  | 5 => c5
  | 6 => c6
  | 7 => c7
  | 8 => c8
  | _ => c9

private def choice (t : Fin 125) : Fin 10 :=
  ⟨(654678280006706806040415736495563953551676532091349043698168865652546645071088620040698702999924698540722499696108028068483637462900908088085713623440 >>> (4 * t.val)) % 16 % 10, Nat.mod_lt _ (by decide)⟩

/-- Each normal form has a square conjugator in the literal carrier. -/
theorem normalForm_square (t : Fin 125) : IsConj (normalForm t) (normalForm t ^ 2) := by
  have h : ∀ s : Fin 125, ∀ i : Fin 100,
      inclusion (actor (choice s) * normalForm s * (actor (choice s))⁻¹) i =
        inclusion (normalForm s ^ 2) i := by
    apply allFin
    decide +kernel
  exact isConj_iff.mpr ⟨actor (choice t), Subtype.ext (Equiv.ext (h t))⟩

/-- A nonidentity normal form moves either 95 or all 100 letters. -/
theorem normalForm_support (t : Fin 125) (ht : t ≠ 0) :
    (inclusion (normalForm t)).support.card = 95 ∨
      (inclusion (normalForm t)).support.card = 100 := by
  have h : ∀ s : Fin 125, s ≠ 0 →
      (inclusion (normalForm s)).support.card = 95 ∨
      (inclusion (normalForm s)).support.card = 100 := by
    apply allFin
    decide +kernel
  exact h t ht

end Sporadic.LeechRelated.HS.FiveFusion
