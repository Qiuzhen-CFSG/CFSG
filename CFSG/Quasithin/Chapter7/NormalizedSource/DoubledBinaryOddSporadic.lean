module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddTernary
public import Theory.SpecificGroups.Janko3.Model.FrattiniEight
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniEight

import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniEight

/-!
# Sporadic outer exclusions for the original binary-three residual

The actual J₃ and McL Sylow two-groups both have order 128. Small word
certificates construct a surjection onto an elementary eight. The established
Frattini bound identifies its full kernel with the Frattini subgroup. The
images of elements whose square is one have respectively five and four
members. They are invariant under all Sylow automorphisms. An automorphism
of order seven fixes only the identity on an eight-element group, so orbit
counting rules out both profiles. The Burnside basis kernel then excludes
seven from the full Sylow automorphism group.

Restriction to the actual Sylow and descent through the entire component
center exclude both sporadic models from the original SL₃(2) outer section.
The final inspection retains five actual model families, and the Chapter12
consumer applies it to the same H-star prime-order witness.

The certificates use the existing ATLAS J3G1-p6156B0 and McLG1-p275B0
permutations with their stored multiplication conventions. The 128 word
normal forms are distinguished by one or two evaluated letters; only
multiplication by generators is checked computationally, and list induction
proves the full homomorphism law. Every certificate is checked by Lean's
kernel. The proof-only `import all` intentionally extends the existing McL
word certificate without changing its public boundary.
Source: Aschbacher–Smith 4.4.10–11, printed p.621, used by 7.3.4 and 7.6.1,
printed pp.699,702, refs/quasithin.pdf. The ATLAS source conventions are
recorded in the imported carrier and J₃ TwoLocal/source/README.md.
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
private theorem no_seven_of_invariant_subset
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (A : Subgroup (MulAut E)) (I : Set E) (hlo : 2 ≤ Nat.card I) (hhi : Nat.card I ≤ 6)
    (hinv : ∀ a : A, ∀ x ∈ I, a.val x ∈ I) : ¬ 7 ∣ Nat.card A := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 7 hd
  let B := zpowers a
  have hB : Nat.card B = 7 := (Nat.card_zpowers a).trans ha
  have hp : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  let F := FixedPoints.subgroup B E
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 7 = Nat.card F % 7 at hmod
  have hle : Nat.card F ≤ 8 := hE ▸ F.card_le_card_group
  have hne : Nat.card F ≠ 8 := by
    intro hc
    have ht : F = ⊤ := F.eq_top_of_card_eq (hc.trans hE.symm)
    have hane : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      exact (show x ∈ F from ht ▸ mem_top x) ⟨a,mem_zpowers a⟩
    rw [hane,orderOf_one] at ha
    norm_num at ha
  have hF : Nat.card F = 1 := by rw [hE] at hmod; omega
  let : MulAction B I :=
    { smul := fun b x => ⟨b.val.val x.val,hinv b.val x.val x.property⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun b c x => Subtype.ext rfl }
  let j : MulAction.fixedPoints B I → F := fun x =>
    ⟨x.val.val,fun b => congrArg Subtype.val (x.property b)⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : F => (z : E)) h))
  have hb : Nat.card (MulAction.fixedPoints B I) ≤ 1 :=
    hF ▸ Nat.card_le_card_of_injective j hj
  have hm := hp.card_modEq_card_fixedPoints I
  change Nat.card I % 7 = Nat.card (MulAction.fixedPoints B I) % 7 at hm
  omega

private def involutionImages {P : Type*} [Group P] : Set (P ⧸ frattini P) :=
  {v | ∃ x : P, x^2=1 ∧ QuotientGroup.mk' (frattini P) x=v}

private theorem no_seven_aut {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hQ : Nat.card (P ⧸ frattini P)=8)
    (hlo : 2 ≤ Nat.card (involutionImages (P:=P)))
    (hhi : Nat.card (involutionImages (P:=P)) ≤ 6) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let α := quotientAut (frattini P)
  have hI : ∀ a : α.range, ∀ x ∈ involutionImages (P:=P), a.val x ∈ involutionImages := by
    rintro ⟨a,b,hb⟩ v ⟨x,hx,rfl⟩
    change a (QuotientGroup.mk' (frattini P) x) ∈ involutionImages
    rw [←hb,quotientAut_apply_mk]
    exact ⟨b x,by rw [←map_pow,hx,map_one],rfl⟩
  intro hd
  have hc : Nat.card α.ker * Nat.card α.range = Nat.card (MulAut P) := by
    rw [←index_ker]; exact α.ker.card_mul_index
  obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hP).exists_card_eq
  have hcop : Nat.Coprime 7 (Nat.card α.ker) := by
    rw [hk]; exact (by decide : Nat.Coprime 7 2).pow_right k
  apply no_seven_of_invariant_subset hQ α.range involutionImages hlo hhi hI
  exact hcop.dvd_of_dvd_mul_left (hc.symm ▸ hd)

private theorem frattini_eq_kernel
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian 2 E]
    (hP : Nat.card P = 128) (hPhi : Nat.card (P ⧸ frattini P) ≤ 8)
    (hE : Nat.card E=8) (f : P →* E) (hf : Function.Surjective f) :
    frattini P = f.ker := by
  let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  have hle := frattini_le_comap_frattini_of_surjective hf
  rw [frattini_eq_bot_of_isElementaryAbelian (R:=E) (p:=2)] at hle
  change frattini P ≤ f.ker at hle
  apply eq_of_le_of_card_ge hle
  have hq : Nat.card (P ⧸ f.ker) = 8 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans hE
  have h1 := card_eq_card_quotient_mul_card_subgroup (frattini P)
  have h2 := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [hP] at h1 h2
  rw [hq] at h2
  nlinarith

private theorem no_seven_aut_of_quotient
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hP : IsPGroup 2 P)
    (hcard : Nat.card P=128) (hPhi : Nat.card (P ⧸ frattini P) ≤ 8)
    (hE : Nat.card E=8) (f : P →* E) (hf : Function.Surjective f)
    (hc : Nat.card {v : E // ∃ x : P, x^2=1 ∧ f x=v}=4 ∨
      Nat.card {v : E // ∃ x : P, x^2=1 ∧ f x=v}=5) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  have hker := frattini_eq_kernel hcard hPhi hE f hf
  let e : P ⧸ frattini P ≃* E := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x : P) : e (QuotientGroup.mk' (frattini P) x) = f x := rfl
  let a : involutionImages (P:=P) ≃ {v : E // ∃ x : P, x^2=1 ∧ f x=v} :=
    { toFun := fun v => ⟨e v, by
        obtain ⟨x,hx,hv⟩ := v.property
        exact ⟨x,hx,by rw [←he,hv]⟩⟩
      invFun := fun v => ⟨e.symm v, by
        obtain ⟨x,hx,hv⟩ := v.property
        refine ⟨x,hx,?_⟩
        apply e.injective
        rw [he,e.apply_symm_apply,hv]⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v) }
  have hI := Nat.card_congr a
  apply no_seven_aut hP ((Nat.card_congr e.toEquiv).trans hE) <;> omega

private abbrev E := Multiplicative (Fin 3 → ZMod 2)
private instance : IsElementaryAbelian 2 E where
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    decide +kernel
private theorem card_E : Nat.card E=8 := by
  rw [Nat.card_eq_fintype_card]
  decide
namespace Janko
open Sporadic.Janko3 Sporadic.Janko3.TwoLocal
open CentralizerCertificate
private abbrev P := sylowCandidate
private def gp : Fin 5 → Equiv.Perm (Fin 6156) := ![S0G0,S0G1,S0G2,S0G3,S0G4]
private theorem gp_spec (i : Fin 5) : gp i = (sylowGenerator i).val := by
  fin_cases i
  · exact S0G0_eq_generator
  · exact S0G1_eq_generator
  · exact S0G2_eq_generator
  · exact S0G3_eq_generator
  · exact S0G4_eq_generator
private def g (i : Fin 5) : P :=
  ⟨⟨gp i,by rw [gp_spec]; exact (sylowGenerator i).property⟩,by
    have he : (⟨gp i,by rw [gp_spec]; exact (sylowGenerator i).property⟩ : Model) = sylowGenerator i :=
      Subtype.ext (gp_spec i)
    exact he.symm ▸ sylowGenerator_mem i⟩
private theorem card_P : Nat.card P=128 := sylowCandidate_card
private def words : Fin 128 → List (Fin 5) := ![[],[0],[1],[2],[3],[4],[0,1],[0,2],[0,3],[0,4],[1,2],[1,3],[1,4],[2,1],[2,3],[2,4],[3,1],[3,2],[3,4],[4,1],[4,2],[4,3],[0,1,2],[0,1,3],[0,1,4],[0,2,1],[0,2,4],[0,3,1],[0,3,4],[0,4,1],[0,4,2],[0,4,3],[1,2,1],[1,2,3],[1,2,4],[1,3,1],[1,3,2],[1,3,4],[1,4,1],[1,4,2],[1,4,3],[2,1,2],[2,1,3],[2,1,4],[2,3,1],[2,3,4],[2,4,1],[2,4,2],[2,4,3],[3,1,2],[3,1,3],[3,2,1],[3,2,4],[3,4,1],[3,4,2],[3,4,3],[4,1,2],[4,1,4],[4,2,1],[4,2,3],[4,3,1],[4,3,2],[4,3,4],[0,1,2,4],[0,1,3,1],[0,1,3,4],[0,1,4,1],[0,1,4,2],[0,2,1,2],[0,2,1,3],[0,2,4,1],[0,2,4,2],[0,2,4,3],[0,3,1,2],[0,3,1,3],[0,3,4,2],[0,3,4,3],[0,4,1,4],[0,4,2,1],[0,4,3,1],[1,2,1,2],[1,2,1,3],[1,2,3,1],[1,2,3,4],[1,2,4,1],[1,2,4,2],[1,2,4,3],[1,3,1,2],[1,3,1,3],[1,3,2,1],[1,3,2,4],[1,3,4,1],[1,3,4,2],[1,3,4,3],[1,4,1,2],[1,4,1,4],[1,4,2,1],[1,4,2,3],[1,4,3,1],[1,4,3,2],[2,1,2,1],[2,1,2,3],[2,1,3,1],[2,1,3,2],[2,1,4,1],[2,3,1,2],[2,3,1,3],[2,4,1,4],[2,4,2,3],[3,1,2,1],[3,1,2,4],[3,1,3,1],[3,1,3,2],[3,1,3,4],[3,2,1,2],[3,2,1,3],[3,2,4,2],[0,1,2,4,3],[0,1,3,4,3],[0,1,4,1,4],[1,2,1,2,3],[1,2,1,3,2],[1,2,3,1,2],[1,2,3,1,3],[1,2,4,1,4],[1,3,1,3,2],[1,3,2,1,2],[1,3,2,1,3]]
private def enum (i : Fin 128) : P := ((words i).map g).prod
private def point (x : P) : Fin 6156 := (x.val.val : Equiv.Perm (Fin 6156)) 0
private def index (t : Fin 6156) : Fin 128 :=
  ⟨(984109561438830968741374235541010951380471782084785090455179988521235580529706985874209488588524250099748438542072112229620410832925745269183591700280009577711222532980831015030289309280379152104449641429541400744100991729223406561377613732755170951201537078370859456228848052827113354000953691444363525319535575164905453081676526746440079126212942280157627336277916925976023001594031487302451291535754216539962157955991158663639392456981643359511228243501124239610130069834269307474831162004275646291928836705272057078718280756749847077615941527704262107664287590312853337542685103175364660252970214663709308915163187809038794069745212443685198037209065568474068837833111473937554897024822848521176878297115820784833966538664767253100065664791832268325674144242956194206708301506987878652724991746710108507737192534350819103237065944520579715718800564844440875105551597112714546040995218818402807451674640320270751099381526192528969310981835644704047188053893350132046235357154309241314320701895406742057451052260478385955620377284462603246871910253393276585577107836733240828636021848489825950828379046038927639093458942717489862764767581652676983702163984825325744787157771046684035055034735537090438940119807969413124579597724739662051032695924753746341258346881268426600470918688171082834443678166053152295018959331091430702411563635218715464209487042751345943494843355586635570152963736293712696484069026905823533450669023898690374133636034326813457310828410137831391590169490757872704017575355413170438836587941223184625290506372623898370922906518526367488070912365903719630236763779576701639290723264284232880420017881438510845959706238561122437520584017050609250357292302453120324569062053463001631473193574587069252845991822264954158137416105556011886020708393579314175274673166502201211399729926321076874591213035946284770303066871377864019304244888089235470103791791686526597663093994821816546551896189620568905568552283220318387275833889542742282071840045468780207303547551316642805085147038586238582081071958987028314572854906640651580632447454350716596557840547938164988647467339480059033270985105923861416592885237294391641359986760390844593259925293617265295402245597556879245482951735456678964307118804869868325135326913407426487366738334320606359661055697146671335002444132423473527745811416796607695013698213530047714811584323925547434139880402091332459315277348989358033401389484175589524369716646273149753094317419961899520956332000282306357623199799553452318589903994149500350515559522399449981569599006531999649359196253887705565417726681242727545474239763960664207398678714035646878924311282331029448801491331012743854789931651495859132416952010338826585660542549448345162454031805220673870442836421739348259043296511114942214944197073546994293707494332944497236967927445662118017895109616084913789129078568048765829138907027403200946460680699128717396690658187202487559062714465740854536116301685369063674144343367633146815282300017525615672343098807260338314342156194504786110843198137190104117132147746430241342472063203339617495863459642746380793928962276869731904691115330151761701124954518646481900614595478268358296320699197213008670439041375202168598465568785693141542897559132503935478966842572275469055100303065155211770294053360005476185214264670067647091779170520721088451767718485180627422060767316159074293491349133045507220855776614384690515208059217871007943163568292120278844354405904853328911872598844585483431477168081709925299017508837918945338793053264312757211889710797366346031406634081147500871189822323504786445621751743131854728431657456586203496317578059731653090589586720981239283462950811721452708062950072641940020041246591916982663111853729520854474240141996883963059163207669154156598952732953747456039745283688441718067206580793378833012451688053602359122458445899659425816360933742020430978992573929637978469118306964379627609229791139232371339686828254204552004643466248898771881056966247113506638344931221578253312286269567327582055671823757327598365108057334005520059005775797361159397272251966197001034413051378451679527358478681430162969708828161926983680137058033380313549474596792173599355558207127569301256389650779859809515772776904833780449720356241874396773916208268136874876410952407493773303884854020761223003002668968663806937931043899858041999029767177339830576127847823576885676958106518383752589108250821974983776120468358912669128544416134661694269374407222443837330563827887253265556400191017437957456161386926195722607147429255740424578778180003933162402097360061791764440511079102773177834923398022443545051510413188600974687238125017688576494112515486712181431400293723896693001244835687680653439097856072741297424157818644963308598758539059303966635843314559387986258735071526259272388533790230245136504788782154367190212152444492929460363114572954504768343508526982753217520726085191058241277542153562303452661699287431934366617138332364439468979370873203886347446635114468423972043491888272569882874683854591824975355856983307553270490356937240148980464055502009797297028987673097848840280124446354594322164696594861916931277827731333293658443653815072836420799176562040167348073634189350689457902022493295786934960488914213202622477731281872111108897859946915843179906835842097150310128629701712170447544954173628530679209930511490662190929915733956559594236757920042271035956278804751353857572637667454962752203074703036790803058600232332104865889709635699579273235487445040972084812911250542438037141160184671324565177764983487968982205143700667764615035008543674348807982831101744700464115131027368332670124608564043392572504473663579151012517728956429209860409049842628831273938454663642256701111960348858760022629666031200817853070145188915066635664778968871509283743621090908350323840566162785950624578446570603128555273991355823667115056241135638471788115461555911745341149372459137505899976511131972083313741595330597065592668068266072172527831860622570674211983871945489485343253269758602596674214769738654468562743099412182911991926799214025911088891983270548482894809975015171358490305593728873101432742527630444790631834678629079960672509337493086480527704160748323791691594490807436376364341305225866868643201675181263777484036301779543486571877063501405488766439245128900914541625210276950240927550858441703593274761862019938931514246972142446702444102649822147885387422072482583636702100040725903081814102294817887210385139729676679558614872477818986013624969079815720061511906171807130363455694569121531407327307911363198546870302108163292897357055913749317034883174193121778768942862502098183922873485132597945048023218146186225970816964610418290478323460968927661944885178396183540256355177642396305303473819816328742786308136654087225357754416514881480032677017796187262137653853882906204791149604916958073852120192917315470509489445109906595991928294002933779546337900524251006324599942713432359980628266251517701636145453211537990490534215698036538057095095332375660796908348372715548724865834826409938725974165884530167184681699496262793103274104341209501500372583054974618163415113694724864743434551096239773989526688819247711936360444560275043184348706703684254298348423879318906026981557124959869386570037219069587487575040213784631958924627949892104843645931872274268422662839687945584233717189649839308524083592435788165004702761663681567578006381931528644061212878558278816898551882480519662024387005385251132139920500754061503345004796450194425320846450140813976027563914736454796970628662704152479019704968504892011354380152772764189571779242762900088505807159416234565044288358180118688135061781980377365758762948355479691637985442185872281443468230691512474682687142246309474282713897760632791920031461224457528098869396201040018964805762632997619284998348456209991238243550234639762913504314339397373359383328388107163162161229983497513883186563985582714656431407780378637547095995311269052626768608783840054904170247697252264278476947715549280435665246674715135655291235257845117511482015685487924092586008648509482757209053195814879398461927585627136204600079604298415223418599066158535528124423125451855697900843520816079710426006819456198992805610306251371661133754650739706522145347862400051102343558606757376909151071263464858978530620987212081990308847929526041133737621885671708280267289467115102199590715235270988647908898209785371361340088058586269712953244180466190878527906098342567757375353852233228869336914735615478424418848342795501163499247500894037245930376918043317886424622647707742076870142337490023513440334092275170006837241914787701540621246546105603922034830679136206233319251066643556755470283306147234398709044711644162423256551653283946811106148615518382882739981237288971881505965841930974654712463007798085973185697480724849851560321783706312033537874701526383583077447840452859898000677979982640416273580314169396127368853029508593323363539307607332511960247182060366067517447235389449381673405575544765130189689374374232545106035749092905421533246332338833792927081933253091703696795676695231164550201768909395668166640607706473290399363842429079228532060006491541713282438560685681278810664327302156798426145747001806927976853554640856624196634381319161871492901193534970967762150831746007860520384639670957236964477711011762424453823703629139222816018946668697709602459876740974243367409508952652882172577892084579332142807013504796337964705213167390397467817275907146725292308138045119974259660945785230889018903109175043794444931693343379636033068799195807576106780567159196806495413295854249989164601731685964509833957448894888928020823794673576987739163312835009313898434922461655563418055409480234990933058641686429214607207525158102843851060238296707936144284487358853546371560750241220646054171179724858466391066898191462046700969454325020815013814440949672865428059805462710542909205385071208218033177000612457068380852387426538470782549212911373103703625993235094221544578826461798247167720747616257840195227833729183354106960630121473583634799622367245374438356247968708934881733174674093776410712224101522129737648813792555502111478488686422775335534836310073919691793649478395215929153437843479034031076127966191196285847583920464747405316115515689830439198039217248165515104047816763874380448372262349322044795700712575276129803518437922354115074605722507220314149505734794313753062105371251206304656434490902754657389102754219046094773155599448466588416184248108916637965403161105221211555419140585921252046955895931509875389924143857751656180252311282883876949725219330146149262003940013296333541877687501781201542135725124437449247846352083985852259776782194071616335431356800586452157760871276671819791173535638389729056455948355969997277567274722500318879837684077551219498063652274011741953507195729224149420203768178178447243533901357551590502509845782011161870644040461132294296960420188715552915387611861922083201736769035897800648427205453340771836288982292941817880029769969235638806171974550844919425890152828299865548698103985930124688975195635832557785292288296643786656750309609983131123785158735678414290655746282758883437347299431377381885185520990398297917371917170299996443920951791751908709979279703978026615183913970512142250945628203742170266838538435488043761465109450539426073597748749253096576387095926047705867209377585949031847765986184487342456675458857428403618314886721075002981086375405638128293577523287687836640248836838971299382490676105539181565758581994494668927153413373223254895187100084334417814962249578298374572049507518797123888370130429833933873374415432851842320355853987936675823052992924033038855299439118564844453017373013302049486426656564246709969086877452768776112834783995699185212481150144038143386854417797482686332169472203861711029859091717639192956711050070904798374877345776675888418269662020311956258420897065204916753130037631445430799863191252726565444831711399131443576642484538882142995489998331423081787593749300219034661868701195721357948742987954600784013296778805099446124972389231983498584109925191272479767772083564933105596613145455096863301613396952775852187015868151210948860987230284083323531061912277103387448937655256808017938018946173971195816007992805966137493791303495073532069488276478750094673834805016808584800083125060215989316549145563590721761800323560825579541330716432301504458133179759920595737183615775973598057136796721351196526051778644639715217659516025527318042559294739288958697039501608208022899261037128139636409717161244654918325736148758400843528485221622649641745666092691542123810580454321674959420092993833407065989565550532217063521796157268652142650311495291318354115534440684822153811971752211149693524262906434717929191198756336665423995389487102218305776813958254713982900674772302189476867281660766049877110606145640975488675916830991468819693568 >>> (7*t.val)) % 128, Nat.mod_lt _ (by decide)⟩
private theorem index_enum : ∀ i : Fin 128, index (point (enum i))=i := by
  decide +kernel
private theorem enum_bijective : Function.Bijective enum := by
  apply (Nat.bijective_iff_injective_and_card enum).mpr
  refine ⟨fun i j he => ?_,?_⟩
  · rw [←index_enum i,←index_enum j,he]
  · rw [Nat.card_fin,card_P]
private theorem point_injective : Function.Injective point := by
  intro x y he
  obtain ⟨i,rfl⟩ := enum_bijective.surjective x
  obtain ⟨j,rfl⟩ := enum_bijective.surjective y
  have h := congrArg index he
  rw [index_enum,index_enum] at h
  exact congrArg enum h
private def label (x : P) : E := Multiplicative.ofAdd (fun i : Fin 3 =>
  ((11257715595203588104777077461726769462981701300510253925196493979530453584665403450347734149979381187597624878179392 >>> (3*(index (point x)).val+i.val)) % 2 : ZMod 2))
private theorem label_gen_mul : ∀ i : Fin 5, ∀ j : Fin 128,
    label (g i * enum j)=label (g i)*label (enum j) := by
  decide +kernel
private theorem label_one : label 1=1 := by decide +kernel
private theorem label_mul (x y : P) : label (x*y)=label x*label y := by
  have hg (i : Fin 5) (z : P) : label (g i*z)=label (g i)*label z := by
    obtain ⟨j,rfl⟩ := enum_bijective.surjective z
    exact label_gen_mul i j
  have hl (l : List (Fin 5)) :
      label ((l.map g).prod*y)=label (l.map g).prod*label y := by
    induction l with
    | nil => simp only [List.map_nil,List.prod_nil,one_mul,label_one]
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,mul_assoc,hg,ih]
  obtain ⟨i,rfl⟩ := enum_bijective.surjective x
  exact hl (words i)
private def quotientMap : P →* E where
  toFun := label
  map_one' := label_one
  map_mul' := label_mul
private theorem quotientMap_surjective : Function.Surjective quotientMap := by
  have h : ∀ v : E, ∃ i : Fin 128, label (enum i)=v := by decide +kernel
  exact fun v => let ⟨i,hi⟩ := h v; ⟨enum i,hi⟩
private def smallImages : Set E :=
  {v | ∃ i : Fin 128, point (enum i ^ 2)=point 1 ∧ label (enum i)=v}
private theorem smallImages_card : Nat.card smallImages=5 := by
  let : DecidablePred (fun v => v ∈ smallImages) := fun v => inferInstanceAs (Decidable (∃ i : Fin 128, point (enum i ^ 2)=point 1 ∧ label (enum i)=v))
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem image_card : Nat.card {v : E // ∃ x : P, x^2=1 ∧ quotientMap x=v}=5 := by
  have he : ({v : E | ∃ x : P, x^2=1 ∧ quotientMap x=v})=smallImages := by
    ext v
    constructor
    · rintro ⟨x,hx,hv⟩
      obtain ⟨i,rfl⟩ := enum_bijective.surjective x
      exact ⟨i,congrArg point hx,hv⟩
    · rintro ⟨i,hi,hv⟩
      exact ⟨enum i,point_injective hi,hv⟩
  change Nat.card ({v : E | ∃ x : P, x^2=1 ∧ quotientMap x=v}) = _
  rw [he]
  exact smallImages_card
end Janko
namespace McLaughlin
open Sporadic.LeechRelated.McL Sporadic.LeechRelated.McL.FrattiniEight
private abbrev P := candidate
private def g (i : Fin 3) : P := ⟨gen i.castSucc.castSucc.castSucc.castSucc,
  candidate_gen_mem i.castSucc.castSucc.castSucc.castSucc⟩
private theorem card_P : Nat.card P=128 := candidate_card
private def words : Fin 128 → List (Fin 3) := ![[],[0],[1],[2],[0,0],[0,1],[0,2],[1,0],[1,2],[2,0],[2,1],[2,2],[0,0,0],[0,0,1],[0,0,2],[0,1,2],[0,2,0],[0,2,1],[0,2,2],[1,0,2],[1,2,0],[1,2,1],[1,2,2],[2,0,0],[2,0,1],[2,0,2],[2,1,0],[2,1,2],[2,2,2],[0,0,0,2],[0,0,1,2],[0,0,2,0],[0,0,2,1],[0,0,2,2],[0,1,2,0],[0,1,2,1],[0,1,2,2],[0,2,0,0],[0,2,0,1],[0,2,0,2],[0,2,1,0],[0,2,1,2],[0,2,2,2],[1,0,2,0],[1,0,2,1],[1,0,2,2],[1,2,0,0],[1,2,0,1],[1,2,0,2],[1,2,1,0],[1,2,1,2],[1,2,2,2],[2,0,0,0],[2,0,0,1],[2,0,0,2],[2,0,1,2],[2,0,2,0],[2,0,2,1],[2,0,2,2],[2,1,0,2],[2,1,2,0],[2,1,2,2],[0,0,0,2,0],[0,0,0,2,1],[0,0,0,2,2],[0,0,1,2,0],[0,0,1,2,1],[0,0,1,2,2],[0,0,2,0,0],[0,0,2,0,1],[0,0,2,0,2],[0,0,2,1,0],[0,0,2,1,2],[0,0,2,2,2],[0,1,2,0,0],[0,1,2,0,1],[0,1,2,0,2],[0,1,2,1,0],[0,1,2,1,2],[0,1,2,2,2],[0,2,0,0,0],[0,2,0,0,1],[0,2,0,0,2],[0,2,0,1,2],[0,2,0,2,0],[0,2,0,2,1],[0,2,0,2,2],[0,2,1,0,2],[0,2,1,2,0],[0,2,1,2,2],[1,0,2,0,2],[1,0,2,1,0],[1,0,2,1,2],[1,2,0,0,0],[1,2,0,0,2],[1,2,0,1,2],[1,2,0,2,0],[1,2,0,2,1],[1,2,1,0,2],[1,2,1,2,0],[2,0,1,2,1],[2,0,2,2,2],[2,1,0,2,2],[0,0,0,2,0,0],[0,0,0,2,0,1],[0,0,0,2,0,2],[0,0,0,2,1,0],[0,0,0,2,1,2],[0,0,0,2,2,2],[0,0,1,2,0,2],[0,0,1,2,1,0],[0,0,1,2,1,2],[0,0,2,0,0,0],[0,0,2,0,0,2],[0,0,2,0,1,2],[0,0,2,0,2,0],[0,0,2,1,2,0],[0,1,2,0,0,0],[0,1,2,0,1,2],[0,1,2,0,2,0],[0,1,2,0,2,1],[0,1,2,1,0,2],[0,2,0,2,2,2],[0,2,1,0,2,2],[1,0,2,0,2,0],[0,0,0,2,0,0,0],[0,0,0,2,0,1,2],[0,0,1,2,0,2,0]]
private def enum (i : Fin 128) : P := ((words i).map g).prod
private def point (x : P) : Fin 275 × Fin 275 := ((x.val.val : Equiv.Perm (Fin 275)) 1,(x.val.val : Equiv.Perm (Fin 275)) 2)
private def index (t : Fin 275 × Fin 275) : Fin 128 :=
  let a := (356141794427959280306550761534525378620949241776628013757528623215187535519629956795186577744803167789360013562038855492066913411738565174166322194427869346696577285946128260985881147989642761453697790074353444723302423443892801425185731314406640806531880568792459073246126436412440446830467293780842887196186082030897522849062094811628683678763891176966838072099333567917748775157979487436172293599664178646050005417072574886050132165292619504044263916218618357997869799523295227763242502470534219378298509077112798942464544158170223926588606779873476080364755911682249015164928 >>> (7*t.1.val)) % 128
  let b := (169821641767132357995810313681111850944814124845293119806856792143155369075442134562021296661277881038999254351709344073293381533447188669879381575281858680808578483732654909014891128255667208653574268135653663213864615588575888645095619207179698628004865936336404815631283809825028870194509563025203433797281183554728848564240387945090168397750784903603011839865936251379111898645917319196609960566161888115751442148238682016634237175210578201213877817223842694521829107647112189472375070320709707824677138177147874534912602324793448231660912590657288063020861285258493952 >>> (7*t.2.val)) % 128
  ⟨(30529621227465575143911986367890815498810066380000367276113848654078254057366683236549216680748020996095769841089701279661317741330505978079460425247544758423922135736984450109595481319467371475699658419221846760003232295889716931106345489505884462630615147006764774877341859609047728509376082960496645191852755061621375005893221118329245835853833573355730237296757297893333958471831671637193743831208960295348729373119846214573759521269867903792103704594926266027356971383103679498602590756114067828785381823623975764739277968637851336704 >>> (7*(a+16*b))) % 128, Nat.mod_lt _ (by decide)⟩
private theorem index_enum : ∀ i : Fin 128, index (point (enum i))=i := by
  decide +kernel
private theorem enum_bijective : Function.Bijective enum := by
  apply (Nat.bijective_iff_injective_and_card enum).mpr
  refine ⟨fun i j he => ?_,?_⟩
  · rw [←index_enum i,←index_enum j,he]
  · rw [Nat.card_fin,card_P]
private theorem point_injective : Function.Injective point := by
  intro x y he
  obtain ⟨i,rfl⟩ := enum_bijective.surjective x
  obtain ⟨j,rfl⟩ := enum_bijective.surjective y
  have h := congrArg index he
  rw [index_enum,index_enum] at h
  exact congrArg enum h
private def label (x : P) : E := Multiplicative.ofAdd (fun i : Fin 3 =>
  ((11425716940189849920306448473829959768896105583511188125934221516111729696964824536323121458604861066490852559653000 >>> (3*(index (point x)).val+i.val)) % 2 : ZMod 2))
private theorem label_gen_mul : ∀ i : Fin 3, ∀ j : Fin 128,
    label (g i * enum j)=label (g i)*label (enum j) := by
  decide +kernel
private theorem label_one : label 1=1 := by decide +kernel
private theorem label_mul (x y : P) : label (x*y)=label x*label y := by
  have hg (i : Fin 3) (z : P) : label (g i*z)=label (g i)*label z := by
    obtain ⟨j,rfl⟩ := enum_bijective.surjective z
    exact label_gen_mul i j
  have hl (l : List (Fin 3)) :
      label ((l.map g).prod*y)=label (l.map g).prod*label y := by
    induction l with
    | nil => simp only [List.map_nil,List.prod_nil,one_mul,label_one]
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,mul_assoc,hg,ih]
  obtain ⟨i,rfl⟩ := enum_bijective.surjective x
  exact hl (words i)
private def quotientMap : P →* E where
  toFun := label
  map_one' := label_one
  map_mul' := label_mul
private theorem quotientMap_surjective : Function.Surjective quotientMap := by
  have h : ∀ v : E, ∃ i : Fin 128, label (enum i)=v := by decide +kernel
  exact fun v => let ⟨i,hi⟩ := h v; ⟨enum i,hi⟩
private def smallImages : Set E :=
  {v | ∃ i : Fin 128, point (enum i ^ 2)=point 1 ∧ label (enum i)=v}
private theorem smallImages_card : Nat.card smallImages=4 := by
  let : DecidablePred (fun v => v ∈ smallImages) := fun v => inferInstanceAs (Decidable (∃ i : Fin 128, point (enum i ^ 2)=point 1 ∧ label (enum i)=v))
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem image_card : Nat.card {v : E // ∃ x : P, x^2=1 ∧ quotientMap x=v}=4 := by
  have he : ({v : E | ∃ x : P, x^2=1 ∧ quotientMap x=v})=smallImages := by
    ext v
    constructor
    · rintro ⟨x,hx,hv⟩
      obtain ⟨i,rfl⟩ := enum_bijective.surjective x
      exact ⟨i,congrArg point hx,hv⟩
    · rintro ⟨i,hi,hv⟩
      exact ⟨enum i,point_injective hi,hv⟩
  change Nat.card ({v : E | ∃ x : P, x^2=1 ∧ quotientMap x=v}) = _
  rw [he]
  exact smallImages_card
end McLaughlin

namespace Janko
open Sporadic.Janko3 Sporadic.Janko3.TwoLocal
private theorem sylow_aut_no_seven : ¬ 7 ∣ Nat.card (MulAut P) :=
  no_seven_aut_of_quotient sylowCandidate_isPGroup card_P
    FrattiniEight.candidate_frattini_card_le_eight card_E quotientMap
    quotientMap_surjective (Or.inr image_card)
end Janko

namespace McLaughlin
open Sporadic.LeechRelated.McL
open Sporadic.LeechRelated.McL.FrattiniEight
private theorem candidate_index_odd : ¬ 2 ∣ candidate.index := by
  have hc := candidate.index_mul_card
  rw [candidate_card,
    Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
    Atlas.Sporadic.McLaughlin.card] at hc
  norm_num [Atlas.Sporadic.McLaughlin.order] at hc
  omega
private def sylow : Sylow 2 Carrier :=
  (IsPGroup.of_card (n:=7) candidate_card).toSylow candidate_index_odd
private theorem sylow_aut_no_seven : ¬ 7 ∣ Nat.card (MulAut P) :=
  no_seven_aut_of_quotient (IsPGroup.of_card (n:=7) candidate_card) card_P
    (sylow_frattini_card_le_eight sylow) card_E quotientMap
    quotientMap_surjective (Or.inl image_card)
end McLaughlin

/-- The involution-coset obstruction excludes seven from the automorphisms
of every literal J₃ Sylow two-subgroup. -/
theorem janko_three_sylow_aut_no_seven {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Sporadic.Janko3.Model) (P : Sylow 2 Q) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let S : Sylow 2 Sporadic.Janko3.Model := Sporadic.Janko3.TwoLocal.sylowCandidate_isPGroup.toSylow (by
    have hc := Sporadic.Janko3.TwoLocal.sylowCandidate.index_mul_card
    rw [Sporadic.Janko3.TwoLocal.sylowCandidate_card,Sporadic.Janko3.model_card] at hc
    omega)
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let a := (P.equivMapOfInjective e.toMonoidHom e.injective).trans (R.equiv S)
  rw [Nat.card_congr (MulAut.congr a).toEquiv]
  exact Janko.sylow_aut_no_seven

/-- The distinct McL involution-coset profile gives the same obstruction,
transported through the actual permutation model. -/
theorem mcl_sylow_aut_no_seven {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Sporadic.LeechRelated.McL.Carrier) (P : Sylow 2 Q) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let a := (P.equivMapOfInjective e.toMonoidHom e.injective).trans (R.equiv McLaughlin.sylow)
  rw [Nat.card_congr (MulAut.congr a).toEquiv]
  exact McLaughlin.sylow_aut_no_seven

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- The original SL₃(2) outer section cannot occur on a J₃ component. -/
theorem janko_three_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.Janko3.Model)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply janko_three_sylow_aut_no_seven e P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- The original SL₃(2) outer section cannot occur on a McL component. -/
theorem mcl_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.LeechRelated.McL.Carrier)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply mcl_sylow_aut_no_seven e P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- Both exclusions descend through the full center of the same component. -/
theorem cover_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) ∧
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.McL.Carrier) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  exact ⟨fun ⟨e⟩ => janko_three_no_outer_section e _ g hg,
    fun ⟨e⟩ => mcl_no_outer_section e _ g hg⟩

/-- The five remaining actual outer models, with their literal markings. -/
inductive RemainingOuterModel (Q : Type*) [Group Q] : Prop
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : ClassificationModels.IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)

/-- Inspect the original B catalogue against the actual outer section. -/
theorem remaining_outer_models {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  obtain ⟨hJ,hM⟩ := cover_exclusions ho
  cases DoubledBinaryOddTernary.remaining_outer_models hm ho with
  | symplectic_odd p hp hq e => exact .symplectic_odd p hp hq e
  | g2_odd p hp hq e => exact .g2_odd p hp hq e
  | linear_four p hp hf e => exact .linear_four p hp hf e
  | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | symplectic_binary e => exact .symplectic_binary e
  | janko_three e => exact (hJ e).elim
  | mcl e => exact (hM e).elim
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
