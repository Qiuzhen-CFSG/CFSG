module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalSubgroup
public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.Arithmetic

/-!
# A certified fixed column for the Harada–Norton local subgroup

The two generators of `localSubgroup` fix the explicit column `indexBaseVector`.
For the second generator we check an 85-step trace through the original ATLAS
matrices, then assemble it using the matrix multiplication law. Every numerical
transition is proved by kernel reduction of the sound packed arithmetic check.
This establishes invariance only; no orbit size or stabilizer equality is assumed.

Source: ATLAS `HNG1-f5r133B0` and `HNG1-max1W1`, preserved in this repository.
`source/GenerateFixedVector.py` regenerates these candidate columns and checks.
-/

namespace HaradaNorton.OrderCertificate
open Matrix IndexArithmetic

set_option maxRecDepth 10000

/-- The local subgroup's fixed column, with coordinates numbered from zero. -/
@[expose] public def indexBaseVector : Fin 133 → ZMod 5 :=
  decodeVector 7356805056032756666280340672879087256176537339049541553432590293310371378409980811848287781

private def column1 : Fin 133 → ZMod 5 :=
  decodeVector 169038439848444820392343843786515478055498115103022882313343590342381508137008576051525489511

private def column2 : Fin 133 → ZMod 5 :=
  decodeVector 68538490884402738343062020615299437153446739526405433469521660679719136142731308235303532082

private def column3 : Fin 133 → ZMod 5 :=
  decodeVector 314581220463461913585315231403948265342269668279139275945540248814040072753735388284785042

private def column4 : Fin 133 → ZMod 5 :=
  decodeVector 248734511354035452795061952476152638594488795881014971188175816283663292610135138098400497153

private def column5 : Fin 133 → ZMod 5 :=
  decodeVector 357115842540345004683091824802720095075965462594905401662370991372387880764961739661672360385

private def column6 : Fin 133 → ZMod 5 :=
  decodeVector 45563026382512039233292226516055919955701557171010366589372087280295700140362284858701588175

private def column7 : Fin 133 → ZMod 5 :=
  decodeVector 171728461913506285653226121716866112549288101686408196448585642529451783122442551459475159400

private def column8 : Fin 133 → ZMod 5 :=
  decodeVector 7571722261641492476505622409640448267860180506586367710608608621643512742293479103095703255

private def column9 : Fin 133 → ZMod 5 :=
  decodeVector 80885297010170040061664114032826798233726721025429705631708604645382524805978417390363671881

private def column10 : Fin 133 → ZMod 5 :=
  decodeVector 742044987268885896193352837781200315688208255935962515406783387863906887593795685029355487626

private def column11 : Fin 133 → ZMod 5 :=
  decodeVector 192842631830249736716176453954609367290753289039934346772066369342082388364306179168703597626

private def column12 : Fin 133 → ZMod 5 :=
  decodeVector 324792021909440214282796494618855065036824705045808938954636854355363781228728392674843769530

private def column13 : Fin 133 → ZMod 5 :=
  decodeVector 773432506149797137173357740525226343133009452753125938476497258352903789033066369354988613280

private def column14 : Fin 133 → ZMod 5 :=
  decodeVector 154354090724110763210924696330292373316914923849314739184283958104060940445602257635899752531

private def column15 : Fin 133 → ZMod 5 :=
  decodeVector 154354090724110763210924696330292373316914923849314739184283958104060940445602257635899752531

private def column16 : Fin 133 → ZMod 5 :=
  decodeVector 663920088230521139137478597742393273505439095603090253539555949397708316370943072537873525851

private def column17 : Fin 133 → ZMod 5 :=
  decodeVector 1482048720949801109617533610753163339838203268662467086191876744706921511948185121890878521

private def column18 : Fin 133 → ZMod 5 :=
  decodeVector 147818982470629921788330477201503860781664912582437617639623670139135286459820866400441064519

private def column19 : Fin 133 → ZMod 5 :=
  decodeVector 611564980445303454533628951913971226584047240782804575063398552495055017277910868275148841208

private def column20 : Fin 133 → ZMod 5 :=
  decodeVector 192499590788384628629100273391806532006493845557883066082659844369251634963157810414601575543

private def column21 : Fin 133 → ZMod 5 :=
  decodeVector 229562465354744964568732450548041548702057908068942944720626011597648053440225219759343062898

private def column22 : Fin 133 → ZMod 5 :=
  decodeVector 360041765274294312002521074488248863863900935952736025182507120491212775060844922033702791644

private def column23 : Fin 133 → ZMod 5 :=
  decodeVector 44431806615427290917193200674452475635069232662737224511407448579603813776865028387890730454

private def column24 : Fin 133 → ZMod 5 :=
  decodeVector 192865920679537934497045511251134432152119207945915326244023386453848822385127550667238907465

private def column25 : Fin 133 → ZMod 5 :=
  decodeVector 198332879418722961161112652115257284342270363587517273587069014423556996623042128450519559465

private def column26 : Fin 133 → ZMod 5 :=
  decodeVector 905116560091381805334178863314432859438594224726305253925311855082784104207715325202540484378

private def column27 : Fin 133 → ZMod 5 :=
  decodeVector 155227418488298309586433139841506146370338052070479886782358648730270938025331618751233996000

private def column28 : Fin 133 → ZMod 5 :=
  decodeVector 147187972794995097406405910882186591102766707866166290531688253179107643688085399666701306625

private def column29 : Fin 133 → ZMod 5 :=
  decodeVector 233678967268956892184572145324720314874215749255023156594313114788881507771956982445814078765

private def column30 : Fin 133 → ZMod 5 :=
  decodeVector 207583285116771574086260155416869426596619795604374932049317436986301695028257444783162203825

private def column31 : Fin 133 → ZMod 5 :=
  decodeVector 8891420947826934070265406579619865595087073960064092972803880485894398773539146586920610025

private def column32 : Fin 133 → ZMod 5 :=
  decodeVector 67652526467919384100007478524193755364998891088267750366789488300437315522446659116296893130

private def column33 : Fin 133 → ZMod 5 :=
  decodeVector 36494883641189082898033323307298788152580617443688566716827097098285449740609565896003968851

private def column34 : Fin 133 → ZMod 5 :=
  decodeVector 753863975556097984132211042128183030281222434712134193313227006920491702520551704991458986896

private def column35 : Fin 133 → ZMod 5 :=
  decodeVector 890505620827175698585238854972349153601623185117137568603153117510830164528198337556337922104

private def column36 : Fin 133 → ZMod 5 :=
  decodeVector 38575180490611641621944131644699578248552859333076117445758683663376231315471683514404609880

private def column37 : Fin 133 → ZMod 5 :=
  decodeVector 707080634911174453905836583001764195618829217134571070804938244884706234376062446600380871900

private def column38 : Fin 133 → ZMod 5 :=
  decodeVector 228126704199218586853139901543505928632129749298869913709610445049984268725220687048097734375

private def column39 : Fin 133 → ZMod 5 :=
  decodeVector 242820191321309606233188393784684470194475202666054525227310535501636127775917225007550406875

private def column40 : Fin 133 → ZMod 5 :=
  decodeVector 623362946646379906104047504354794130644272325939161436170281679144288646073713207910355328750

private def column41 : Fin 133 → ZMod 5 :=
  decodeVector 146997828559869600650967761258098357463083303703447711548392477432953334481763882727263701900

private def column42 : Fin 133 → ZMod 5 :=
  decodeVector 323626874093685677325202057038264232760208750439013094814733932719451859639945446031739969880

private def column43 : Fin 133 → ZMod 5 :=
  decodeVector 162171186388680612463763709362923151228239328615330642824900515787234185330271839927982825671

private def column44 : Fin 133 → ZMod 5 :=
  decodeVector 891635953902766821169121181776858778119536382402106346659935094069221682077944446565923940779

private def column45 : Fin 133 → ZMod 5 :=
  decodeVector 552729116915737645314330645713951660198324712907663570030013922512472956515657908682873051384

private def column46 : Fin 133 → ZMod 5 :=
  decodeVector 39440770287609868492144524571015135974228539416063801974166069849177070079684922639419938056

private def column47 : Fin 133 → ZMod 5 :=
  decodeVector 303221998095756973820691121589239788318491613178292404031744720968428394952223317014406341286

private def column48 : Fin 133 → ZMod 5 :=
  decodeVector 747969026623827508373825476932009815870344703975367383024760650833198629667761346136248532027

private def column49 : Fin 133 → ZMod 5 :=
  decodeVector 780517136215628824165071899802409347481368152055604094352684548824934871906204715129705175632

private def column50 : Fin 133 → ZMod 5 :=
  decodeVector 1706461175592787126966020965891252477547067662815745428540771081694910377040487406301235276

private def column51 : Fin 133 → ZMod 5 :=
  decodeVector 339413326038912526635246365075262126439436643766285613443849223369904938385303151124810961881

private def column52 : Fin 133 → ZMod 5 :=
  decodeVector 337985775575541319937607633182428126419217489573562786541332913340829080203545209362119972101

private def column53 : Fin 133 → ZMod 5 :=
  decodeVector 175748743642318299858887499780984004476935601860020762501956592399214425361228585223831178255

private def column54 : Fin 133 → ZMod 5 :=
  decodeVector 222452583582287988132432617210338971036078518023483519055471089116280697656050263252335550275

private def column55 : Fin 133 → ZMod 5 :=
  decodeVector 14416729185786137242271053547403315277937235493321012735923369583047692919051640503186028135

private def column56 : Fin 133 → ZMod 5 :=
  decodeVector 737270903377057509512591560607036152088747184185462085533379998158434290648768603947568769377

private def column57 : Fin 133 → ZMod 5 :=
  decodeVector 742160609257393444951105695518439725491963603407147143200170127295105043062871379755670407002

private def column58 : Fin 133 → ZMod 5 :=
  decodeVector 220805523850774326986808696676509759585424463477064019383731879413986955092322849315400050905

private def column59 : Fin 133 → ZMod 5 :=
  decodeVector 909551074069969391446303883758746965522358604090059747171110325591641040526688701640829789530

private def column60 : Fin 133 → ZMod 5 :=
  decodeVector 830555968353253976432681139746620588159150307748340240696105753424997096933174153177980622581

private def column61 : Fin 133 → ZMod 5 :=
  decodeVector 184250306182227969295909886273620899281795403579937088832544709731956385125517975489270563276

private def column62 : Fin 133 → ZMod 5 :=
  decodeVector 155861357137354383647921398617362679808704332555267984057344856641453344525168025245488378756

private def column63 : Fin 133 → ZMod 5 :=
  decodeVector 72060339795566188819513266809271634642843696166104663973413723151986445376369381721447266401

private def column64 : Fin 133 → ZMod 5 :=
  decodeVector 190961427123858982784986539633199386532751517281976764806100328777687427222919484529054784381

private def column65 : Fin 133 → ZMod 5 :=
  decodeVector 45514707177479635700757389286278698507439326406712578345198498709654208080775759283877360126

private def column66 : Fin 133 → ZMod 5 :=
  decodeVector 66659967993174429376233678897033280165509833547492606564799053839730913752333188330860878751

private def column67 : Fin 133 → ZMod 5 :=
  decodeVector 846718835880876291697383423813430219241473801208772363802989993064783188663434986366360558900

private def column68 : Fin 133 → ZMod 5 :=
  decodeVector 198705109251770320366937057427883778047290144424764682451591234406515262134733506013333269130

private def column69 : Fin 133 → ZMod 5 :=
  decodeVector 67239148104011646725660429728236163620721063674474627314411083085867142351365204645019556266

private def column70 : Fin 133 → ZMod 5 :=
  decodeVector 578157139510374811226377130263033312501559968227062565551506429759032443285057664191414453253

private def column71 : Fin 133 → ZMod 5 :=
  decodeVector 11767267405180568031220306249177997053800739965980400370539804054077388832278273662402346878

private def column72 : Fin 133 → ZMod 5 :=
  decodeVector 361840226609785219336045245110116633340278898733283602613514336008401955492568305969689844125

private def column73 : Fin 133 → ZMod 5 :=
  decodeVector 148700563390828949424381642050069171269710705598593136692202285791104666896689450227051190640

private def column74 : Fin 133 → ZMod 5 :=
  decodeVector 601313246420167568133582622831445182708126170426851014318093462845368984400942329413136719575

private def column75 : Fin 133 → ZMod 5 :=
  decodeVector 338061157664006347772023010107334684085173486643440219930496831057101971693415790711672515655

private def column76 : Fin 133 → ZMod 5 :=
  decodeVector 670020619561222274504193811704015300688395859611718481847568712139401030729451656843341797530

private def column77 : Fin 133 → ZMod 5 :=
  decodeVector 817367778930353422321764754346471670136659813929129850612018383417689498553050999176185640651

private def column78 : Fin 133 → ZMod 5 :=
  decodeVector 742563167024939542918095669060569284208426976926507864839362021275536484085360150398105578875

private def column79 : Fin 133 → ZMod 5 :=
  decodeVector 882200499392509638651421192347946462727348370769622888989673272331929316007139991943616504375

private def column80 : Fin 133 → ZMod 5 :=
  decodeVector 45563026382512039233292226516055919955701557171010366589372087280295700140362284858701588175

private def column81 : Fin 133 → ZMod 5 :=
  decodeVector 357115842540345004683091824802720095075965462594905401662370991372387880764961739661672360385

private def column82 : Fin 133 → ZMod 5 :=
  decodeVector 314581220463461913585315231403948265342269668279139275945540248814040072753735388284785042

private def column83 : Fin 133 → ZMod 5 :=
  decodeVector 68538490884402738343062020615299437153446739526405433469521660679719136142731308235303532082

private def column84 : Fin 133 → ZMod 5 :=
  decodeVector 7356805056032756666280340672879087256176537339049541553432590293310371378409980811848287781

/-- The first local generator fixes the candidate column. -/
public theorem aMatrix_mulVec_indexBaseVector :
    aMatrix *ᵥ indexBaseVector = indexBaseVector :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition0 :
    bMatrix *ᵥ indexBaseVector = column1 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition1 :
    bMatrix *ᵥ column1 = column2 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition2 :
    aMatrix *ᵥ column2 = column3 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition3 :
    bMatrix *ᵥ column3 = column4 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition4 :
    bMatrix *ᵥ column4 = column5 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition5 :
    aMatrix *ᵥ column5 = column6 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition6 :
    bMatrix *ᵥ column6 = column7 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition7 :
    aMatrix *ᵥ column7 = column8 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition8 :
    bMatrix *ᵥ column8 = column9 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition9 :
    bMatrix *ᵥ column9 = column10 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition10 :
    aMatrix *ᵥ column10 = column11 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition11 :
    bMatrix *ᵥ column11 = column12 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition12 :
    aMatrix *ᵥ column12 = column13 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition13 :
    bMatrix *ᵥ column13 = column14 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition14 :
    aMatrix *ᵥ column14 = column15 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition15 :
    bMatrix *ᵥ column15 = column16 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition16 :
    aMatrix *ᵥ column16 = column17 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition17 :
    bMatrix *ᵥ column17 = column18 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition18 :
    bMatrix *ᵥ column18 = column19 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition19 :
    aMatrix *ᵥ column19 = column20 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition20 :
    bMatrix *ᵥ column20 = column21 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition21 :
    bMatrix *ᵥ column21 = column22 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition22 :
    aMatrix *ᵥ column22 = column23 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition23 :
    bMatrix *ᵥ column23 = column24 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition24 :
    aMatrix *ᵥ column24 = column25 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition25 :
    bMatrix *ᵥ column25 = column26 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition26 :
    bMatrix *ᵥ column26 = column27 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition27 :
    aMatrix *ᵥ column27 = column28 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition28 :
    bMatrix *ᵥ column28 = column29 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition29 :
    aMatrix *ᵥ column29 = column30 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition30 :
    bMatrix *ᵥ column30 = column31 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition31 :
    aMatrix *ᵥ column31 = column32 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition32 :
    bMatrix *ᵥ column32 = column33 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition33 :
    aMatrix *ᵥ column33 = column34 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition34 :
    bMatrix *ᵥ column34 = column35 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition35 :
    bMatrix *ᵥ column35 = column36 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition36 :
    aMatrix *ᵥ column36 = column37 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition37 :
    bMatrix *ᵥ column37 = column38 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition38 :
    bMatrix *ᵥ column38 = column39 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition39 :
    aMatrix *ᵥ column39 = column40 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition40 :
    bMatrix *ᵥ column40 = column41 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition41 :
    aMatrix *ᵥ column41 = column42 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition42 :
    bMatrix *ᵥ column42 = column43 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition43 :
    bMatrix *ᵥ column43 = column44 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition44 :
    aMatrix *ᵥ column44 = column45 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition45 :
    bMatrix *ᵥ column45 = column46 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition46 :
    aMatrix *ᵥ column46 = column47 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition47 :
    bMatrix *ᵥ column47 = column48 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition48 :
    aMatrix *ᵥ column48 = column49 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition49 :
    bMatrix *ᵥ column49 = column50 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition50 :
    aMatrix *ᵥ column50 = column51 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition51 :
    bMatrix *ᵥ column51 = column52 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition52 :
    bMatrix *ᵥ column52 = column53 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition53 :
    aMatrix *ᵥ column53 = column54 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition54 :
    bMatrix *ᵥ column54 = column55 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition55 :
    bMatrix *ᵥ column55 = column56 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition56 :
    aMatrix *ᵥ column56 = column57 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition57 :
    bMatrix *ᵥ column57 = column58 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition58 :
    aMatrix *ᵥ column58 = column59 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition59 :
    bMatrix *ᵥ column59 = column60 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition60 :
    bMatrix *ᵥ column60 = column61 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition61 :
    aMatrix *ᵥ column61 = column62 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition62 :
    bMatrix *ᵥ column62 = column63 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition63 :
    aMatrix *ᵥ column63 = column64 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition64 :
    bMatrix *ᵥ column64 = column65 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition65 :
    aMatrix *ᵥ column65 = column66 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition66 :
    bMatrix *ᵥ column66 = column67 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition67 :
    aMatrix *ᵥ column67 = column68 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition68 :
    bMatrix *ᵥ column68 = column69 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition69 :
    bMatrix *ᵥ column69 = column70 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition70 :
    aMatrix *ᵥ column70 = column71 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition71 :
    bMatrix *ᵥ column71 = column72 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition72 :
    bMatrix *ᵥ column72 = column73 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition73 :
    aMatrix *ᵥ column73 = column74 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition74 :
    bMatrix *ᵥ column74 = column75 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition75 :
    aMatrix *ᵥ column75 = column76 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition76 :
    bMatrix *ᵥ column76 = column77 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition77 :
    bMatrix *ᵥ column77 = column78 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition78 :
    aMatrix *ᵥ column78 = column79 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition79 :
    bMatrix *ᵥ column79 = column80 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition80 :
    aMatrix *ᵥ column80 = column81 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition81 :
    bMatrix *ᵥ column81 = column82 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition82 :
    aMatrix *ᵥ column82 = column83 :=
  checkVector_sound aRows _ _ (by decide +kernel)

private theorem transition83 :
    bMatrix *ᵥ column83 = column84 :=
  checkVector_sound bRows _ _ (by decide +kernel)

private theorem transition84 :
    aMatrix *ᵥ column84 = indexBaseVector :=
  checkVector_sound aRows _ _ (by decide +kernel)

/-- The complete ATLAS local word fixes the same column. -/
public theorem localB_mulVec_indexBaseVector :
    matrixHom localB *ᵥ indexBaseVector = indexBaseVector := by
  simp only [localB, localBBase, map_mul, map_one, matrixHom_a, matrixHom_b,
    pow_succ, pow_zero, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transition0, transition1, transition2, transition3, transition4, transition5, transition6, transition7, transition8, transition9, transition10, transition11, transition12, transition13, transition14, transition15, transition16, transition17, transition18, transition19, transition20, transition21, transition22, transition23, transition24, transition25, transition26, transition27, transition28, transition29, transition30, transition31, transition32, transition33, transition34, transition35, transition36, transition37, transition38, transition39, transition40, transition41, transition42, transition43, transition44, transition45, transition46, transition47, transition48, transition49, transition50, transition51, transition52, transition53, transition54, transition55, transition56, transition57, transition58, transition59, transition60, transition61, transition62, transition63, transition64, transition65, transition66, transition67, transition68, transition69, transition70, transition71, transition72, transition73, transition74, transition75, transition76, transition77, transition78, transition79, transition80, transition81, transition82, transition83, transition84]

end HaradaNorton.OrderCertificate
