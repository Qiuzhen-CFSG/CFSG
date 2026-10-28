module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.Rows
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.Core

/-!
# Elimination identities and predecessor bounds

Finite witness from the saved full Gaussian elimination. Every identity
is checked in Lean; see KernelSpanning/source/README.md.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
namespace Trace2432
open LinearMembership GeneratorCertificates Binary

private def Step (i : ℕ) : Prop := ∃ ps : List ℕ,
  (∀ j ∈ ps, j < i) ∧ row i = base i ^^^ xorList (ps.map row)

private def parents0 : List ℕ := decodeParents 30 748421612023117315470221819434925587226192336231792488061762448334741333818329495912305823317112727607870152833026317

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check0 :
    (∀ j ∈ parents0, j < 2432) ∧
    row 2432 = base 2432 ^^^ xorList (parents0.map row) := by decide +kernel

private theorem certified0 : Step 2432 := ⟨parents0, check0⟩

private def parents1 : List ℕ := decodeParents 35 27623242114526147159508692412302764874486700775122811302542908520771489462878359313901208766916330425069632770211547158992180994776811783

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check1 :
    (∀ j ∈ parents1, j < 2433) ∧
    row 2433 = base 2433 ^^^ xorList (parents1.map row) := by decide +kernel

private theorem certified1 : Step 2433 := ⟨parents1, check1⟩

private def parents2 : List ℕ := decodeParents 26 166114612887498476661174670205995843327231905253381713903116591071401244908939314260697657138987182342

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check2 :
    (∀ j ∈ parents2, j < 2434) ∧
    row 2434 = base 2434 ^^^ xorList (parents2.map row) := by decide +kernel

private theorem certified2 : Step 2434 := ⟨parents2, check2⟩

private def parents3 : List ℕ := decodeParents 33 411956864761776967700975436636841333131763414437016272733656225330972484570329497254420606460773335449168303653786134253803186431

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check3 :
    (∀ j ∈ parents3, j < 2435) ∧
    row 2435 = base 2435 ^^^ xorList (parents3.map row) := by decide +kernel

private theorem certified3 : Step 2435 := ⟨parents3, check3⟩

private def parents4 : List ℕ := decodeParents 34 3376137309456846301164170226618554671177399359650739851517471685549286025189451416772575289907458384340747971445417523023687862233348

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check4 :
    (∀ j ∈ parents4, j < 2436) ∧
    row 2436 = base 2436 ^^^ xorList (parents4.map row) := by decide +kernel

private theorem certified4 : Step 2436 := ⟨parents4, check4⟩

private def parents5 : List ℕ := decodeParents 35 27668672307802798025002208878468638974105546679821366262202706232017549591305299554003436830437925159237800842999083644550326668875065605

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check5 :
    (∀ j ∈ parents5, j < 2437) ∧
    row 2437 = base 2437 ^^^ xorList (parents5.map row) := by decide +kernel

private theorem certified5 : Step 2437 := ⟨parents5, check5⟩

private def parents6 : List ℕ := decodeParents 28 11175288868035130163681467871468575480555649187625688720791503000927442297223247280265575318073083064801077507

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check6 :
    (∀ j ∈ parents6, j < 2438) ∧
    row 2438 = base 2438 ^^^ xorList (parents6.map row) := by decide +kernel

private theorem certified6 : Step 2438 := ⟨parents6, check6⟩

private def parents7 : List ℕ := decodeParents 39 124710940728791247565286099719682710760764801503950625169586743591144789423934580732401536168479248160455061783681193713968851933583511764028352165890301

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check7 :
    (∀ j ∈ parents7, j < 2439) ∧
    row 2439 = base 2439 ^^^ xorList (parents7.map row) := by decide +kernel

private theorem certified7 : Step 2439 := ⟨parents7, check7⟩

private def parents8 : List ℕ := decodeParents 33 412126074429266210384709897827424581908430454179000388119357799667054574282951450047287167364542591784094628208476356582014757116

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check8 :
    (∀ j ∈ parents8, j < 2440) ∧
    row 2440 = base 2440 ^^^ xorList (parents8.map row) := by decide +kernel

private theorem certified8 : Step 2440 := ⟨parents8, check8⟩

private def parents9 : List ℕ := decodeParents 33 412295387399360757856416743105827371437354241055158459950556981214848823551325417913644412706449171578341102553504283911944456448

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check9 :
    (∀ j ∈ parents9, j < 2441) ∧
    row 2441 = base 2441 ^^^ xorList (parents9.map row) := by decide +kernel

private theorem certified9 : Step 2441 := ⟨parents9, check9⟩

private def parents10 : List ℕ := decodeParents 29 91547957231269308695824864913337218039779770885101792235276228917214946467273837222136188239911712967142561884428

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check10 :
    (∀ j ∈ parents10, j < 2442) ∧
    row 2442 = base 2442 ^^^ xorList (parents10.map row) := by decide +kernel

private theorem certified10 : Step 2442 := ⟨parents10, check10⟩

private def parents11 : List ℕ := decodeParents 38 15248480544103715369114690854428661384523271802502943502672526331768717542880503079272586423627292603750619809087993268809239468429983917304097343739

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check11 :
    (∀ j ∈ parents11, j < 2443) ∧
    row 2443 = base 2443 ^^^ xorList (parents11.map row) := by decide +kernel

private theorem certified11 : Step 2443 := ⟨parents11, check11⟩

private def parents12 : List ℕ := decodeParents 36 227126997118891231088895228645514642832859975140693148430598718881368990256944346116348002969874544064110422014420888176177728685417297398018

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check12 :
    (∀ j ∈ parents12, j < 2444) ∧
    row 2444 = base 2444 ^^^ xorList (parents12.map row) := by decide +kernel

private theorem certified12 : Step 2444 := ⟨parents12, check12⟩

private def parents13 : List ℕ := decodeParents 35 27759541013211478389698566377053216513715281093519230935595472276427971148644232020845974802845223791589564950115194174099800245389543681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check13 :
    (∀ j ∈ parents13, j < 2445) ∧
    row 2445 = base 2445 ^^^ xorList (parents13.map row) := by decide +kernel

private theorem certified13 : Step 2445 := ⟨parents13, check13⟩

private def parents14 : List ℕ := decodeParents 35 27770897868447868893895020281200310482475317918314047238194962581490471752411507128922684126067645065226426749393963057457526712520206584

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check14 :
    (∀ j ∈ parents14, j < 2446) ∧
    row 2446 = base 2446 ^^^ xorList (parents14.map row) := by decide +kernel

private theorem certified14 : Step 2446 := ⟨parents14, check14⟩

private def parents15 : List ℕ := decodeParents 30 753039560720733621092533490585792658718325771298364390486251820672064204105322375800276434504538408215501157769472254

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check15 :
    (∀ j ∈ parents15, j < 2447) ∧
    row 2447 = base 2447 ^^^ xorList (parents15.map row) := by decide +kernel

private theorem certified15 : Step 2447 := ⟨parents15, check15⟩

private def parents16 : List ℕ := decodeParents 40 1024565342505740397000002499396405896401415881929003389965112696922391438840246925785307800042132783694790945206834458969639076534451455305301560496189131002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check16 :
    (∀ j ∈ parents16, j < 2448) ∧
    row 2448 = base 2448 ^^^ xorList (parents16.map row) := by decide +kernel

private theorem certified16 : Step 2448 := ⟨parents16, check16⟩

private def parents17 : List ℕ := decodeParents 36 227406137263745288534607536650911892377352633557673979348235004155688217389488268620698292993099725576638859947806507535658934520577526384889

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check17 :
    (∀ j ∈ parents17, j < 2449) ∧
    row 2449 = base 2449 ^^^ xorList (parents17.map row) := by decide +kernel

private theorem certified17 : Step 2449 := ⟨parents17, check17⟩

private def parents18 : List ℕ := decodeParents 46 310035773606036556727812174131885584984991668740827931716211881809496793423591374192524253224575544851488613446344777620236782683508568295630413107748477492916730369761063832430838

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check18 :
    (∀ j ∈ parents18, j < 2450) ∧
    row 2450 = base 2450 ^^^ xorList (parents18.map row) := by decide +kernel

private theorem certified18 : Step 2450 := ⟨parents18, check18⟩

private def parents19 : List ℕ := decodeParents 40 1026660568253412207133224711992569102603219463760861500939121558220761293822406336517725779204207651296972589009655450058410666529985640102803921298933721335

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check19 :
    (∀ j ∈ parents19, j < 2451) ∧
    row 2451 = base 2451 ^^^ xorList (parents19.map row) := by decide +kernel

private theorem certified19 : Step 2451 := ⟨parents19, check19⟩

private def parents20 : List ℕ := decodeParents 45 37877089506510197026422180030417773025258900284890121711382182489608679510018985550368152635667641534447787203438831494204819103237258100120260602797706876694603801280289220853

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check20 :
    (∀ j ∈ parents20, j < 2452) ∧
    row 2452 = base 2452 ^^^ xorList (parents20.map row) := by decide +kernel

private theorem certified20 : Step 2452 := ⟨parents20, check20⟩

private def parents21 : List ℕ := decodeParents 42 68954264304330571368589124038170966892205684776304517809895121865718317934571981924202393746064137116483684984669771559273980503273364313309614624070601502089595123

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check21 :
    (∀ j ∈ parents21, j < 2453) ∧
    row 2453 = base 2453 ^^^ xorList (parents21.map row) := by decide +kernel

private theorem certified21 : Step 2453 := ⟨parents21, check21⟩

private def parents22 : List ℕ := decodeParents 42 68926132361424181516545810384970275447739990279889493217249342002404470598267741645839457842628215447970063698285808854474788350966901960647226570886957805309831412

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check22 :
    (∀ j ∈ parents22, j < 2454) ∧
    row 2454 = base 2454 ^^^ xorList (parents22.map row) := by decide +kernel

private theorem certified22 : Step 2454 := ⟨parents22, check22⟩

private def parents23 : List ℕ := decodeParents 41 8420701828757601065049663517167301116720540089875823228293349547080964970090595910864968272720456669885787397561584721621447454053370292029094559113230183622897

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check23 :
    (∀ j ∈ parents23, j < 2455) ∧
    row 2455 = base 2455 ^^^ xorList (parents23.map row) := by decide +kernel

private theorem certified23 : Step 2455 := ⟨parents23, check23⟩

private def parents24 : List ℕ := decodeParents 40 1028755794001083255027701259758201028355393669927622225464283655305364616236973954854918894715679160179430056517018126027952669789053641672531281994521864434

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check24 :
    (∀ j ∈ parents24, j < 2456) ∧
    row 2456 = base 2456 ^^^ xorList (parents24.map row) := by decide +kernel

private theorem certified24 : Step 2456 := ⟨parents24, check24⟩

private def parents25 : List ℕ := decodeParents 45 37954389692798094278866373242652469989580546125973133727241166368607361852905693546686469996526462436526994455676683605288992570734198019306472921781230447657097266604439816431

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check25 :
    (∀ j ∈ parents25, j < 2457) ∧
    row 2457 = base 2457 ^^^ xorList (parents25.map row) := by decide +kernel

private theorem certified25 : Step 2457 := ⟨parents25, check25⟩

private def parents26 : List ℕ := decodeParents 43 566025223845776538313556685348341330078297674228598729862066476233020030444199025852198899673201900848833969556900657284202790364015555622115022064088914117330186324203

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check26 :
    (∀ j ∈ parents26, j < 2458) ∧
    row 2458 = base 2458 ^^^ xorList (parents26.map row) := by decide +kernel

private theorem certified26 : Step 2458 := ⟨parents26, check26⟩

private def parents27 : List ℕ := decodeParents 42 69122994168533243676198909373642881257900490258900114029666751609047636592121917847423920274217214797518815989558345965767133388612240176364438581158525777933289712

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check27 :
    (∀ j ∈ parents27, j < 2459) ∧
    row 2459 = base 2459 ^^^ xorList (parents27.map row) := by decide +kernel

private theorem certified27 : Step 2459 := ⟨parents27, check27⟩

private def parents28 : List ℕ := decodeParents 42 69151112380168132657649489692754002483309176474671766020736697262769058372436557338405992821726161211917054055447302629334504121736277305354723488938492453557160143

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check28 :
    (∀ j ∈ parents28, j < 2460) ∧
    row 2460 = base 2460 ^^^ xorList (parents28.map row) := by decide +kernel

private theorem certified28 : Step 2460 := ⟨parents28, check28⟩

private def parents29 : List ℕ := decodeParents 41 8444730296799808057869078812343639238842431796698789089178012472531429477576353181297470402542910795456199097051561556578336350604913348130421663533408469985516

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check29 :
    (∀ j ∈ parents29, j < 2461) ∧
    row 2461 = base 2461 ^^^ xorList (parents29.map row) := by decide +kernel

private theorem certified29 : Step 2461 := ⟨parents29, check29⟩

private def parents30 : List ℕ := decodeParents 43 566946713863743010575816961496382190032102453711621692514531041513182878288556987241013841416919586492763016824985584938459858158663854489188354096049518318557445286090

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check30 :
    (∀ j ∈ parents30, j < 2462) ∧
    row 2462 = base 2462 ^^^ xorList (parents30.map row) := by decide +kernel

private theorem certified30 : Step 2462 := ⟨parents30, check30⟩

private def parents31 : List ℕ := decodeParents 48 20899643377622291542456333684775136787224923547894852619301632388403365496556549252325202010549288428166525187805802223412038549268925691505569435939395305456075989575577255374283795400908

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check31 :
    (∀ j ∈ parents31, j < 2463) ∧
    row 2463 = base 2463 ^^^ xorList (parents31.map row) := by decide +kernel

private theorem certified31 : Step 2463 := ⟨parents31, check31⟩

private def parents32 : List ℕ := decodeParents 43 566716256997752737578670936931004091789497727005439177453751960496885085580405639222511642597078114523679908071289286297834178254610180848867298414509480133037323233396

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check32 :
    (∀ j ∈ parents32, j < 2464) ∧
    row 2464 = base 2464 ^^^ xorList (parents32.map row) := by decide +kernel

private theorem certified32 : Step 2464 := ⟨parents32, check32⟩

private def parents33 : List ℕ := decodeParents 48 20916639793265794925947382627107821462578411770868340717182344917049966846833565403913431798484719490292011267791193207066877406118293612835985752050782765809415604164200986609502567049450

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check33 :
    (∀ j ∈ parents33, j < 2465) ∧
    row 2465 = base 2465 ^^^ xorList (parents33.map row) := by decide +kernel

private theorem certified33 : Step 2465 := ⟨parents33, check33⟩

private def parents34 : List ℕ := decodeParents 44 4651975635306427191757780704246732677067339324968998384353338874434009859853809728497864162521797759516434628966357843021023247801728071083175411306819872518067378490747086

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check34 :
    (∀ j ∈ parents34, j < 2466) ∧
    row 2466 = base 2466 ^^^ xorList (parents34.map row) := by decide +kernel

private theorem certified34 : Step 2466 := ⟨parents34, check34⟩

private def parents35 : List ℕ := decodeParents 43 567637831397816238413294257214186370797095395519646976033791182804287475081386947548496580978486794815061359581087484794264264444837350957918513648513425332339372239051

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check35 :
    (∀ j ∈ parents35, j < 2467) ∧
    row 2467 = base 2467 ^^^ xorList (parents35.map row) := by decide +kernel

private theorem certified35 : Step 2467 := ⟨parents35, check35⟩

private def parents36 : List ℕ := decodeParents 51 11522408022073363573086960040473517023795466049253857735949009046376340250408839361895967693672688859424855187927959134465711019782857694324280031758120947603657178811861014711024180074484012002363577

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check36 :
    (∀ j ∈ parents36, j < 2468) ∧
    row 2468 = base 2468 ^^^ xorList (parents36.map row) := by decide +kernel

private theorem certified36 : Step 2468 := ⟨parents36, check36⟩

private def parents37 : List ℕ := decodeParents 51 11527080531710137541282622978749694421266931708067412779668935305875337797496698160856921352161630265714740466087994782836666925655916914603078845915141239353785092202979670898659155630046095589550194

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check37 :
    (∀ j ∈ parents37, j < 2469) ∧
    row 2469 = base 2469 ^^^ xorList (parents37.map row) := by decide +kernel

private theorem certified37 : Step 2469 := ⟨parents37, check37⟩

private def parents38 : List ℕ := decodeParents 51 11531751900388636511975268975372415995604557851541880625708166379974856413468344857678346202399765987302653246667228020045887253218897659139564714373305134932045155992536192016822267535335163263764593

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check38 :
    (∀ j ∈ parents38, j < 2470) ∧
    row 2470 = base 2470 ^^^ xorList (parents38.map row) := by decide +kernel

private theorem certified38 : Step 2470 := ⟨parents38, check38⟩

private def parents39 : List ℕ := decodeParents 56 425791343456883956059904567627455454243998325349797937413723434353087119145859079605260638341709354284889348185867670402752801247554698456066132200260336327447714232996945544532661668996325425716928748497755692643952757

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check39 :
    (∀ j ∈ parents39, j < 2471) ∧
    row 2471 = base 2471 ^^^ xorList (parents39.map row) := by decide +kernel

private theorem certified39 : Step 2471 := ⟨parents39, check39⟩

private def parents40 : List ℕ := decodeParents 48 20976136586264453166665462209794220382499363373475703819268886101964801825121012136468897061646981653856916691751334990696468827329698418498066583916235487003980725632510018412053424310384

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check40 :
    (∀ j ∈ parents40, j < 2472) ∧
    row 2472 = base 2472 ^^^ xorList (parents40.map row) := by decide +kernel

private theorem certified40 : Step 2472 := ⟨parents40, check40⟩

private def parents41 : List ℕ := decodeParents 49 172045379869115113894738526267743965839994817900890233723120484336011697803318886002849632272852566034764475920296197548266168452606832712426057792349502618660692602170641114502791337469364251

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check41 :
    (∀ j ∈ parents41, j < 2473) ∧
    row 2473 = base 2473 ^^^ xorList (parents41.map row) := by decide +kernel

private theorem certified41 : Step 2473 := ⟨parents41, check41⟩

private def parents42 : List ℕ := decodeParents 54 6352491975262753112761650145932736114104424783425791475919143134672836196168255048298857982082990928042286854465568547350824248221657443047965269297361488746234741339870066577104841138986008501103338838016174175

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check42 :
    (∀ j ∈ parents42, j < 2474) ∧
    row 2474 = base 2474 ^^^ xorList (parents42.map row) := by decide +kernel

private theorem certified42 : Step 2474 := ⟨parents42, check42⟩

private def parents43 : List ℕ := decodeParents 61 15734368221103999592370591040643469755204530833206503459441180168512571997460947070537770864002166731746158698997926956332854109280324813039080013038287277947400462903641240353546884376166447105283259614580387519156112302574946952814323738

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check43 :
    (∀ j ∈ parents43, j < 2475) ∧
    row 2475 = base 2475 ^^^ xorList (parents43.map row) := by decide +kernel

private theorem certified43 : Step 2475 := ⟨parents43, check43⟩

private def parents44 : List ℕ := decodeParents 57 3493731230629655149619172355119932970030573956497409256148375978140809000127377408378991210710945626093547418932143586918175971898582471508424718037950910490349076393097941621652899490329342565031768356413750428746801268759

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check44 :
    (∀ j ∈ parents44, j < 2476) ∧
    row 2476 = base 2476 ^^^ xorList (parents44.map row) := by decide +kernel

private theorem certified44 : Step 2476 := ⟨parents44, check44⟩

private def parents45 : List ℕ := decodeParents 55 52102743598388953938148266146589782299959204622897296341587454715199754123554294384278516268399401457604919803683191023680844721824619700267272228934530974752721507836559509258397737779677672772859104393527409821720

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check45 :
    (∀ j ∈ parents45, j < 2477) ∧
    row 2477 = base 2477 ^^^ xorList (parents45.map row) := by decide +kernel

private theorem certified45 : Step 2477 := ⟨parents45, check45⟩

private def parents46 : List ℕ := decodeParents 58 28632217639375867791114474717978470708169817232322216381309621411975422933078054428098544224679145996145684807036566194973170641162474421975307002115105944965463653461479998607425624878004968734196521583683224217727933430155269

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check46 :
    (∀ j ∈ parents46, j < 2478) ∧
    row 2478 = base 2478 ^^^ xorList (parents46.map row) := by decide +kernel

private theorem certified46 : Step 2478 := ⟨parents46, check46⟩

private def parents47 : List ℕ := decodeParents 60 1923804661026980324456152382771104003786223237730012012614363110481595794614691111902151738271874837303776646337274085630100135926361493027675940109437243277234117649628351970813005294667471568945493053201627136610073552815986213169347

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check47 :
    (∀ j ∈ parents47, j < 2479) ∧
    row 2479 = base 2479 ^^^ xorList (parents47.map row) := by decide +kernel

private theorem certified47 : Step 2479 := ⟨parents47, check47⟩

private def parents48 : List ℕ := decodeParents 53 776077775910356546427579481723623734250894885652342086980915649533783554179869024707474578005344311560324988742640675358124637432315158363832309160002886749969747693703756497854859790946314141849989293844718

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check48 :
    (∀ j ∈ parents48, j < 2480) ∧
    row 2480 = base 2480 ^^^ xorList (parents48.map row) := by decide +kernel

private theorem certified48 : Step 2480 := ⟨parents48, check48⟩

private def parents49 : List ℕ := decodeParents 60 1925357273877471026806836505524419889077207058064391844609378211259695114225368892776315494833365193736075963086015430214507124141988681041381037453028442336105409933469128618841437226482261554719279377370933422523800764696665260607689

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check49 :
    (∀ j ∈ parents49, j < 2481) ∧
    row 2481 = base 2481 ^^^ xorList (parents49.map row) := by decide +kernel

private theorem certified49 : Step 2481 := ⟨parents49, check49⟩

private def parents50 : List ℕ := decodeParents 54 6370472836795853012686410831400029883608109937140516573810414670610016514469468991869369484061632107057549525231319721095575600497958134979533471033390847762974233641102854823785819297898636342153271722304391405

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check50 :
    (∀ j ∈ parents50, j < 2482) ∧
    row 2482 = base 2482 ^^^ xorList (parents50.map row) := by decide +kernel

private theorem certified50 : Step 2482 := ⟨parents50, check50⟩

private def parents51 : List ℕ := decodeParents 51 11597168175008456818449231226876646037843145169385090775967465358598242470263208833729140596789908104839933532345815959811760550149536318577609350582771738341947954723970489882873466982685055103060165

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check51 :
    (∀ j ∈ parents51, j < 2483) ∧
    row 2483 = base 2483 ^^^ xorList (parents51.map row) := by decide +kernel

private theorem certified51 : Step 2483 := ⟨parents51, check51⟩

private def parents52 : List ℕ := decodeParents 71 21494421950235109805486113026804875561738723602648178752729119394282445620886196903320589194631446540988294481073006402112871918164567436087893573000404492686618479626779744939993421859566645798863141594810751179466909633850630134861935201623876884287343691229410073447127099585

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check52 :
    (∀ j ∈ parents52, j < 2484) ∧
    row 2484 = base 2484 ^^^ xorList (parents52.map row) := by decide +kernel

private theorem certified52 : Step 2484 := ⟨parents52, check52⟩

private def parents53 : List ℕ := decodeParents 59 235408043109454674038507562887680878802714196733461416289800587144032350290034279704196740977304103104074850420132144801924109062424889277483065915177588767590109057852613180809917563786179779433180483112372899412813929033402738882

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check53 :
    (∀ j ∈ parents53, j < 2485) ∧
    row 2485 = base 2485 ^^^ xorList (parents53.map row) := by decide +kernel

private theorem certified53 : Step 2485 := ⟨parents53, check53⟩

private def parents54 : List ℕ := decodeParents 64 8678031074753765672097433649931659996910562617542372671216148871916371586655464664145640745616034622787758458111271045477668626596109226687027712303684220595377001771137558277575645020188540558854790613465809483029363027196806509244566626723051382971

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check54 :
    (∀ j ∈ parents54, j < 2486) ∧
    row 2486 = base 2486 ^^^ xorList (parents54.map row) := by decide +kernel

private theorem certified54 : Step 2486 := ⟨parents54, check54⟩

private def parents55 : List ℕ := decodeParents 60 1928462689152648453185360366415841412576407265080518089053368875928236943776839617633766764922673924857772047194312369385538185791529282882469826274095162504738005608719934578587460352332521143298358066679486904255114034471369219549414

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check55 :
    (∀ j ∈ parents55, j < 2487) ∧
    row 2487 = base 2487 ^^^ xorList (parents55.map row) := by decide +kernel

private theorem certified55 : Step 2487 := ⟨parents55, check55⟩

private def parents56 : List ℕ := decodeParents 66 582607445719732399382830079402326959857153963474983567907193944911064355989299747406389062201881693648612444063428706810563984374227334057391856124960990785505355445009695550146904800683251566998081716596488075671652979463606664003452676836311781904952633528

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check56 :
    (∀ j ∈ parents56, j < 2488) ∧
    row 2488 = base 2488 ^^^ xorList (parents56.map row) := by decide +kernel

private theorem certified56 : Step 2488 := ⟨parents56, check56⟩

private def parents57 : List ℕ := decodeParents 61 15817046797082446048626737473497704233330210390836204610008988121323178392798280961467414719579850497588265036818212607068302603169631074937171799663129291660158212024220250916917756731168048616506785200605431826725419690781315227634411749

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check57 :
    (∀ j ∈ parents57, j < 2489) ∧
    row 2489 = base 2489 ^^^ xorList (parents57.map row) := by decide +kernel

private theorem certified57 : Step 2489 := ⟨parents57, check57⟩

private def parents58 : List ℕ := decodeParents 70 2630171112761868356917808845751786338208090335012546149017304129361831370079332633666199900721323734408428442499362167650587750460403530020057241107560623066965548480522491475269729879708842072584083950875854399050268636800909822055903888507630575002595654402504110782326967

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check58 :
    (∀ j ∈ parents58, j < 2490) ∧
    row 2490 = base 2490 ^^^ xorList (parents58.map row) := by decide +kernel

private theorem certified58 : Step 2490 := ⟨parents58, check58⟩

private def parents59 : List ℕ := decodeParents 72 176507795504121605990734806224258457853127135813315056165556117872738347226051854286109346129769901043910647542885791031227759307847870666195078075775206064123017264453492317202695870459797686253302152660548263638368817442221459079560728406918109837180049811918583069870983769270449

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check59 :
    (∀ j ∈ parents59, j < 2491) ∧
    row 2491 = base 2491 ^^^ xorList (parents59.map row) := by decide +kernel

private theorem certified59 : Step 2491 := ⟨parents59, check59⟩

private def parents60 : List ℕ := decodeParents 58 28817311988684851916084621017284263114509239443512744468375629628270476926312757418043117854995096907955775367406265733148720598356973628734289157084079823693045970465435899226018132823013696488962171861811580548987854957095085

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check60 :
    (∀ j ∈ parents60, j < 2492) ∧
    row 2492 = base 2492 ^^^ xorList (parents60.map row) := by decide +kernel

private theorem certified60 : Step 2492 := ⟨parents60, check60⟩

private def parents61 : List ℕ := decodeParents 58 28759471946100049889489855090060015513296447104218432185267435645871811551084259561339684262713981949583235568293157669480876816642379163023510491341442791119528779445277282926518960998323880262529076140678062160289845048027310

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check61 :
    (∀ j ∈ parents61, j < 2493) ∧
    row 2493 = base 2493 ^^^ xorList (parents61.map row) := by decide +kernel

private theorem certified61 : Step 2493 := ⟨parents61, check61⟩

private def parents62 : List ℕ := decodeParents 57 3520562638576776679868583938909166023689621501286832451396533851298837774426628937717125783175088334988446278901251478366436703989786872619468194019189376447477477343352087439762129060658604684634095208543760988146644928623

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check62 :
    (∀ j ∈ parents62, j < 2494) ∧
    row 2494 = base 2494 ^^^ xorList (parents62.map row) := by decide +kernel

private theorem certified62 : Step 2494 := ⟨parents62, check62⟩

private def parents63 : List ℕ := decodeParents 57 3521975162732702903810341673252605830631068855050510089117372353034002328185333088945165401198629015575871271179031454509622837658751341080777712716247469286565399872861116714673268426497950086683002351573515066236912314473

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check63 :
    (∀ j ∈ parents63, j < 2495) ∧
    row 2495 = base 2495 ^^^ xorList (parents63.map row) := by decide +kernel

private theorem certified63 : Step 2495 := ⟨parents63, check63⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem steps (k : Fin 64) : ∃ ps : List ℕ,
    (∀ j ∈ ps, j < 2432 + k.val) ∧
    row (2432 + k.val) = base (2432 + k.val) ^^^ xorList (ps.map row) := by
  change Step (2432 + k.val)
  fin_cases k
  · exact certified0
  · exact certified1
  · exact certified2
  · exact certified3
  · exact certified4
  · exact certified5
  · exact certified6
  · exact certified7
  · exact certified8
  · exact certified9
  · exact certified10
  · exact certified11
  · exact certified12
  · exact certified13
  · exact certified14
  · exact certified15
  · exact certified16
  · exact certified17
  · exact certified18
  · exact certified19
  · exact certified20
  · exact certified21
  · exact certified22
  · exact certified23
  · exact certified24
  · exact certified25
  · exact certified26
  · exact certified27
  · exact certified28
  · exact certified29
  · exact certified30
  · exact certified31
  · exact certified32
  · exact certified33
  · exact certified34
  · exact certified35
  · exact certified36
  · exact certified37
  · exact certified38
  · exact certified39
  · exact certified40
  · exact certified41
  · exact certified42
  · exact certified43
  · exact certified44
  · exact certified45
  · exact certified46
  · exact certified47
  · exact certified48
  · exact certified49
  · exact certified50
  · exact certified51
  · exact certified52
  · exact certified53
  · exact certified54
  · exact certified55
  · exact certified56
  · exact certified57
  · exact certified58
  · exact certified59
  · exact certified60
  · exact certified61
  · exact certified62
  · exact certified63

end Trace2432

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
