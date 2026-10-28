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
namespace Trace0064
open LinearMembership GeneratorCertificates Binary

private def Step (i : ℕ) : Prop := ∃ ps : List ℕ,
  (∀ j ∈ ps, j < i) ∧ row i = base i ^^^ xorList (ps.map row)

private def parents0 : List ℕ := decodeParents 24 61117918334552913629727484107863658513327533710873905481080297630973700554596900290928050177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check0 :
    (∀ j ∈ parents0, j < 64) ∧
    row 64 = base 64 ^^^ xorList (parents0.map row) := by decide +kernel

private theorem certified0 : Step 64 := ⟨parents0, check0⟩

private def parents1 : List ℕ := decodeParents 25 517366404357169266926705158856329201797058488946745901544007750158745570582196853373256620621824

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check1 :
    (∀ j ∈ parents1, j < 65) ∧
    row 65 = base 65 ^^^ xorList (parents1.map row) := by decide +kernel

private theorem certified1 : Step 65 := ⟨parents1, check1⟩

private def parents2 : List ℕ := decodeParents 28 284427988249916590350289507429634326809138557455496901875696477822212355265713880187477474732714840769486849

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check2 :
    (∀ j ∈ parents2, j < 66) ∧
    row 66 = base 66 ^^^ xorList (parents2.map row) := by decide +kernel

private theorem certified2 : Step 66 := ⟨parents2, check2⟩

private def parents3 : List ℕ := decodeParents 25 534062970856126630902477226346637907065577011387801483435461576410451315193871991419637778661376

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check3 :
    (∀ j ∈ parents3, j < 67) ∧
    row 67 = base 67 ^^^ xorList (parents3.map row) := by decide +kernel

private theorem certified3 : Step 67 := ⟨parents3, check3⟩

private def parents4 : List ℕ := decodeParents 30 19703483434418642628286007765902168150831732448014246401922038393544094820715640623308742239354233014727211495768065

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check4 :
    (∀ j ∈ parents4, j < 68) ∧
    row 68 = base 68 ^^^ xorList (parents4.map row) := by decide +kernel

private theorem certified4 : Step 68 := ⟨parents4, check4⟩

private def parents5 : List ℕ := decodeParents 30 20626892824220095914558502526772647184400088489956678888291811677566494780539732067195438724750375571077640275156993

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check5 :
    (∀ j ∈ parents5, j < 69) ∧
    row 69 = base 69 ^^^ xorList (parents5.map row) := by decide +kernel

private theorem certified5 : Step 69 := ⟨parents5, check5⟩

private def parents6 : List ℕ := decodeParents 30 20626892828805413269630431121439094687772491719049350663309173000583089749432540709984751191258486515413350480928769

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check6 :
    (∀ j ∈ parents6, j < 70) ∧
    row 70 = base 70 ^^^ xorList (parents6.map row) := by decide +kernel

private theorem certified6 : Step 70 := ⟨parents6, check6⟩

private def parents7 : List ℕ := decodeParents 26 4648466883213818443750154842801024942703325445764850598117171493924337345964880046280486367480832001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check7 :
    (∀ j ∈ parents7, j < 71) ∧
    row 71 = base 71 ^^^ xorList (parents7.map row) := by decide +kernel

private theorem certified7 : Step 71 := ⟨parents7, check7⟩

private def parents8 : List ℕ := decodeParents 29 2555521695272563589220656674129684019678983375811922473406149822799765196859129144586859681652232184764909486087

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check8 :
    (∀ j ∈ parents8, j < 72) ∧
    row 72 = base 72 ^^^ xorList (parents8.map row) := by decide +kernel

private theorem certified8 : Step 72 := ⟨parents8, check8⟩

private def parents9 : List ℕ := decodeParents 21 120437796161726159153588029910671355223978575340156745586031813476372032465739782

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check9 :
    (∀ j ∈ parents9, j < 73) ∧
    row 73 = base 73 ^^^ xorList (parents9.map row) := by decide +kernel

private theorem certified9 : Step 73 := ⟨parents9, check9⟩

private def parents10 : List ℕ := decodeParents 26 4238307300953689882373686997870234902487556483209267905550086549229496960645236316095166689801445379

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check10 :
    (∀ j ∈ parents10, j < 74) ∧
    row 74 = base 74 ^^^ xorList (parents10.map row) := by decide +kernel

private theorem certified10 : Step 74 := ⟨parents10, check10⟩

private def parents11 : List ℕ := decodeParents 28 311952211865017415850934572726484591994665503015753770734590385986492307105655659555539576521806858212655105

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check11 :
    (∀ j ∈ parents11, j < 75) ∧
    row 75 = base 75 ^^^ xorList (parents11.map row) := by decide +kernel

private theorem certified11 : Step 75 := ⟨parents11, check11⟩

private def parents12 : List ℕ := decodeParents 29 2405205794860223436783826787997988689958800100115695008308540287585436019016171275466554794454116089474981093377

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check12 :
    (∀ j ∈ parents12, j < 76) ∧
    row 76 = base 76 ^^^ xorList (parents12.map row) := by decide +kernel

private theorem certified12 : Step 76 := ⟨parents12, check12⟩

private def parents13 : List ℕ := decodeParents 34 94282109354355222358068231676266639309700287125471423043464300469818912443109345696162552987828095416676573664937277538050487926791

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check13 :
    (∀ j ∈ parents13, j < 77) ∧
    row 77 = base 77 ^^^ xorList (parents13.map row) := by decide +kernel

private theorem certified13 : Step 77 := ⟨parents13, check13⟩

private def parents14 : List ℕ := decodeParents 24 69267305654234556651253427909408813757634941553412755863503203133270455344190972857369550849

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check14 :
    (∀ j ∈ parents14, j < 78) ∧
    row 78 = base 78 ^^^ xorList (parents14.map row) := by decide +kernel

private theorem certified14 : Step 78 := ⟨parents14, check14⟩

private def parents15 : List ℕ := decodeParents 28 307364094760666184944249910484535415142282922675512532799887279533142763010039799781363962416209141516255233

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check15 :
    (∀ j ∈ parents15, j < 79) ∧
    row 79 = base 79 ^^^ xorList (parents15.map row) := by decide +kernel

private theorem certified15 : Step 79 := ⟨parents15, check15⟩

private def parents16 : List ℕ := decodeParents 30 20934758560548640391378154129648333425106435775250144724302012506119019356584749003027039796615039453221429155201025

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check16 :
    (∀ j ∈ parents16, j < 80) ∧
    row 80 = base 80 ^^^ xorList (parents16.map row) := by decide +kernel

private theorem certified16 : Step 80 := ⟨parents16, check16⟩

private def parents17 : List ℕ := decodeParents 31 171498157859523821313097570744529505348806674684049367152615117062850846924263360348960964654835740554286092077024411655

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check17 :
    (∀ j ∈ parents17, j < 81) ∧
    row 81 = base 81 ^^^ xorList (parents17.map row) := by decide +kernel

private theorem certified17 : Step 81 := ⟨parents17, check17⟩

private def parents18 : List ℕ := decodeParents 33 13709268061734027194851643925205116059600351904812522548493550817224758678052318009897091220029900551611669627099813376245686273

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check18 :
    (∀ j ∈ parents18, j < 82) ∧
    row 82 = base 82 ^^^ xorList (parents18.map row) := by decide +kernel

private theorem certified18 : Step 82 := ⟨parents18, check18⟩

private def parents19 : List ℕ := decodeParents 30 25244954242705820007337978485899424190079389585843386993492207078992072481394388812212370024746376795561826592038914

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check19 :
    (∀ j ∈ parents19, j < 83) ∧
    row 83 = base 83 ^^^ xorList (parents19.map row) := by decide +kernel

private theorem certified19 : Step 83 := ⟨parents19, check19⟩

private def parents20 : List ℕ := decodeParents 28 307364654901923177334769420149367927451535469317335074323874799246674778356237952371835941344615498740973569

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check20 :
    (∀ j ∈ parents20, j < 84) ∧
    row 84 = base 84 ^^^ xorList (parents20.map row) := by decide +kernel

private theorem certified20 : Step 84 := ⟨parents20, check20⟩

private def parents21 : List ℕ := decodeParents 26 5742184030372967784802118405567082332645462866491567076299527779491743002212296554998387814587957255

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check21 :
    (∀ j ∈ parents21, j < 85) ∧
    row 85 = base 85 ^^^ xorList (parents21.map row) := by decide +kernel

private theorem certified21 : Step 85 := ⟨parents21, check21⟩

private def parents22 : List ℕ := decodeParents 33 14386313321769697797522454152095889093588605807086892381660454162298783385723288867262661272656637726448933611984452126379130880

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check22 :
    (∀ j ∈ parents22, j < 86) ∧
    row 86 = base 86 ^^^ xorList (parents22.map row) := by decide +kernel

private theorem certified22 : Step 86 := ⟨parents22, check22⟩

private def parents23 : List ℕ := decodeParents 25 700938994824883877145937788838216873145244660571316999550985226601637762239510709518336310435841

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check23 :
    (∀ j ∈ parents23, j < 87) ∧
    row 87 = base 87 ^^^ xorList (parents23.map row) := by decide +kernel

private theorem certified23 : Step 87 := ⟨parents23, check23⟩

private def parents24 : List ℕ := decodeParents 25 692610575846860524569323027726795306012661079748463337910705584486818839328517789997647876145155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check24 :
    (∀ j ∈ parents24, j < 88) ∧
    row 88 = base 88 ^^^ xorList (parents24.map row) := by decide +kernel

private theorem certified24 : Step 88 := ⟨parents24, check24⟩

private def parents25 : List ℕ := decodeParents 36 7908959404307468070484314779440937881310435592183565306340683985025946960357679352633172367771815219748994084256576841669765139112092819457

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check25 :
    (∀ j ∈ parents25, j < 89) ∧
    row 89 = base 89 ^^^ xorList (parents25.map row) := by decide +kernel

private theorem certified25 : Step 89 := ⟨parents25, check25⟩

private def parents26 : List ℕ := decodeParents 34 122012529837966531806221750118862789048941148765494594800056104510639827447362859146902978306798451267311269369483744550613394964480

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check26 :
    (∀ j ∈ parents26, j < 90) ∧
    row 90 = base 90 ^^^ xorList (parents26.map row) := by decide +kernel

private theorem certified26 : Step 90 := ⟨parents26, check26⟩

private def parents27 : List ℕ := decodeParents 36 8002006126190212682055771511143765631077432395941820429591360226919643718176310811582715533964525615575987381522058390939715503829528141825

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check27 :
    (∀ j ∈ parents27, j < 91) ∧
    row 91 = base 91 ^^^ xorList (parents27.map row) := by decide +kernel

private theorem certified27 : Step 91 := ⟨parents27, check27⟩

private def parents28 : List ℕ := decodeParents 43 20733469449336046620323536037724447403133149536165437620597412174651039914070962097602016368011942399122247939769008170947021277660275284012755852698725682171193909249

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check28 :
    (∀ j ∈ parents28, j < 92) ∧
    row 92 = base 92 ^^^ xorList (parents28.map row) := by decide +kernel

private theorem certified28 : Step 92 := ⟨parents28, check28⟩

private def parents29 : List ℕ := decodeParents 36 8188054132834643874379197966107592621110360806032520548384200909467382407974322890954594328030411102567828839785522508558434065707295571969

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check29 :
    (∀ j ∈ parents29, j < 93) ∧
    row 93 = base 93 ^^^ xorList (parents29.map row) := by decide +kernel

private theorem certified29 : Step 93 := ⟨parents29, check29⟩

private def parents30 : List ℕ := decodeParents 28 412876231802324956895520987560339992537712278211898706568299108560548220856870301239190170735086315889549313

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check30 :
    (∀ j ∈ parents30, j < 94) ∧
    row 94 = base 94 ^^^ xorList (parents30.map row) := by decide +kernel

private theorem certified30 : Step 94 := ⟨parents30, check30⟩

private def parents31 : List ℕ := decodeParents 33 15401736651226529473314861979102601956959419230687481751145949815699634792625403844347809627104062590909384848737144450223964167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check31 :
    (∀ j ∈ parents31, j < 95) ∧
    row 95 = base 95 ^^^ xorList (parents31.map row) := by decide +kernel

private theorem certified31 : Step 95 := ⟨parents31, check31⟩

private def parents32 : List ℕ := decodeParents 26 6220678522607928293477769862370083255954463602890479191696851915331698138198238663638932617227665409

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check32 :
    (∀ j ∈ parents32, j < 96) ∧
    row 96 = base 96 ^^^ xorList (parents32.map row) := by decide +kernel

private theorem certified32 : Step 96 := ⟨parents32, check32⟩

private def parents33 : List ℕ := decodeParents 32 1983399933091335962820628927789758935386089678381171689304765627922585372470774620125698775144203225980713533924333932576774

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check33 :
    (∀ j ∈ parents33, j < 97) ∧
    row 97 = base 97 ^^^ xorList (parents33.map row) := by decide +kernel

private theorem certified33 : Step 97 := ⟨parents33, check33⟩

private def parents34 : List ℕ := decodeParents 40 38552205006293881245695541948383753164677644295242757703790696501809424888764673860975324062835862199477387534751911556841778587444897060217815212402671623

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check34 :
    (∀ j ∈ parents34, j < 98) ∧
    row 98 = base 98 ^^^ xorList (parents34.map row) := by decide +kernel

private theorem certified34 : Step 98 := ⟨parents34, check34⟩

private def parents35 : List ℕ := decodeParents 37 71650715838260324475984543452895241521016523278908805559983162552525407124476173959855667606839325687978261607087128666726923486639257796272129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check35 :
    (∀ j ∈ parents35, j < 99) ∧
    row 99 = base 99 ^^^ xorList (parents35.map row) := by decide +kernel

private theorem certified35 : Step 99 := ⟨parents35, check35⟩

private def parents36 : List ℕ := decodeParents 37 73936780600620745863426905812624168551147014883819596138822851170999431560949899457283518507350520969202188891621757937068995867334929041850369

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check36 :
    (∀ j ∈ parents36, j < 100) ∧
    row 100 = base 100 ^^^ xorList (parents36.map row) := by decide +kernel

private theorem certified36 : Step 100 := ⟨parents36, check36⟩

private def parents37 : List ℕ := decodeParents 42 2643455134824462828428293550257590498326786408791307859379406954955730103047007502090893181361475279911614329780703883806387998329576529907477479932930785215004679

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check37 :
    (∀ j ∈ parents37, j < 101) ∧
    row 101 = base 101 ^^^ xorList (parents37.map row) := by decide +kernel

private theorem certified37 : Step 101 := ⟨parents37, check37⟩

private def parents38 : List ℕ := decodeParents 39 5064156763733568015011977236442135244067602501074358994802666442078439641192514115462843534282132582874529448292431570005703792056334220408790456516608

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check38 :
    (∀ j ∈ parents38, j < 102) ∧
    row 102 = base 102 ^^^ xorList (parents38.map row) := by decide +kernel

private theorem certified38 : Step 102 := ⟨parents38, check38⟩

private def parents39 : List ℕ := decodeParents 39 5064156761446758844864152892215193772711866357061218060072593033146822216532081431049341648563639568238191775928019474544372804072227596745922324783105

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check39 :
    (∀ j ∈ parents39, j < 103) ∧
    row 103 = base 103 ^^^ xorList (parents39.map row) := by decide +kernel

private theorem certified39 : Step 103 := ⟨parents39, check39⟩

private def parents40 : List ℕ := decodeParents 33 16586658855113953670165748752276040513841578524468191055571821883411899711389802757694965654553175464587488559453890652156256257

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check40 :
    (∀ j ∈ parents40, j < 104) ∧
    row 104 = base 104 ^^^ xorList (parents40.map row) := by decide +kernel

private theorem certified40 : Step 104 := ⟨parents40, check40⟩

private def parents41 : List ℕ := decodeParents 46 13171441593933760738956676070086330735493063048707223386691740517718863012993906703556247770352670085894400971624343492498920793126469664450687595427962905692236178924279584317441

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check41 :
    (∀ j ∈ parents41, j < 105) ∧
    row 105 = base 105 ^^^ xorList (parents41.map row) := by decide +kernel

private theorem certified41 : Step 105 := ⟨parents41, check41⟩

private def parents42 : List ℕ := decodeParents 45 1607838217714799383329920251712194838682184893228288274721187676194584110002577714443095712519374839119529397520418738333831079801950077020823080923042580650016678344772288519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check42 :
    (∀ j ∈ parents42, j < 106) ∧
    row 106 = base 106 ^^^ xorList (parents42.map row) := by decide +kernel

private theorem certified42 : Step 106 := ⟨parents42, check42⟩

private def parents43 : List ℕ := decodeParents 33 17432748523690126187596474867977935314809338702259386370501234763515958150732383142299928585673816624370183620269586534270812167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check43 :
    (∀ j ∈ parents43, j < 107) ∧
    row 107 = base 107 ^^^ xorList (parents43.map row) := by decide +kernel

private theorem certified43 : Step 107 := ⟨parents43, check43⟩

private def parents44 : List ℕ := decodeParents 40 44418734811312336342126641929570895569594048974100488943822670318331696509783072442649861213365878613633427384854439026877915291790333672734335601433640967

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check44 :
    (∀ j ∈ parents44, j < 108) ∧
    row 108 = base 108 ^^^ xorList (parents44.map row) := by decide +kernel

private theorem certified44 : Step 108 := ⟨parents44, check44⟩

private def parents45 : List ℕ := decodeParents 45 1638762066284757058144118967592600295732526588020957084793767605880048667540996929432697372465909772553007589972638415077389701859685662457925906288825628075682854919873806343

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check45 :
    (∀ j ∈ parents45, j < 109) ∧
    row 109 = base 109 ^^^ xorList (parents45.map row) := by decide +kernel

private theorem certified45 : Step 109 := ⟨parents45, check45⟩

private def parents46 : List ℕ := decodeParents 42 3065248900808126806448232286401885195429728427303878296834166806792199322098902489939481928909963478742096237496848093467931553740847897753024854972395720682815488

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check46 :
    (∀ j ∈ parents46, j < 110) ∧
    row 110 = base 110 ^^^ xorList (parents46.map row) := by decide +kernel

private theorem certified46 : Step 110 := ⟨parents46, check46⟩

private def parents47 : List ℕ := decodeParents 39 5524527272043677509687631439616264416580357933694002422277953074929904508736625214176370236301258236898867531007842034324538437045385262578739466821632

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check47 :
    (∀ j ∈ parents47, j < 111) ∧
    row 111 = base 111 ^^^ xorList (parents47.map row) := by decide +kernel

private theorem certified47 : Step 111 := ⟨parents47, check47⟩

private def parents48 : List ℕ := decodeParents 44 209479794836562751078110051526125304477945997573858908229856370465850460275985617514070476016285575124414492611408370662648729166665677608180812308149365558377450427179009

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check48 :
    (∀ j ∈ parents48, j < 112) ∧
    row 112 = base 112 ^^^ xorList (parents48.map row) := by decide +kernel

private theorem certified48 : Step 112 := ⟨parents48, check48⟩

private def parents49 : List ℕ := decodeParents 46 13931317891219388498995744934231291788473977740664435424014296867178928277357712301495480958296440937571754737750341081222499307941608532131424801138548775624008995934061776093190

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check49 :
    (∀ j ∈ parents49, j < 113) ∧
    row 113 = base 113 ^^^ xorList (parents49.map row) := by decide +kernel

private theorem certified49 : Step 113 := ⟨parents49, check49⟩

private def parents50 : List ℕ := decodeParents 45 1746980440428897359333448504507084244181392932172153526424468753810739295618013347227571774672094439022438501369210426588736158401324760526720338227486792218066735343106842625

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check50 :
    (∀ j ∈ parents50, j < 114) ∧
    row 114 = base 114 ^^^ xorList (parents50.map row) := by decide +kernel

private theorem certified50 : Step 114 := ⟨parents50, check50⟩

private def parents51 : List ℕ := decodeParents 45 1746980440198637334554215306232299615142530034553782089095606355850177838875617510185876220530936159501272014414560594323004953814025714695561608937464959127762221936481968129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check51 :
    (∀ j ∈ parents51, j < 115) ∧
    row 115 = base 115 ^^^ xorList (parents51.map row) := by decide +kernel

private theorem certified51 : Step 115 := ⟨parents51, check51⟩

private def parents52 : List ℕ := decodeParents 40 45256722806937559296014141264504669760384901035290786371563809080145084249675102648136170175807973513041420804390882612793121494874263717112619449605709824

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check52 :
    (∀ j ∈ parents52, j < 116) ∧
    row 116 = base 116 ^^^ xorList (parents52.map row) := by decide +kernel

private theorem certified52 : Step 116 := ⟨parents52, check52⟩

private def parents53 : List ℕ := decodeParents 51 523322211991461449883879359624845365579029837266229591122155610502439391464621220111286803558961656420489930821626823938138041436550756779396002142424977108283425684549073445716903350939165170614272

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check53 :
    (∀ j ∈ parents53, j < 117) ∧
    row 117 = base 117 ^^^ xorList (parents53.map row) := by decide +kernel

private theorem certified53 : Step 117 := ⟨parents53, check53⟩

private def parents54 : List ℕ := decodeParents 37 86894838322966450991277123618129132334755425985532553631969790062078968938152616982597939847472772950238853200317273637687391845335519333564418

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check54 :
    (∀ j ∈ parents54, j < 118) ∧
    row 118 = base 118 ^^^ xorList (parents54.map row) := by decide +kernel

private theorem certified54 : Step 118 := ⟨parents54, check54⟩

private def parents55 : List ℕ := decodeParents 50 65593299673877962951045212582002790593196151060278479867888748759979650222530813775705778199598931330478369896263175664241653754259180170748738762112751165112518577614854813126392198193894916097

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check55 :
    (∀ j ∈ parents55, j < 119) ∧
    row 119 = base 119 ^^^ xorList (parents55.map row) := by decide +kernel

private theorem certified55 : Step 119 := ⟨parents55, check55⟩

private def parents56 : List ℕ := decodeParents 52 4478422863036964242469311761678210412480150808322493578351266235895532363131524168073305377600242759229181259728653364660033056244170862856790781319376222738849887841907861709898567991001265771649220615

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check56 :
    (∀ j ∈ parents56, j < 120) ∧
    row 120 = base 120 ^^^ xorList (parents56.map row) := by decide +kernel

private theorem certified56 : Step 120 := ⟨parents56, check56⟩

private def parents57 : List ℕ := decodeParents 49 8146178239912710344797373152310145583686390792725238371530224641218885332980563749247547490854890668754341226295780460717583907532690384611103237236818262490026196290205010043780799429394433

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check57 :
    (∀ j ∈ parents57, j < 121) ∧
    row 121 = base 121 ^^^ xorList (parents57.map row) := by decide +kernel

private theorem certified57 : Step 121 := ⟨parents57, check57⟩

private def parents58 : List ℕ := decodeParents 52 4516681374224298654827631096554971406332035630604379305057632012451858181294622573227125382349868317768822277255155518778655061113364440150438019857066723163843398494513827547971810038293200884457275399

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check58 :
    (∀ j ∈ parents58, j < 122) ∧
    row 122 = base 122 ^^^ xorList (parents58.map row) := by decide +kernel

private theorem certified58 : Step 122 := ⟨parents58, check58⟩

private def parents59 : List ℕ := decodeParents 44 230237970351885487901505311476660072181519580439857633659895345126287800863345654681925612906960920949842196780278250853679869615481735379499568876912616048966946793734145

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check59 :
    (∀ j ∈ parents59, j < 123) ∧
    row 123 = base 123 ^^^ xorList (parents59.map row) := by decide +kernel

private theorem certified59 : Step 123 := ⟨parents59, check59⟩

private def parents60 : List ℕ := decodeParents 53 36687354911576404605771967916911698010003160747373054746200178780538083594954685819777599574357441194808094819051849906455570247915435242158691142327982450039469261572984830842435074741136502681600077643776

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check60 :
    (∀ j ∈ parents60, j < 124) ∧
    row 124 = base 124 ^^^ xorList (parents60.map row) := by decide +kernel

private theorem certified60 : Step 124 := ⟨parents60, check60⟩

private def parents61 : List ℕ := decodeParents 45 1808820590795291335458283442089581038517612781445164586512301076673753912255457346375384819204327821557091810304625916934469482936631869924535958383472669167754270704490561536

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check61 :
    (∀ j ∈ parents61, j < 125) ∧
    row 125 = base 125 ^^^ xorList (parents61.map row) := by decide +kernel

private theorem certified61 : Step 125 := ⟨parents61, check61⟩

private def parents62 : List ℕ := decodeParents 40 49447020862096434058644277358611294977188353964311068309911677636314242124210591026642983414523753600191748115161741930223315725424002165771180445626531847

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check62 :
    (∀ j ∈ parents62, j < 126) ∧
    row 126 = base 126 ^^^ xorList (parents62.map row) := by decide +kernel

private theorem certified62 : Step 126 := ⟨parents62, check62⟩

private def parents63 : List ℕ := decodeParents 56 21030907324921286102573995726091879454268321887535493550271626957459374647549071147711758888365495841556520679093377738389269450685847102899258857174411766861996086685124110692826269245640136738948946195696008757821440

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check63 :
    (∀ j ∈ parents63, j < 127) ∧
    row 127 = base 127 ^^^ xorList (parents63.map row) := by decide +kernel

private theorem certified63 : Step 127 := ⟨parents63, check63⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem steps (k : Fin 64) : ∃ ps : List ℕ,
    (∀ j ∈ ps, j < 64 + k.val) ∧
    row (64 + k.val) = base (64 + k.val) ^^^ xorList (ps.map row) := by
  change Step (64 + k.val)
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

end Trace0064

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
