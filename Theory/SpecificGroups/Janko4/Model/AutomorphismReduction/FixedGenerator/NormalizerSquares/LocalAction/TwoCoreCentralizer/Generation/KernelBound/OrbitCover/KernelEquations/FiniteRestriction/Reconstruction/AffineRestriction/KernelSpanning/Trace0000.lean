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
namespace Trace0000
open LinearMembership GeneratorCertificates Binary

private def Step (i : ℕ) : Prop := ∃ ps : List ℕ,
  (∀ j ∈ ps, j < i) ∧ row i = base i ^^^ xorList (ps.map row)

private def parents0 : List ℕ := decodeParents 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check0 :
    (∀ j ∈ parents0, j < 0) ∧
    row 0 = base 0 ^^^ xorList (parents0.map row) := by decide +kernel

private theorem certified0 : Step 0 := ⟨parents0, check0⟩

private def parents1 : List ℕ := decodeParents 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check1 :
    (∀ j ∈ parents1, j < 1) ∧
    row 1 = base 1 ^^^ xorList (parents1.map row) := by decide +kernel

private theorem certified1 : Step 1 := ⟨parents1, check1⟩

private def parents2 : List ℕ := decodeParents 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check2 :
    (∀ j ∈ parents2, j < 2) ∧
    row 2 = base 2 ^^^ xorList (parents2.map row) := by decide +kernel

private theorem certified2 : Step 2 := ⟨parents2, check2⟩

private def parents3 : List ℕ := decodeParents 1 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check3 :
    (∀ j ∈ parents3, j < 3) ∧
    row 3 = base 3 ^^^ xorList (parents3.map row) := by decide +kernel

private theorem certified3 : Step 3 := ⟨parents3, check3⟩

private def parents4 : List ℕ := decodeParents 3 134217729

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check4 :
    (∀ j ∈ parents4, j < 4) ∧
    row 4 = base 4 ^^^ xorList (parents4.map row) := by decide +kernel

private theorem certified4 : Step 4 := ⟨parents4, check4⟩

private def parents5 : List ℕ := decodeParents 2 24578

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check5 :
    (∀ j ∈ parents5, j < 5) ∧
    row 5 = base 5 ^^^ xorList (parents5.map row) := by decide +kernel

private theorem certified5 : Step 5 := ⟨parents5, check5⟩

private def parents6 : List ℕ := decodeParents 1 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check6 :
    (∀ j ∈ parents6, j < 6) ∧
    row 6 = base 6 ^^^ xorList (parents6.map row) := by decide +kernel

private theorem certified6 : Step 6 := ⟨parents6, check6⟩

private def parents7 : List ℕ := decodeParents 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check7 :
    (∀ j ∈ parents7, j < 7) ∧
    row 7 = base 7 ^^^ xorList (parents7.map row) := by decide +kernel

private theorem certified7 : Step 7 := ⟨parents7, check7⟩

private def parents8 : List ℕ := decodeParents 1 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check8 :
    (∀ j ∈ parents8, j < 8) ∧
    row 8 = base 8 ^^^ xorList (parents8.map row) := by decide +kernel

private theorem certified8 : Step 8 := ⟨parents8, check8⟩

private def parents9 : List ℕ := decodeParents 3 268484609

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check9 :
    (∀ j ∈ parents9, j < 9) ∧
    row 9 = base 9 ^^^ xorList (parents9.map row) := by decide +kernel

private theorem certified9 : Step 9 := ⟨parents9, check9⟩

private def parents10 : List ℕ := decodeParents 5 40534596206485504

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check10 :
    (∀ j ∈ parents10, j < 10) ∧
    row 10 = base 10 ^^^ xorList (parents10.map row) := by decide +kernel

private theorem certified10 : Step 10 := ⟨parents10, check10⟩

private def parents11 : List ℕ := decodeParents 7 3022646626461445909381121

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check11 :
    (∀ j ∈ parents11, j < 11) ∧
    row 11 = base 11 ^^^ xorList (parents11.map row) := by decide +kernel

private theorem certified11 : Step 11 := ⟨parents11, check11⟩

private def parents12 : List ℕ := decodeParents 7 3324914974853250420850694

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check12 :
    (∀ j ∈ parents12, j < 12) ∧
    row 12 = base 12 ^^^ xorList (parents12.map row) := by decide +kernel

private theorem certified12 : Step 12 := ⟨parents12, check12⟩

private def parents13 : List ℕ := decodeParents 8 27237703363308355256206811137

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check13 :
    (∀ j ∈ parents13, j < 13) ∧
    row 13 = base 13 ^^^ xorList (parents13.map row) := by decide +kernel

private theorem certified13 : Step 13 := ⟨parents13, check13⟩

private def parents14 : List ℕ := decodeParents 7 3627183305229557313888257

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check14 :
    (∀ j ∈ parents14, j < 14) ∧
    row 14 = base 14 ^^^ xorList (parents14.map row) := by decide +kernel

private theorem certified14 : Step 14 := ⟨parents14, check14⟩

private def parents15 : List ℕ := decodeParents 8 34665948061930446419212165121

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check15 :
    (∀ j ∈ parents15, j < 15) ∧
    row 15 = base 15 ^^^ xorList (parents15.map row) := by decide +kernel

private theorem certified15 : Step 15 := ⟨parents15, check15⟩

private def parents16 : List ℕ := decodeParents 8 37141828288079662608759652353

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check16 :
    (∀ j ∈ parents16, j < 16) ∧
    row 16 = base 16 ^^^ xorList (parents16.map row) := by decide +kernel

private theorem certified16 : Step 16 := ⟨parents16, check16⟩

private def parents17 : List ℕ := decodeParents 4 6597673779207

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check17 :
    (∀ j ∈ parents17, j < 17) ∧
    row 17 = base 17 ^^^ xorList (parents17.map row) := by decide +kernel

private theorem certified17 : Step 17 := ⟨parents17, check17⟩

private def parents18 : List ℕ := decodeParents 3 1006731275

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check18 :
    (∀ j ∈ parents18, j < 18) ∧
    row 18 = base 18 ^^^ xorList (parents18.map row) := by decide +kernel

private theorem certified18 : Step 18 := ⟨parents18, check18⟩

private def parents19 : List ℕ := decodeParents 9 304265857940595968836510840569856

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check19 :
    (∀ j ∈ parents19, j < 19) ∧
    row 19 = base 19 ^^^ xorList (parents19.map row) := by decide +kernel

private theorem certified19 : Step 19 := ⟨parents19, check19⟩

private def parents20 : List ℕ := decodeParents 8 39617406172089007648683343878

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check20 :
    (∀ j ∈ parents20, j < 20) ∧
    row 20 = base 20 ^^^ xorList (parents20.map row) := by decide +kernel

private theorem certified20 : Step 20 := ⟨parents20, check20⟩

private def parents21 : List ℕ := decodeParents 6 590363369851278368770

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check21 :
    (∀ j ∈ parents21, j < 21) ∧
    row 21 = base 21 ^^^ xorList (parents21.map row) := by decide +kernel

private theorem certified21 : Step 21 := ⟨parents21, check21⟩

private def parents22 : List ℕ := decodeParents 8 34665343746617108043573288961

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check22 :
    (∀ j ∈ parents22, j < 22) ∧
    row 22 = base 22 ^^^ xorList (parents22.map row) := by decide +kernel

private theorem certified22 : Step 22 := ⟨parents22, check22⟩

private def parents23 : List ℕ := decodeParents 9 304263381455870038842307801776129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check23 :
    (∀ j ∈ parents23, j < 23) ∧
    row 23 = base 23 ^^^ xorList (parents23.map row) := by decide +kernel

private theorem certified23 : Step 23 := ⟨parents23, check23⟩

private def parents24 : List ℕ := decodeParents 7 2720230690605153126449153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check24 :
    (∀ j ∈ parents24, j < 24) ∧
    row 24 = base 24 ^^^ xorList (parents24.map row) := by decide +kernel

private theorem certified24 : Step 24 := ⟨parents24, check24⟩

private def parents25 : List ℕ := decodeParents 5 18015498423820289

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check25 :
    (∀ j ∈ parents25, j < 25) ∧
    row 25 = base 25 ^^^ xorList (parents25.map row) := by decide +kernel

private theorem certified25 : Step 25 := ⟨parents25, check25⟩

private def parents26 : List ℕ := decodeParents 6 516553875008144801799

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check26 :
    (∀ j ∈ parents26, j < 26) ∧
    row 26 = base 26 ^^^ xorList (parents26.map row) := by decide +kernel

private theorem certified26 : Step 26 := ⟨parents26, check26⟩

private def parents27 : List ℕ := decodeParents 11 20418936060096366556798001945115606704129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check27 :
    (∀ j ∈ parents27, j < 27) ∧
    row 27 = base 27 ^^^ xorList (parents27.map row) := by decide +kernel

private theorem certified27 : Step 27 := ⟨parents27, check27⟩

private def parents28 : List ℕ := decodeParents 11 19057806612695021097854835274593454833664

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check28 :
    (∀ j ∈ parents28, j < 28) ∧
    row 28 = base 28 ^^^ xorList (parents28.map row) := by decide +kernel

private theorem certified28 : Step 28 := ⟨parents28, check28⟩

private def parents29 : List ℕ := decodeParents 5 40533496560615431

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check29 :
    (∀ j ∈ parents29, j < 29) ∧
    row 29 = base 29 ^^^ xorList (parents29.map row) := by decide +kernel

private theorem certified29 : Step 29 := ⟨parents29, check29⟩

private def parents30 : List ℕ := decodeParents 8 34665948209526916457403826176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check30 :
    (∀ j ∈ parents30, j < 30) ∧
    row 30 = base 30 ^^^ xorList (parents30.map row) := by decide +kernel

private theorem certified30 : Step 30 := ⟨parents30, check30⟩

private def parents31 : List ℕ := decodeParents 11 21780564069415606715677495980448991469569

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check31 :
    (∀ j ∈ parents31, j < 31) ∧
    row 31 = base 31 ^^^ xorList (parents31.map row) := by decide +kernel

private theorem certified31 : Step 31 := ⟨parents31, check31⟩

private def parents32 : List ℕ := decodeParents 10 2658699407722779076730507932855230465

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check32 :
    (∀ j ∈ parents32, j < 32) ∧
    row 32 = base 32 ^^^ xorList (parents32.map row) := by decide +kernel

private theorem certified32 : Step 32 := ⟨parents32, check32⟩

private def parents33 : List ℕ := decodeParents 6 442739876565719449601

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check33 :
    (∀ j ∈ parents33, j < 33) ∧
    row 33 = base 33 ^^^ xorList (parents33.map row) := by decide +kernel

private theorem certified33 : Step 33 := ⟨parents33, check33⟩

private def parents34 : List ℕ := decodeParents 11 42197672623544598654497288401438594088961

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check34 :
    (∀ j ∈ parents34, j < 34) ∧
    row 34 = base 34 ^^^ xorList (parents34.map row) := by decide +kernel

private theorem certified34 : Step 34 := ⟨parents34, check34⟩

private def parents35 : List ℕ := decodeParents 9 567942134245993388979665852481536

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check35 :
    (∀ j ∈ parents35, j < 35) ∧
    row 35 = base 35 ^^^ xorList (parents35.map row) := by decide +kernel

private theorem certified35 : Step 35 := ⟨parents35, check35⟩

private def parents36 : List ℕ := decodeParents 11 43561294028629647812952336844632247762951

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check36 :
    (∀ j ∈ parents36, j < 36) ∧
    row 36 = base 36 ^^^ xorList (parents36.map row) := by decide +kernel

private theorem certified36 : Step 36 := ⟨parents36, check36⟩

private def parents37 : List ℕ := decodeParents 7 4533914563429775722995713

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check37 :
    (∀ j ∈ parents37, j < 37) ∧
    row 37 = base 37 ^^^ xorList (parents37.map row) := by decide +kernel

private theorem certified37 : Step 37 := ⟨parents37, check37⟩

private def parents38 : List ℕ := decodeParents 2 16390

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check38 :
    (∀ j ∈ parents38, j < 38) ∧
    row 38 = base 38 ^^^ xorList (parents38.map row) := by decide +kernel

private theorem certified38 : Step 38 := ⟨parents38, check38⟩

private def parents39 : List ℕ := decodeParents 14 25445017849717509770658863194669731600936463899820039

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check39 :
    (∀ j ∈ parents39, j < 39) ∧
    row 39 = base 39 ^^^ xorList (parents39.map row) := by decide +kernel

private theorem certified39 : Step 39 := ⟨parents39, check39⟩

private def parents40 : List ℕ := decodeParents 14 26193489431488822719044041309622475830407909689319425

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check40 :
    (∀ j ∈ parents40, j < 40) ∧
    row 40 = base 40 ^^^ xorList (parents40.map row) := by decide +kernel

private theorem certified40 : Step 40 := ⟨parents40, check40⟩

private def parents41 : List ℕ := decodeParents 13 3654133253641145860121471990464567575632947462150

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check41 :
    (∀ j ∈ parents41, j < 41) ∧
    row 41 = base 41 ^^^ xorList (parents41.map row) := by decide +kernel

private theorem certified41 : Step 41 := ⟨parents41, check41⟩

private def parents42 : List ℕ := decodeParents 16 1958664188523812492325419178167973781614722099645269552455681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check42 :
    (∀ j ∈ parents42, j < 42) ∧
    row 42 = base 42 ^^^ xorList (parents42.map row) := by decide +kernel

private theorem certified42 : Step 42 := ⟨parents42, check42⟩

private def parents43 : List ℕ := decodeParents 18 134817012841191319979454308887180650625705310475837529823813834948615

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check43 :
    (∀ j ∈ parents43, j < 43) ∧
    row 43 = base 43 ^^^ xorList (parents43.map row) := by decide +kernel

private theorem certified43 : Step 43 := ⟨parents43, check43⟩

private def parents44 : List ℕ := decodeParents 18 141555765379560989771421565463390909468735204943945413120168223047681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check44 :
    (∀ j ∈ parents44, j < 44) ∧
    row 44 = base 44 ^^^ xorList (parents44.map row) := by decide +kernel

private theorem certified44 : Step 44 := ⟨parents44, check44⟩

private def parents45 : List ℕ := decodeParents 16 2059134599925063831320520749969737924263086560617781247623174

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check45 :
    (∀ j ∈ parents45, j < 45) ∧
    row 45 = base 45 ^^^ xorList (parents45.map row) := by decide +kernel

private theorem certified45 : Step 45 := ⟨parents45, check45⟩

private def parents46 : List ℕ := decodeParents 17 18514035615141407291997659026637890190727818145046675436798525441

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check46 :
    (∀ j ∈ parents46, j < 46) ∧
    row 46 = base 46 ^^^ xorList (parents46.map row) := by decide +kernel

private theorem certified46 : Step 46 := ⟨parents46, check46⟩

private def parents47 : List ℕ := decodeParents 18 144928638647273926526794077510191799037966466219217562160564325597190

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check47 :
    (∀ j ∈ parents47, j < 47) ∧
    row 47 = base 47 ^^^ xorList (parents47.map row) := by decide +kernel

private theorem certified47 : Step 47 := ⟨parents47, check47⟩

private def parents48 : List ℕ := decodeParents 19 1214852285673836705071207915602618797098273673676199834233581192578334721

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check48 :
    (∀ j ∈ parents48, j < 48) ∧
    row 48 = base 48 ^^^ xorList (parents48.map row) := by decide +kernel

private theorem certified48 : Step 48 := ⟨parents48, check48⟩

private def parents49 : List ℕ := decodeParents 16 2209815690737146736423825149254351433043340905620365069271046

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check49 :
    (∀ j ∈ parents49, j < 49) ∧
    row 49 = base 49 ^^^ xorList (parents49.map row) := by decide +kernel

private theorem certified49 : Step 49 := ⟨parents49, check49⟩

private def parents50 : List ℕ := decodeParents 16 2310181884209254414237429037421287028320645858434091334033409

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check50 :
    (∀ j ∈ parents50, j < 50) ∧
    row 50 = base 50 ^^^ xorList (parents50.map row) := by decide +kernel

private theorem certified50 : Step 50 := ⟨parents50, check50⟩

private def parents51 : List ℕ := decodeParents 23 6217208327229171132464096884657218315049869733493754431599441297840844338851086327660545

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check51 :
    (∀ j ∈ parents51, j < 51) ∧
    row 51 = base 51 ^^^ xorList (parents51.map row) := by decide +kernel

private theorem certified51 : Step 51 := ⟨parents51, check51⟩

private def parents52 : List ℕ := decodeParents 18 161780662395831507857413809215011154150966217406191639572104578367494

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check52 :
    (∀ j ∈ parents52, j < 52) ∧
    row 52 = base 52 ^^^ xorList (parents52.map row) := by decide +kernel

private theorem certified52 : Step 52 := ⟨parents52, check52⟩

private def parents53 : List ℕ := decodeParents 18 165149421952349562541402578357710942264802492717933776504043616657409

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check53 :
    (∀ j ∈ parents53, j < 53) ∧
    row 53 = base 53 ^^^ xorList (parents53.map row) := by decide +kernel

private theorem certified53 : Step 53 := ⟨parents53, check53⟩

private def parents54 : List ℕ := decodeParents 15 300405048533047310750003340744711491312467929551788359687

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check54 :
    (∀ j ∈ parents54, j < 54) ∧
    row 54 = base 54 ^^^ xorList (parents54.map row) := by decide +kernel

private theorem certified54 : Step 54 := ⟨parents54, check54⟩

private def parents55 : List ℕ := decodeParents 28 243141093403658298523783216402037663509135409414660515964305396772938626111450820855951242956712174747172865

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check55 :
    (∀ j ∈ parents55, j < 55) ∧
    row 55 = base 55 ^^^ xorList (parents55.map row) := by decide +kernel

private theorem certified55 : Step 55 := ⟨parents55, check55⟩

private def parents56 : List ℕ := decodeParents 25 442271071846184099215762380858735747354180817849521653073920745369161539332609194929263858466816

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check56 :
    (∀ j ∈ parents56, j < 56) ∧
    row 56 = base 56 ^^^ xorList (parents56.map row) := by decide +kernel

private theorem certified56 : Step 56 := ⟨parents56, check56⟩

private def parents57 : List ℕ := decodeParents 20 11987781439926868006202227119583191473743606393770536897846775428413726441472

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check57 :
    (∀ j ∈ parents57, j < 57) ∧
    row 57 = base 57 ^^^ xorList (parents57.map row) := by decide +kernel

private theorem certified57 : Step 57 := ⟨parents57, check57⟩

private def parents58 : List ℕ := decodeParents 22 789298177326594837079974989756876671181124417701746399954681816453273215701467840513

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check58 :
    (∀ j ∈ parents58, j < 58) ∧
    row 58 = base 58 ^^^ xorList (parents58.map row) := by decide +kernel

private theorem certified58 : Step 58 := ⟨parents58, check58⟩

private def parents59 : List ℕ := decodeParents 23 7087660612644919423502374769524702852841561371733614396088770623236709739027590610468871

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check59 :
    (∀ j ∈ parents59, j < 59) ∧
    row 59 = base 59 ^^^ xorList (parents59.map row) := by decide +kernel

private theorem certified59 : Step 59 := ⟨parents59, check59⟩

private def parents60 : List ℕ := decodeParents 18 185372673062285335488031401631922847691311446712570386215198145945600

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check60 :
    (∀ j ∈ parents60, j < 60) ∧
    row 60 = base 60 ^^^ xorList (parents60.map row) := by decide +kernel

private theorem certified60 : Step 60 := ⟨parents60, check60⟩

private def parents61 : List ℕ := decodeParents 27 30800523424113478208115504189208850390578135561486771736448314891694103709151623507921426078803540574209

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check61 :
    (∀ j ∈ parents61, j < 61) ∧
    row 61 = base 61 ^^^ xorList (parents61.map row) := by decide +kernel

private theorem certified61 : Step 61 := ⟨parents61, check61⟩

private def parents62 : List ℕ := decodeParents 31 151322483379707146025442662851756041872204426273789115911701304761361266113879937525971439556264529600608628369512259585

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check62 :
    (∀ j ∈ parents62, j < 62) ∧
    row 62 = base 62 ^^^ xorList (parents62.map row) := by decide +kernel

private theorem certified62 : Step 62 := ⟨parents62, check62⟩

private def parents63 : List ℕ := decodeParents 27 33600341038321689121226105479864180534736232563245139683236894509583779524692969135486897974605409968135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check63 :
    (∀ j ∈ parents63, j < 63) ∧
    row 63 = base 63 ^^^ xorList (parents63.map row) := by decide +kernel

private theorem certified63 : Step 63 := ⟨parents63, check63⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem steps (k : Fin 64) : ∃ ps : List ℕ,
    (∀ j ∈ ps, j < 0 + k.val) ∧
    row (0 + k.val) = base (0 + k.val) ^^^ xorList (ps.map row) := by
  change Step (0 + k.val)
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

end Trace0000

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
