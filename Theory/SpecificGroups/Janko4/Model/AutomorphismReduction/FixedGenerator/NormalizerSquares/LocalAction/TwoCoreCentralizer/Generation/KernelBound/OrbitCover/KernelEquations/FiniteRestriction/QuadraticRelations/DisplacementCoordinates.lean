module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.RestrictionTransport

/-!
# Certified coordinates and pairing on the displacement space

Write `N = A - 1`. The displayed columns `E` and dual rows `C` satisfy
`C E = 1` and `E C N = N`; chosen lifts satisfy `N L = E`. Thus any matrix
commuting with `A` intertwines `E` with its extracted matrix `S = C g E`.
A further packed identity `F E = (C N)ᵀ J` identifies the displacement
pairing. Preservation of `F` then gives `Sᵀ J S = J`.

Every finite identity is proved by the Lean kernel, through rectangular XOR
multiplication. The subsequent arguments are ordinary matrix identities.
Neither exterior-space preservation nor chart reconstruction is needed until
the final exterior-transport corollary. These results do not assert membership
in `restrictionLinearSpace` or any of the nine quadratic relations.

The rectangular arithmetic follows `GeneratorCertificates/Packed.lean`.
The coordinate witnesses come from the unchanged ATLAS matrices and the saved
change of basis `(I,H,U)`, documented in `source/README.md`; ambient provenance
is `KernelEquations/source/README.md` and `Janko4/Model/Data.lean`.
-/

open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open GeneratorCertificates

private def rdecode {m : ℕ} (n : ℕ) (rows : Vector ℕ m) :
    Matrix (Fin m) (Fin n) (ZMod 2) := fun i j => bit (rows.get i) j.val

private def rproduct {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then ys.get k else 0))

private theorem rdecode_product {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) :
    rdecode k (Vector.ofFn (fun i => rproduct (xs.get i) ys)) =
      rdecode n xs * rdecode k ys := by
  funext i j
  simp only [rdecode, get_ofFn]
  rw [rproduct, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [rdecode, bit]
  cases h : (xs.get i).testBit a.val <;> simp [h]

private theorem rproduct_eq {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i, rproduct (xs.get i) ys = zs.get i) :
    rdecode n xs * rdecode k ys = rdecode k zs := by
  rw [← rdecode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = zs.get ⟨i, hi⟩
  rw [get_ofFn, h]

private theorem rproducts_eq {m n k l : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (ws : Vector ℕ l)
    (h : ∀ i, rproduct (xs.get i) ys = rproduct (zs.get i) ws) :
    rdecode n xs * rdecode k ys = rdecode l zs * rdecode k ws := by
  rw [← rdecode_product, ← rdecode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  simpa only [get_ofFn] using h ⟨i, hi⟩

private theorem rdecode_one (n : ℕ) :
    rdecode n (Vector.ofFn (fun i : Fin n => 2 ^ i.val)) = 1 := by
  funext i j
  simp only [rdecode, get_ofFn, bit, Nat.testBit_two_pow, decide_eq_true_eq,
    Matrix.one_apply, Fin.ext_iff]

private def embeddingRows : Vector ℕ 112 :=
  ⟨#[
    119477285147039,
    790680708051570,
    84095026867073,
    82375195184160,
    539605856530436,
    1073833702399310,
    373642317151682,
    949380886784660,
    465885335322939,
    250499650352094,
    643189567930722,
    946624143893287,
    50471942971765,
    1113023814658160,
    502744308554092,
    258270053759593,
    612015530628838,
    485018194323422,
    1108593761442460,
    310957456411604,
    327521678164551,
    1044861237340583,
    807211159951731,
    1086467843852852,
    509311635445753,
    571584675869944,
    987037193740386,
    840476914734881,
    322635470002717,
    612934877621608,
    598052449064741,
    107376298805102,
    273289519972024,
    894747975442083,
    177197923907438,
    1076986525808576,
    20770335098964,
    68483938120579,
    982674889107161,
    350092729779015,
    1038948516950416,
    962943729541639,
    170758992927912,
    86821695554714,
    378616201444368,
    477411322753261,
    413980720992724,
    565062799464848,
    34546589960191,
    1072414689447471,
    496691762461220,
    471527110130321,
    631121757578459,
    756004322575998,
    768034168583459,
    110178775353348,
    50976125520867,
    20002029723815,
    809697442832380,
    610696216685723,
    846369029501057,
    66261649111027,
    943295686885961,
    126523776041025,
    915364822258694,
    458290517423102,
    247628774951637,
    83411861568980,
    682832220918581,
    987938355830811,
    607972707663999,
    115159498645256,
    133056636258623,
    10394269507828,
    23876940972779,
    547939970745977,
    283953419985918,
    111786077757125,
    1040520852334589,
    1097519750279025,
    353524014036256,
    473607798873237,
    959536724509791,
    1001124117836957,
    131513599494283,
    849101674445353,
    804015349845368,
    30702872825711,
    865826245419534,
    846663665731482,
    719406918583060,
    773536977074968,
    319569665814392,
    710253742986095,
    20867924679506,
    929665634124192,
    908506913920203,
    844674658756839,
    207842696372086,
    614770603101704,
    624107318439403,
    242726700048424,
    677122511830536,
    368942445240885,
    816433481959915,
    672132449671121,
    498159113355857,
    687482730142171,
    543704922226688,
    408508322962744,
    906826141821634,
    431462371927679], rfl⟩

private def displacementRows : Vector ℕ 112 :=
  ⟨#[
    1992620233831200998739695420821919,
    4548812463040436436398002310738546,
    4579763007375449631904229919828865,
    4080153871114733878802426523241504,
    1439978407090975369276215590760452,
    3365133212822434824860433551269198,
    1471229623365047717343295211716034,
    2822217237604101094078468862470804,
    2494842593938752814577701115068731,
    261989887220116426361920830632926,
    2043631208997996640758850379071842,
    2671114374041930408704149026054951,
    4593489923350193260226978762154357,
    3272122105173178179713150993655920,
    4401778904369502298524477752645996,
    4186640874167064257934436810586729,
    1211655171817095840583015222531814,
    1668560972834249876829729169778654,
    533277261393297183288791114832540,
    5155790246375968049885198904118228,
    4452397812055568636441119076942407,
    4456317569528337584147099080206759,
    5121085709918811605613434287331699,
    4187358161972724780793859571747380,
    1083632858118452297017707823126521,
    126562542495709282751057400722680,
    4485664455508295821100726646480994,
    2985790501362743443628532996101921,
    333057385183139901424494926158365,
    1364690842904553665005306029452648,
    247341916192671925289858676332325,
    3846835328051482079834025216034670,
    2071616325741326621747171901456056,
    4977063607425746817521170285158051,
    4485001132195498749715462667319150,
    3656982944221797112223975800076224,
    3390627978665772084786808046618708,
    4450671938776768667310407296086915,
    359095039370532054102688704620249,
    193860211646370267853536375866183,
    4967398328541890126731947551682960,
    4615791266623557848327496078991879,
    2844767310072929330246124851535016,
    5044436561122103157859583213601946,
    3955697864619984484003433552116752,
    4468606862217571656379912942383341,
    2896133387748016457249844198740436,
    1639790737743510901779765073549712,
    2576523075216148486904889220859903,
    1570107686070616544045081259003439,
    215623166937565703891908169857572,
    1755917299747168800512603274525329,
    4030437299374614446591847026107611,
    4060315491199453155173085832840830,
    3918288086894550822760239894050083,
    3858918071873317592341490270750724,
    700071904588650241896056671079395,
    2492852204312354985611315023732903,
    4211648467434974241280737397743612,
    1860194739368744859636423176727707,
    1377089117534174925034667355287681,
    213149696801598184365101096548339,
    3917546910146533182284980320322121,
    2113133545577609713968648996651073,
    2363180867628201113503926607549446,
    883356838175881407946024384639998,
    3922693348952197704648915205933781,
    3407398649571345036105492665007572,
    4703800760738906720855857806447413,
    2935051774930715193415864865153051,
    2585260127377633750188220244951167,
    1882609333292007232645701052817160,
    4116399301095794581605092248127807,
    4032127327201739858117476367589620,
    4877107277339695466448826966328043,
    552458403155606577083211892950649,
    578012274622256332021454947951614,
    5101441613208550959385885732544197,
    2219588841404867069438155200980989,
    334435294954958170844863697350513,
    25816902013153045090777950500128,
    520271695141072586656317592919189,
    1383234265864617379410385580131423,
    2455140847666766094315274323588253,
    3604314176894371384851477047642251,
    3008769244863232426884862674139689,
    2771235082458873119435550096510328,
    4729391198093550010744461765906287,
    897670596758349925241501103399438,
    4774142460210199083409940010387354,
    4295171325615101236047129095750420,
    2390426491765121008587475175422744,
    2350264058083407207353470843187064,
    1116906907851823257676052538659695,
    2101824797251837182397154523405138,
    3874764303704402287932834303820192,
    4242170499258811479174310818567371,
    2434267959008249639056382136969447,
    3482784460074026443879340265840502,
    3353402370236922825928361745485320,
    3686524577171368513558906369502699,
    2721041971484688649844298853638184,
    3681791044548172245236478267457032,
    3562831367296346332993925708784181,
    389973376413848344087502133185003,
    1064474590998777186293121844484049,
    1200841012465749742099717488001617,
    4188345524188256435639301471689179,
    5190843908382623455852659369607168,
    5074946231096776520764287620898104,
    1137087748607662430291228422466242,
    431602574313010130416431222335103], rfl⟩

private def imageCoordinateRows : Vector ℕ 50 :=
  ⟨#[
    4154426621330580540153828942544897,
    933764872920218781398721884061698,
    456295066825881468893732938973188,
    342513422648270058213592155553800,
    3524873274854897558006322966822928,
    557184045108172901871768330829856,
    174523670380518033872878057816128,
    1217934980581926084545405784162432,
    513812521563332071865881855000832,
    1402226537656008858206459087815168,
    109375314182792687001361943888896,
    5030528822929230829531236665395200,
    3096085630284122935615014383390720,
    5153296449249281363318163445391360,
    1226793265343965860387845744640000,
    3085210869650833653132472596070400,
    4941429861551744462161582974107648,
    3609659582841341546825908232519680,
    3448994076083782768815882979508224,
    3254080945185185332906200060657664,
    756349720879486875868105339305984,
    2791228087302701574497857416724480,
    4565665434194577492996722241044480,
    1948279757508965974000826358693888,
    4866795922018999167272506330447872,
    3283958197732363558837355817205760,
    2877207325760316217010963177537536,
    3690446277908733430107019658919936,
    4659328104220082632394745854296064,
    1241412238430971694370966103654400,
    1600342362371343525881111770038272,
    2501414262046060956598352169926656,
    1903337617220819068926171912601600,
    614352044398487462210715017805824,
    3393427121188261548328547006808064,
    4957207752270137869325642288332800,
    2586841984217624017473072753803264,
    1969791376546100265960877234061312,
    4808111637804157827067416607195136,
    658943799589437932756900249600000,
    3668645116287299761098271448104960,
    4166471767278927726234591536611328,
    966402910171750923827518571020288,
    901662757478820021224379219181568,
    2157900346489038739597862744621056,
    2828989377783591471868691940900864,
    946091136930214933544173593165824,
    3116266006841871827843862220505088,
    4506324637899143196977778535694336,
    748665360403723681450148654743552], rfl⟩

private def liftRows : Vector ℕ 112 :=
  ⟨#[
    1,
    2,
    4,
    8,
    16,
    32,
    64,
    128,
    256,
    512,
    1024,
    2048,
    4096,
    8192,
    16384,
    32768,
    65536,
    131072,
    262144,
    524288,
    1048576,
    2097152,
    4194304,
    8388608,
    16777216,
    33554432,
    67108864,
    134217728,
    268435456,
    536870912,
    1073741824,
    2147483648,
    4294967296,
    8589934592,
    17179869184,
    34359738368,
    68719476736,
    137438953472,
    274877906944,
    549755813888,
    1099511627776,
    2199023255552,
    4398046511104,
    8796093022208,
    17592186044416,
    35184372088832,
    70368744177664,
    140737488355328,
    281474976710656,
    562949953421312,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0], rfl⟩

private def imageCoordinateTransposeRows : Vector ℕ 112 :=
  ⟨#[
    1,
    2,
    4,
    8,
    16,
    32,
    64,
    128,
    256,
    512,
    1024,
    2048,
    4096,
    8192,
    16384,
    32768,
    65536,
    131072,
    262144,
    524288,
    1048576,
    2097152,
    4194304,
    8388608,
    16777216,
    33554432,
    67108864,
    134217728,
    268435456,
    536870912,
    1073741824,
    2147483648,
    4294967296,
    8589934592,
    17179869184,
    34359738368,
    68719476736,
    137438953472,
    274877906944,
    549755813888,
    1099511627776,
    2199023255552,
    4398046511104,
    8796093022208,
    17592186044416,
    35184372088832,
    70368744177664,
    140737488355328,
    281474976710656,
    562949953421312,
    176594070787566,
    970927010744074,
    442814455201769,
    611579356825596,
    187406466133906,
    703618756513431,
    204778039041043,
    544941402445546,
    657952890242020,
    103706489421235,
    83444912598007,
    88427570683285,
    559691149196549,
    90312085363606,
    54286067136111,
    808185713964269,
    574944616890117,
    1123598607596426,
    850355565792153,
    736018512159496,
    832022710099245,
    196964800410044,
    410366324411012,
    1039233996730192,
    385999727458336,
    836467540374192,
    286119778470755,
    833575936089141,
    1038927776647053,
    4144296321150,
    568417240853667,
    973619524077242,
    957292059575147,
    741901039737768,
    941044835865648,
    885847805572325,
    72656430099285,
    186105250768188,
    115663395064082,
    142864244436528,
    751254553748083,
    832956727259457,
    963203283663617,
    567637349509433,
    1094468237180998,
    489661600474850,
    919764276945166,
    35696780786268,
    526553874488709,
    882899632439542,
    44675132744037,
    1125386575107628,
    628438794388797,
    779628354670681,
    183024653371184,
    409116053151782,
    931696468846231,
    561111256857075,
    423430759643564,
    666290018543762,
    301789396150785,
    461022316967953], rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem embedding_decode : rdecode 50 embeddingRows = restrictionEmbedding := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem displacement_decode : rdecode 112 displacementRows = matrixA - 1 := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem lifts_decode : rdecode 50 liftRows = restrictionLifts := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem imageCoordinate_transpose :
    rdecode 50 imageCoordinateTransposeRows = (rdecode 112 imageCoordinateRows)ᵀ := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem embedding_factorization :
    restrictionEmbedding * rdecode 112 imageCoordinateRows = matrixA - 1 := by
  rw [← embedding_decode, ← displacement_decode]
  apply rproduct_eq
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
public theorem restrictionExtraction_embedding :
    restrictionExtraction * restrictionEmbedding = 1 := by
  change rdecode 112 restrictionDualRows * restrictionEmbedding = 1
  rw [← embedding_decode, ← rdecode_one 50]
  apply rproduct_eq
  simp only [get_ofFn]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem imageCoordinate_lifts :
    rdecode 112 imageCoordinateRows * restrictionLifts = 1 := by
  rw [← lifts_decode, ← rdecode_one 50]
  apply rproduct_eq
  simp only [get_ofFn]
  decide +kernel

public theorem restrictionEmbedding_displacement :
    (matrixA - 1) * restrictionLifts = restrictionEmbedding := by
  rw [← embedding_factorization, Matrix.mul_assoc, imageCoordinate_lifts, Matrix.mul_one]

private theorem extraction_displacement :
    restrictionExtraction * (matrixA - 1) = rdecode 112 imageCoordinateRows := by
  rw [← embedding_factorization, ← Matrix.mul_assoc, restrictionExtraction_embedding,
    Matrix.one_mul]

public theorem restrictionEmbedding_extraction_displacement :
    restrictionEmbedding * restrictionExtraction * (matrixA - 1) = matrixA - 1 := by
  rw [Matrix.mul_assoc, extraction_displacement, embedding_factorization]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem pairing_factorization :
    invariantForm * restrictionEmbedding =
      (rdecode 112 imageCoordinateRows)ᵀ * restrictionPairing := by
  change rdecode 112 invariantFormRows * restrictionEmbedding = _
  rw [← embedding_decode, ← imageCoordinate_transpose]
  change rdecode 112 invariantFormRows * rdecode 50 embeddingRows =
    rdecode 50 imageCoordinateTransposeRows * rdecode 50 restrictionPairingRows
  apply rproducts_eq
  decide +kernel

public theorem restrictionPairing_identity :
    restrictionLiftsᵀ * invariantForm * restrictionEmbedding = restrictionPairing := by
  rw [Matrix.mul_assoc, pairing_factorization, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, imageCoordinate_lifts, Matrix.transpose_one, Matrix.one_mul]

public theorem restrictionPairing_factorization :
    invariantForm * restrictionEmbedding =
      (restrictionExtraction * (matrixA - 1))ᵀ * restrictionPairing := by
  rw [extraction_displacement, pairing_factorization]

public theorem restrictionMatrix_intertwining (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    (g : BinaryMatrix) * restrictionEmbedding =
      restrictionEmbedding * restrictionMatrix g := by
  have hc : (g : BinaryMatrix) * (matrixA - 1) = (matrixA - 1) * (g : BinaryMatrix) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hker.1]
  have hg : (g : BinaryMatrix) * restrictionEmbedding =
      (matrixA - 1) * (g : BinaryMatrix) * restrictionLifts := by
    rw [← restrictionEmbedding_displacement, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  calc
    _ = (matrixA - 1) * (g : BinaryMatrix) * restrictionLifts := hg
    _ = (restrictionEmbedding * restrictionExtraction * (matrixA - 1)) *
        (g : BinaryMatrix) * restrictionLifts := by
      rw [restrictionEmbedding_extraction_displacement]
    _ = restrictionEmbedding * (restrictionExtraction *
        ((matrixA - 1) * (g : BinaryMatrix) * restrictionLifts)) := by
      simp only [Matrix.mul_assoc]
    _ = restrictionEmbedding * (restrictionExtraction *
        ((g : BinaryMatrix) * restrictionEmbedding)) := by rw [← hg]
    _ = _ := by simp only [restrictionMatrix, Matrix.mul_assoc]

public theorem restrictionMatrix_pairing (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm) :
    (restrictionMatrix g)ᵀ * restrictionPairing * restrictionMatrix g =
      restrictionPairing := by
  have hc : (g : BinaryMatrix) * (matrixA - 1) = (matrixA - 1) * (g : BinaryMatrix) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hker.1]
  have hs : restrictionExtraction * (matrixA - 1) * (g : BinaryMatrix) * restrictionLifts =
      restrictionMatrix g := by
    calc
      _ = restrictionExtraction * ((matrixA - 1) * (g : BinaryMatrix)) *
          restrictionLifts := by simp only [Matrix.mul_assoc]
      _ = restrictionExtraction * ((g : BinaryMatrix) * (matrixA - 1)) *
          restrictionLifts := by rw [hc]
      _ = restrictionExtraction * (g : BinaryMatrix) *
          ((matrixA - 1) * restrictionLifts) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [restrictionEmbedding_displacement]; rfl
  calc
    _ = (restrictionExtraction * (matrixA - 1) * (g : BinaryMatrix) * restrictionLifts)ᵀ *
        restrictionPairing * restrictionMatrix g := by rw [hs]
    _ = restrictionLiftsᵀ * (g : BinaryMatrix)ᵀ *
        (invariantForm * restrictionEmbedding) * restrictionMatrix g := by
      rw [restrictionPairing_factorization]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = restrictionLiftsᵀ * (g : BinaryMatrix)ᵀ * invariantForm *
        ((g : BinaryMatrix) * restrictionEmbedding) := by
      rw [restrictionMatrix_intertwining g hker]
      simp only [Matrix.mul_assoc]
    _ = restrictionLiftsᵀ * formPullback g invariantForm * restrictionEmbedding := by
      simp only [formPullback, Matrix.mul_assoc]
    _ = restrictionPairing := by rw [hform, restrictionPairing_identity]

/-- The extracted zeroth column is the actual ambient base image. -/
public theorem restrictionImage_matrix (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    restrictionImage (restrictionMatrix g) =
      (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) :=
  restrictionImage_eq_of_intertwining g _ (restrictionMatrix_intertwining g hker)

/-- The nine test pullbacks satisfy the finite exterior membership conditions. -/
public theorem restrictionTestForm_preserved (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace)
    (i : Fin 9) :
    (restrictionMatrix g)ᵀ * restrictionTestForm i * restrictionMatrix g ∈
      restrictionExteriorSpace :=
  restrictionTestForm_preserved_of_intertwining g _
    (restrictionMatrix_intertwining g hker) hext i

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
