module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.FinalProducts.HaBlocks.Basic

/-!
# HA product rows 0 through 31

Each expanded integer row sum and its binary parity is checked independently
by kernel reduction. The proved one-row checks combine into a bounded interval.
The exact input is H = 1 + B + (A + BA) + UB and the output is the fixed HA table.
See `source/README.md` for reproduction, source attribution and conventions.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.HaBlocks

private def sum0000 : Nat := 0

set_option maxRecDepth 8192 in
private theorem sum0000_checked : Wide.sumRow hRows[0]! wideFirst = sum0000 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0000_checked : Wide.checkParity 1792 sum0000 haRows[0]! = true := by
  decide +kernel

private theorem row0000 :
    Wide.checkRows 1792 ((hRows.drop 0).take 1) wideFirst ((haRows.drop 0).take 1) = true :=
  row_checked hRows wideFirst haRows 0 sum0000
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0000_checked parity0000_checked

private def sum0001 : Nat := 91343852333181756906283960471494753428212551680

set_option maxRecDepth 8192 in
private theorem sum0001_checked : Wide.sumRow hRows[1]! wideFirst = sum0001 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0001_checked : Wide.checkParity 1792 sum0001 haRows[1]! = true := by
  decide +kernel

private theorem row0001 :
    Wide.checkRows 1792 ((hRows.drop 1).take 1) wideFirst ((haRows.drop 1).take 1) = true :=
  row_checked hRows wideFirst haRows 1 sum0001
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0001_checked parity0001_checked

private def sum0002 : Nat := 91343852333181756985512122985758809546779791360

set_option maxRecDepth 8192 in
private theorem sum0002_checked : Wide.sumRow hRows[2]! wideFirst = sum0002 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0002_checked : Wide.checkParity 1792 sum0002 haRows[2]! = true := by
  decide +kernel

private theorem row0002 :
    Wide.checkRows 1792 ((hRows.drop 2).take 1) wideFirst ((haRows.drop 2).take 1) = true :=
  row_checked hRows wideFirst haRows 2 sum0002
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0002_checked parity0002_checked

private def sum0003 : Nat := 91343852333181432387730302045920610301822111744

set_option maxRecDepth 8192 in
private theorem sum0003_checked : Wide.sumRow hRows[3]! wideFirst = sum0003 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0003_checked : Wide.checkParity 1792 sum0003 haRows[3]! = true := by
  decide +kernel

private theorem row0003 :
    Wide.checkRows 1792 ((hRows.drop 3).take 1) wideFirst ((haRows.drop 3).take 1) = true :=
  row_checked hRows wideFirst haRows 3 sum0003
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0003_checked parity0003_checked

private def sum0004 : Nat := 1766847064778384329583671645162075226974544119420961563205740058206277632

set_option maxRecDepth 8192 in
private theorem sum0004_checked : Wide.sumRow hRows[4]! wideFirst = sum0004 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0004_checked : Wide.checkParity 1792 sum0004 haRows[4]! = true := by
  decide +kernel

private theorem row0004 :
    Wide.checkRows 1792 ((hRows.drop 4).take 1) wideFirst ((haRows.drop 4).take 1) = true :=
  row_checked hRows wideFirst haRows 4 sum0004
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0004_checked parity0004_checked

private def sum0005 : Nat := 29642774844752946028440449263959491091200951864151710633518484855009021364535297

set_option maxRecDepth 8192 in
private theorem sum0005_checked : Wide.sumRow hRows[5]! wideFirst = sum0005 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0005_checked : Wide.checkParity 1792 sum0005 haRows[5]! = true := by
  decide +kernel

private theorem row0005 :
    Wide.checkRows 1792 ((hRows.drop 5).take 1) wideFirst ((haRows.drop 5).take 1) = true :=
  row_checked hRows wideFirst haRows 5 sum0005
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0005_checked parity0005_checked

private def sum0006 : Nat := 374144419156711147060143317175369605953423354630145

set_option maxRecDepth 8192 in
private theorem sum0006_checked : Wide.sumRow hRows[6]! wideFirst = sum0006 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0006_checked : Wide.checkParity 1792 sum0006 haRows[6]! = true := by
  decide +kernel

private theorem row0006 :
    Wide.checkRows 1792 ((hRows.drop 6).take 1) wideFirst ((haRows.drop 6).take 1) = true :=
  row_checked hRows wideFirst haRows 6 sum0006
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0006_checked parity0006_checked

private def sum0007 : Nat := 39402006196394479212279040100143735251528278223285325162751642036401582676214101955523230975480823340463226095665152

set_option maxRecDepth 8192 in
private theorem sum0007_checked : Wide.sumRow hRows[7]! wideFirst = sum0007 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0007_checked : Wide.checkParity 1792 sum0007 haRows[7]! = true := by
  decide +kernel

private theorem row0007 :
    Wide.checkRows 1792 ((hRows.drop 7).take 1) wideFirst ((haRows.drop 7).take 1) = true :=
  row_checked hRows wideFirst haRows 7 sum0007
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0007_checked parity0007_checked

private def sum0008 : Nat := 661055968790248598951915308032773076864381017450367487730337204652566843078849430923595511511122199986910052933019770028032

set_option maxRecDepth 8192 in
private theorem sum0008_checked : Wide.sumRow hRows[8]! wideFirst = sum0008 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0008_checked : Wide.checkParity 1792 sum0008 haRows[8]! = true := by
  decide +kernel

private theorem row0008 :
    Wide.checkRows 1792 ((hRows.drop 8).take 1) wideFirst ((haRows.drop 8).take 1) = true :=
  row_checked hRows wideFirst haRows 8 sum0008
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0008_checked parity0008_checked

private def sum0009 : Nat := 186070713419675363980626894819329160934516234722066186591901633525771425139632718225772240300675856174780475829345153697758411463476641792

set_option maxRecDepth 8192 in
private theorem sum0009_checked : Wide.sumRow hRows[9]! wideFirst = sum0009 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0009_checked : Wide.checkParity 1792 sum0009 haRows[9]! = true := by
  decide +kernel

private theorem row0009 :
    Wide.checkRows 1792 ((hRows.drop 9).take 1) wideFirst ((haRows.drop 9).take 1) = true :=
  row_checked hRows wideFirst haRows 9 sum0009
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0009_checked parity0009_checked

private def sum0010 : Nat := 39402006196394479212279040100143613805079739270465446667948293404245813115349545122074649770102834465505465069473792

set_option maxRecDepth 8192 in
private theorem sum0010_checked : Wide.sumRow hRows[10]! wideFirst = sum0010 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0010_checked : Wide.checkParity 1792 sum0010 haRows[10]! = true := by
  decide +kernel

private theorem row0010 :
    Wide.checkRows 1792 ((hRows.drop 10).take 1) wideFirst ((haRows.drop 10).take 1) = true :=
  row_checked hRows wideFirst haRows 10 sum0010
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0010_checked parity0010_checked

private def sum0011 : Nat := 247330401473104534060502521019647190035131349103920186218196704602803222123542130120493375047347705146773724605033764197162699804180520934989821479480993287770223621619843072

set_option maxRecDepth 8192 in
private theorem sum0011_checked : Wide.sumRow hRows[11]! wideFirst = sum0011 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0011_checked : Wide.checkParity 1792 sum0011 haRows[11]! = true := by
  decide +kernel

private theorem row0011 :
    Wide.checkRows 1792 ((hRows.drop 11).take 1) wideFirst ((haRows.drop 11).take 1) = true :=
  row_checked hRows wideFirst haRows 11 sum0011
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0011_checked parity0011_checked

private def sum0012 : Nat := 285152538601387201165073225356268207805826781703035757992912412778670926578930411448191325905711324887340945504307880260028627542510834388474996886072805702982627427357859154378118252275433472

set_option maxRecDepth 8192 in
private theorem sum0012_checked : Wide.sumRow hRows[12]! wideFirst = sum0012 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0012_checked : Wide.checkParity 1792 sum0012 haRows[12]! = true := by
  decide +kernel

private theorem row0012 :
    Wide.checkRows 1792 ((hRows.drop 12).take 1) wideFirst ((haRows.drop 12).take 1) = true :=
  row_checked hRows wideFirst haRows 12 sum0012
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0012_checked parity0012_checked

private def sum0013 : Nat := 4784065733063810973581885157618788676291241975216678764449069467952930096753259332042012378297916388616123557510348076179660689109968021826914775686221365528077855789326668137453835882733813798797312

set_option maxRecDepth 8192 in
private theorem sum0013_checked : Wide.sumRow hRows[13]! wideFirst = sum0013 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0013_checked : Wide.checkParity 1792 sum0013 haRows[13]! = true := by
  decide +kernel

private theorem row0013 :
    Wide.checkRows 1792 ((hRows.drop 13).take 1) wideFirst ((haRows.drop 13).take 1) = true :=
  row_checked hRows wideFirst haRows 13 sum0013
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0013_checked parity0013_checked

private def sum0014 : Nat := 1346594790796383617853693410017312938380886989522732508910254011682313475017735992743516965097550361932450732429672946510284539166923362946734623463000620587253753675128758136609072235504114761084662961767702331392

set_option maxRecDepth 8192 in
private theorem sum0014_checked : Wide.sumRow hRows[14]! wideFirst = sum0014 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0014_checked : Wide.checkParity 1792 sum0014 haRows[14]! = true := by
  decide +kernel

private theorem row0014 :
    Wide.checkRows 1792 ((hRows.drop 14).take 1) wideFirst ((haRows.drop 14).take 1) = true :=
  row_checked hRows wideFirst haRows 14 sum0014
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0014_checked parity0014_checked

private def sum0015 : Nat := 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044991364518490794523670467158075915558584153377079127826032023434965270134784

set_option maxRecDepth 8192 in
private theorem sum0015_checked : Wide.sumRow hRows[15]! wideFirst = sum0015 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0015_checked : Wide.checkParity 1792 sum0015 haRows[15]! = true := by
  decide +kernel

private theorem row0015 :
    Wide.checkRows 1792 ((hRows.drop 15).take 1) wideFirst ((haRows.drop 15).take 1) = true :=
  row_checked hRows wideFirst haRows 15 sum0015
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0015_checked parity0015_checked

private def sum0016 : Nat := 26046931378436930758124421057504913270096712196546516251547883090268594894061296791198920631129399332112575881819294883494030887968437806339681335581508814878911636459572125045968197364988098415497099841948845718468001457088501864372109312

set_option maxRecDepth 8192 in
private theorem sum0016_checked : Wide.sumRow hRows[16]! wideFirst = sum0016 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0016_checked : Wide.checkParity 1792 sum0016 haRows[16]! = true := by
  decide +kernel

private theorem row0016 :
    Wide.checkRows 1792 ((hRows.drop 16).take 1) wideFirst ((haRows.drop 16).take 1) = true :=
  row_checked hRows wideFirst haRows 16 sum0016
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0016_checked parity0016_checked

private def sum0017 : Nat := 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348379293231762796991140110055761159372645599229499369159485276233395036103599194112

set_option maxRecDepth 8192 in
private theorem sum0017_checked : Wide.sumRow hRows[17]! wideFirst = sum0017 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0017_checked : Wide.checkParity 1792 sum0017 haRows[17]! = true := by
  decide +kernel

private theorem row0017 :
    Wide.checkRows 1792 ((hRows.drop 17).take 1) wideFirst ((haRows.drop 17).take 1) = true :=
  row_checked hRows wideFirst haRows 17 sum0017
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0017_checked parity0017_checked

private def sum0018 : Nat := 34622310392506957584946940144288832324819178359103260074178033026772100897557837698877842840618484956629558357043317557561914040570997209208181538116479196669187490996323954443198916321442050196460802152043435621394342437232329674821427918626773301569682730076751558252429312

set_option maxRecDepth 8192 in
private theorem sum0018_checked : Wide.sumRow hRows[18]! wideFirst = sum0018 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0018_checked : Wide.checkParity 1792 sum0018 haRows[18]! = true := by
  decide +kernel

private theorem row0018 :
    Wide.checkRows 1792 ((hRows.drop 18).take 1) wideFirst ((haRows.drop 18).take 1) = true :=
  row_checked hRows wideFirst haRows 18 sum0018
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0018_checked parity0018_checked

private def sum0019 : Nat := 39916806190694396233127454260736771321349025208709150830050944848744237837384798314557052093535060603687689867992396398875523394853277174170910820448552344279219234559599470236796843678677574771401489848832926706312448004365651182437671986416357704882989336788663365292841625710619337752051712

set_option maxRecDepth 8192 in
private theorem sum0019_checked : Wide.sumRow hRows[19]! wideFirst = sum0019 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0019_checked : Wide.checkParity 1792 sum0019 haRows[19]! = true := by
  decide +kernel

private theorem row0019 :
    Wide.checkRows 1792 ((hRows.drop 19).take 1) wideFirst ((haRows.drop 19).take 1) = true :=
  row_checked hRows wideFirst haRows 19 sum0019
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0019_checked parity0019_checked

private def sum0020 : Nat := 669692879491417075592765655662501131600878007315958504652343992731469406953177613847647937630749939728288031819297013930725518295886521991719544849851936677690826162569686135837244792237904227674289182312672479512925840960832186477944734878949246451804526634698606813795618636961054922308660968292352

set_option maxRecDepth 8192 in
private theorem sum0020_checked : Wide.sumRow hRows[20]! wideFirst = sum0020 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0020_checked : Wide.checkParity 1792 sum0020 haRows[20]! = true := by
  decide +kernel

private theorem row0020 :
    Wide.checkRows 1792 ((hRows.drop 20).take 1) wideFirst ((haRows.drop 20).take 1) = true :=
  row_checked hRows wideFirst haRows 20 sum0020
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0020_checked parity0020_checked

private def sum0021 : Nat := 12953744211667879574559702190010707651171625584905095574841686913755541732351702201192178834749432073008008736388873591996533989061941859602080530466509063710519453423322542935805405256329245056010952252515948890880159053729148369140671256893233417553615565373182352443484843956926466818982276660503088819543865047887917350912

set_option maxRecDepth 8192 in
private theorem sum0021_checked : Wide.sumRow hRows[21]! wideFirst = sum0021 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0021_checked : Wide.checkParity 1792 sum0021 haRows[21]! = true := by
  decide +kernel

private theorem row0021 :
    Wide.checkRows 1792 ((hRows.drop 21).take 1) wideFirst ((haRows.drop 21).take 1) = true :=
  row_checked hRows wideFirst haRows 21 sum0021
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0021_checked parity0021_checked

private def sum0022 : Nat := 217327764647901735884376228537482684576559015509079127959763147156450094840678695797076204826225654552053426203116235541270728306952424662628579379879251559884728725949582511922565099770969861780602519240059665486169622196106484589438088060090415788661798987949040870893257638593207446026207046786818348185228905683265773977921912832

set_option maxRecDepth 8192 in
private theorem sum0022_checked : Wide.sumRow hRows[22]! wideFirst = sum0022 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0022_checked : Wide.checkParity 1792 sum0022 haRows[22]! = true := by
  decide +kernel

private theorem row0022 :
    Wide.checkRows 1792 ((hRows.drop 22).take 1) wideFirst ((haRows.drop 22).take 1) = true :=
  row_checked hRows wideFirst haRows 22 sum0022
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0022_checked parity0022_checked

private def sum0023 : Nat := 61172327492847069472032393719205726809135813743440799050195397570919697796091958321786986941313694928524412354321192270208874740224216865716278547593828880641586426463783632421803323346359777108662387813123442705596174213050687631173740486250853511073534925737133043254421487025718481577280022779248469433469322822027916558991255163837951300861952

set_option maxRecDepth 8192 in
private theorem sum0023_checked : Wide.sumRow hRows[23]! wideFirst = sum0023 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0023_checked : Wide.checkParity 1792 sum0023 haRows[23]! = true := by
  decide +kernel

private theorem row0023 :
    Wide.checkRows 1792 ((hRows.drop 23).take 1) wideFirst ((haRows.drop 23).take 1) = true :=
  row_checked hRows wideFirst haRows 23 sum0023
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0023_checked parity0023_checked

private def sum0024 : Nat := 34622310392506957584946940144288832324819178359103260074178033026772100877957520390515409281853501465865381150278099185099233529659567999369251322492547208112307431728755191675294267782542924177892485653785149272170340296438112619382660071997436134823872819973812332340969472

set_option maxRecDepth 8192 in
private theorem sum0024_checked : Wide.sumRow hRows[24]! wideFirst = sum0024 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0024_checked : Wide.checkParity 1792 sum0024 haRows[24]! = true := by
  decide +kernel

private theorem row0024 :
    Wide.checkRows 1792 ((hRows.drop 24).take 1) wideFirst ((haRows.drop 24).take 1) = true :=
  row_checked hRows wideFirst haRows 24 sum0024
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0024_checked parity0024_checked

private def sum0025 : Nat := 1183244898432394516240178782864414363145358748541491968958224828202629403184955697044215348993654013729142299534551766639314290654523986398306995803195197003043106967857889104253534023666188757448912662064834662572469088210747144284404747343186301647850953792976935032002581046060222426268478660306859998050385018801807183080644190194345203502297055239794531690295561551872

set_option maxRecDepth 8192 in
private theorem sum0025_checked : Wide.sumRow hRows[25]! wideFirst = sum0025 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0025_checked : Wide.checkParity 1792 sum0025 haRows[25]! = true := by
  decide +kernel

private theorem row0025 :
    Wide.checkRows 1792 ((hRows.drop 25).take 1) wideFirst ((haRows.drop 25).take 1) = true :=
  row_checked hRows wideFirst haRows 25 sum0025
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0025_checked parity0025_checked

private def sum0026 : Nat := 39916806190694396233127454260736771321349025208709150830050944848744237837379281315699159309852714021786848936883849904879448759767871873214783435965696628406400113459022374586319544677486211658961108249630065950604589847642088846164383507558409295332930884471650166871713054678620328712732672

set_option maxRecDepth 8192 in
private theorem sum0026_checked : Wide.sumRow hRows[26]! wideFirst = sum0026 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0026_checked : Wide.checkParity 1792 sum0026 haRows[26]! = true := by
  decide +kernel

private theorem row0026 :
    Wide.checkRows 1792 ((hRows.drop 26).take 1) wideFirst ((haRows.drop 26).take 1) = true :=
  row_checked hRows wideFirst haRows 26 sum0026
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0026_checked parity0026_checked

private def sum0027 : Nat := 1572802244866018108182967249994981337399178505432223228293716677435703277129801955281491139254988030713175578535185735860770240336938648365818694767212980092180930673365761656208904376468134321979033204597865736722163255659172526422009451446146296206099902326298009354790191881316609478116481577742891494048253908980080801321269044473352299515959976585174796879994158116507961851573953939949540037645148618752

set_option maxRecDepth 8192 in
private theorem sum0027_checked : Wide.sumRow hRows[27]! wideFirst = sum0027 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0027_checked : Wide.checkParity 1792 sum0027 haRows[27]! = true := by
  decide +kernel

private theorem row0027 :
    Wide.checkRows 1792 ((hRows.drop 27).take 1) wideFirst ((haRows.drop 27).take 1) = true :=
  row_checked hRows wideFirst haRows 27 sum0027
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0027_checked parity0027_checked

private def sum0028 : Nat := 26387242987402076860897009074091800813514896008193582461300996140141119992314547440979917645367013268689580715774192597765613825196575039949982673835245766620803305398702757952442292003541010842575954894239585283979747435495075003373395021549966316687631823044026044640166222757681984601362784778624360803268877142669220831934911586918886593722391913712229878243063236011641211729683567925300236079682312976142958592

set_option maxRecDepth 8192 in
private theorem sum0028_checked : Wide.sumRow hRows[28]! wideFirst = sum0028 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0028_checked : Wide.checkParity 1792 sum0028 haRows[28]! = true := by
  decide +kernel

private theorem row0028 :
    Wide.checkRows 1792 ((hRows.drop 28).take 1) wideFirst ((haRows.drop 28).take 1) = true :=
  row_checked hRows wideFirst haRows 28 sum0028
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0028_checked parity0028_checked

private def sum0029 : Nat := 12953744211667879574559702190010707651171625584905095574841686913755541732351702201085464556891975967691972983316275962328947759192690782519488857596207264634977115153700247127325882095494151916552764806786236311282787808673349518897412446087683526565098667226635266852240388338245798983271261546020971955682564383631854272512

set_option maxRecDepth 8192 in
private theorem sum0029_checked : Wide.sumRow hRows[29]! wideFirst = sum0029 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0029_checked : Wide.checkParity 1792 sum0029 haRows[29]! = true := by
  decide +kernel

private theorem row0029 :
    Wide.checkRows 1792 ((hRows.drop 29).take 1) wideFirst ((haRows.drop 29).take 1) = true :=
  row_checked hRows wideFirst haRows 29 sum0029
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0029_checked parity0029_checked

private def sum0030 : Nat := 35074662110434038747627587960280857993524015880330828824075798024790963850563322203657080886584969261653150406795438407791146311394881878043579356984563411010176497182516348414100702687622025207153355472201977051463301814667239493129065175127851770780794521740541562140924613430095116668851406948001785739171374944284362354004670687524163170875188483516002627469834063538275421541872199281960185223469042975936255502267234587484286974064671150332444672

set_option maxRecDepth 8192 in
private theorem sum0030_checked : Wide.sumRow hRows[30]! wideFirst = sum0030 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0030_checked : Wide.checkParity 1792 sum0030 haRows[30]! = true := by
  decide +kernel

private theorem row0030 :
    Wide.checkRows 1792 ((hRows.drop 30).take 1) wideFirst ((haRows.drop 30).take 1) = true :=
  row_checked hRows wideFirst haRows 30 sum0030
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0030_checked parity0030_checked

private def sum0031 : Nat := 40438332213938378681647749604523927988174577432926379805774761820206261354332266127116583971814151861950407256827974728385624973673504879155930107601834773471818257427763786535678505258211774609871121120214054687508653545602785711313607899099730375853071901757395136804733759949343646000958898073175361135802336611628587664251724954704994573977323265188373227481195608319044341692293931559384752583361203751847955274127904582040914923749873952593249413655909256944156672

set_option maxRecDepth 8192 in
private theorem sum0031_checked : Wide.sumRow hRows[31]! wideFirst = sum0031 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem parity0031_checked : Wide.checkParity 1792 sum0031 haRows[31]! = true := by
  decide +kernel

private theorem row0031 :
    Wide.checkRows 1792 ((hRows.drop 31).take 1) wideFirst ((haRows.drop 31).take 1) = true :=
  row_checked hRows wideFirst haRows 31 sum0031
    (by rw [h_length]; decide) (by rw [ha_length]; decide)
    sum0031_checked parity0031_checked

/-- The exact HA checker on rows [0, 32). -/
theorem block0000 :
    Wide.checkRows 1792 ((hRows.drop 0).take 32) wideFirst
      ((haRows.drop 0).take 32) = true :=
  (append_ranges hRows wideFirst haRows 0 16 16
    (append_ranges hRows wideFirst haRows 0 8 8
    (append_ranges hRows wideFirst haRows 0 4 4
    (append_ranges hRows wideFirst haRows 0 2 2
    (append_ranges hRows wideFirst haRows 0 1 1
    row0000 row0001) (append_ranges hRows wideFirst haRows 2 1 1
    row0002 row0003)) (append_ranges hRows wideFirst haRows 4 2 2
    (append_ranges hRows wideFirst haRows 4 1 1
    row0004 row0005) (append_ranges hRows wideFirst haRows 6 1 1
    row0006 row0007))) (append_ranges hRows wideFirst haRows 8 4 4
    (append_ranges hRows wideFirst haRows 8 2 2
    (append_ranges hRows wideFirst haRows 8 1 1
    row0008 row0009) (append_ranges hRows wideFirst haRows 10 1 1
    row0010 row0011)) (append_ranges hRows wideFirst haRows 12 2 2
    (append_ranges hRows wideFirst haRows 12 1 1
    row0012 row0013) (append_ranges hRows wideFirst haRows 14 1 1
    row0014 row0015)))) (append_ranges hRows wideFirst haRows 16 8 8
    (append_ranges hRows wideFirst haRows 16 4 4
    (append_ranges hRows wideFirst haRows 16 2 2
    (append_ranges hRows wideFirst haRows 16 1 1
    row0016 row0017) (append_ranges hRows wideFirst haRows 18 1 1
    row0018 row0019)) (append_ranges hRows wideFirst haRows 20 2 2
    (append_ranges hRows wideFirst haRows 20 1 1
    row0020 row0021) (append_ranges hRows wideFirst haRows 22 1 1
    row0022 row0023))) (append_ranges hRows wideFirst haRows 24 4 4
    (append_ranges hRows wideFirst haRows 24 2 2
    (append_ranges hRows wideFirst haRows 24 1 1
    row0024 row0025) (append_ranges hRows wideFirst haRows 26 1 1
    row0026 row0027)) (append_ranges hRows wideFirst haRows 28 2 2
    (append_ranges hRows wideFirst haRows 28 1 1
    row0028 row0029) (append_ranges hRows wideFirst haRows 30 1 1
    row0030 row0031)))))

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.HaBlocks
