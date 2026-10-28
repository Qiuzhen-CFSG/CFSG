module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.PackedGenerators
import Mathlib.Data.List.GetD

/-!
# Certified re-encoding of the degree-896 HS generators

The two shared packed generators decode to the literal HSG1-f4r896aB0
matrices, with coefficients 0, 1, omega, omega + 1 in that order.
The unchanged downloads, hashes and coefficient convention are recorded in
`../source/README.md` and `source/README.md`.

For a bounded kernel check, ten shifts and masks spread each bit plane into
the even positions. A symbolic routing function lists precisely the input
bits contributing to each output bit. Its semantics is proved by induction;
a single finite certificate checks the first 896 even and odd positions.
Fourteen bounded row checks are joined by a proved list-concatenation step
to certify both complete arrays. All
finite checks use `decide +kernel`; no external calculation is trusted.

The private encoding works in 1024 input bits. Only its first 896 entries
are used in the semantic theorem. The resulting matrix equalities have no
size, density, trace, or group-action premises.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates
namespace Reencoding

/-- Force the previous arithmetic state before it is used twice. -/
private def forceNat {α : Sort*} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)

private theorem forceNat_eq {α : Sort*} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

/-- Masks keep alternating blocks of widths 1, 2, ..., 512 in 2048 bits.
The last stage is applied first. These literals are only candidates: the
routing certificate below verifies all positions used by the matrices. -/
private def stages : List (ℕ × ℕ) := [
  (1, 10772335357103669100238292229556650653481367556571828010710115142508218379622630297732400470507637821229572653640632673164706519716830307031696050795482761040210292455766998697250065916796550702265352546128022522758930739547539918720612698112825390156860548617345435014295858630513688602869184133041310128507304777796556114140228324928854856498285392011775440686025935219777008730902820104716752864288059038908647867906153952452532783717433881968134565871077762410409041894903606736575052367242310441156559514193552232645015332422784332879405175055463145778514534045144409868215106159534984049397851951203686532076885),
  (2, 6463401214262201460142975337733990392088820533943096806426069085504931027773578178639440282304582692737743592184379603898823911830098184219017630477289656624126175473460199218350039550077930421359211527676813513655358443728523951232367618867695234094116329170407261008577515178308213161721510479824786077104382866677933668484136994957312913898971235207065264411615561131866205238541692062830051718572835423345188720743692371471519670230460329180880739522646657446245425136942164041945031420345386264693935708516131339587009199453670599727643105033277887467108720427086645920929063695720990429638711170722211919246131),
  (4, 1901000357135941605924404511098232468261417804100910825419432083972038537580464170188070671266053733158159880054229295264359974067675936535005185434496957830625345727488293887750011632375861888635062214022592209898634836390742338597755182019910362968857743873649194414287504464208297988741620729360231199148347901964098137789452057340386151146756245649136842474004576803490060364276968253773544623109657477454467270806968344550446961832488332112023746918425487484189830922630048247630891594219231254321745796622391570466767411604020764625777383833317025725620211890319601741449724616388526596952562109035944682131215),
  (8, 125747105335840495333520920967587361713790282761538848374048036682975311824388680518277048293863476512407462882964583733440153926655606696868047285550382424593894464464206210473736178017080358392202558904218161744267674002500465977283416709488234126344675664793915583824465275842572240500418491825384943134326514915913106390741964882437994433832125198581036272599524535639420335380188561533658593746553218353019235812134092830185207592032302124141648628845265709070922668033894242061187381718781833943461784212376096100914575864857404663961928113487896643328963432433592333092005130266945339098029400208603344732415),
  (16, 493110854499153261527303304830400414429163719268741078049504027152977022733232996524058187154171131783400490729235363527383303464462683996751272600003788441958449080173047226631524142856549004482903667216748822318336088295811827763886630366639854898310597766941366022901377479767781036797649456019102650190303406219229875374531714524414675213922763874381285717351691497311915806227145891849646132610039780837175085886117183535370834050266286920432789075075656304548989512561008593767263638886841499053506851741469043409601385435225185752143301114887612147878963061101869624862983024529730566675214853496666914815),
  (32, 7524389322797446040883062092537733229786709286255942365591042456667314442386984930096710212860769417795340657030827683038844698134727362301284631268392235937583875243951827485067390432889168540459798904583851961347493402961438138317409892571406969311454956545629852567160903318873644454808418626039175260691609949036049282500668357192980174976837821551246685093927923721588007749784843196246171229662840693970933302712516988312146012401244517765743466989949769396632294237631961231141629598705401114366081875798891955552658541527505604808849729680814712227957530391280469301474478369841928076546552539119615),
  (64, 1751908409537131537125538500170898456289982643253648994597171622084866540056922972656596711067189883143022427928261387198048309577447708096161081508699543188141910799902361070622401213741372869165576561922289064005031441460299875909588734720986560192536021217458484325625391881476254406473079046653046818198811063732807766626815778669059263539288279240724043002972198751108816706724514596508072044707863500473414019828271440565021291938453587422416281612723545945938909968678247193364858445334012215555435275427943811594957345986593699556195903066794743184472440265626440142038293478191736570249215),
  (128, 94971145180789141405469863695884969990413375523057264366393133656667101213790966126577778796192435976493286721619611273819053280153830754471864219391289063009512806159964370817305614238014244837688992683186106238684767551483551350234458097273324874897360483666819816039560925245068139788358907078031552764684530246952389718316880392918374272991258975094057996680343827463235688502168934277549034830891396697676020193061348779341148892066948388025097854535507810266613457395028123006836137017554784880056507653590091639305530513408919664906739868441072650790136656884348974268415),
  (256, 279095111627852376407822673918065072905887935345660252615989519488029661278602584477274180335287279405243496479269655964121202716886217624945655141584838007703178109579584255207605922065345056860944776274180728348556737279454388833698212982515973506422648097610271573739270676850754346538118912161587565627322601608861055814126836611515444383335727234678394072087732734025567668896419351136825388822676270715092663370710364205902957257037840983601227613820869153236869843656264309782139126643440567491781248474770930966086857614467652386815),
  (512, 2410312426921032588580116606028314112912093247945688951359675039065257391591803200669085024107346049663448766280888004787862416978794958324969612987890774471685899853150034451840262999015208137879147648906730546627516188125228793608498254413622185557461794521228420806236115696491848613995171671120355230896257999149258109674668529734341363050113939500588541302086847006769686052748707136868564708653190246324172185170594217116133658727496874721447108785121263615)]

private def spread : List (ℕ × ℕ) → ℕ → ℕ
  | [], x => x % 2 ^ 1024
  | (s, m) :: ss, x => forceNat (spread ss x) fun y => (y ||| y <<< s) &&& m

/-- Input bit positions whose disjunction forms an output bit. -/
private def route : List (ℕ × ℕ) → ℕ → List ℕ
  | [], i => if i < 1024 then [i] else []
  | (s, m) :: ss, i => if m.testBit i then
      route ss i ++ (if s ≤ i then route ss (i - s) else []) else []

private theorem testBit_spread (ss : List (ℕ × ℕ)) (x i : ℕ) :
    (spread ss x).testBit i = (route ss i).any x.testBit := by
  induction ss generalizing i with
  | nil =>
    simp only [spread, route, Nat.testBit_mod_two_pow]
    split <;> simp_all
  | cons sm ss ih =>
    rcases sm with ⟨s,m⟩
    simp only [spread, forceNat_eq, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, ih, route]
    split <;> simp_all
    split <;> simp_all

set_option maxRecDepth 4096 in
private theorem routes_correct : ∀ i : Fin 896,
    route stages (2 * i.val) = [i.val] ∧ route stages (2 * i.val + 1) = [] := by decide +kernel

private def encode (a : Packed.Row) : ℕ := spread stages a.1 ||| (spread stages a.2 <<< 1)

private theorem spread_even (x : ℕ) (i : Fin 896) :
    (spread stages x).testBit (2 * i.val) = x.testBit i.val := by
  rw [testBit_spread, (routes_correct i).1]
  simp

private theorem spread_odd (x : ℕ) (i : Fin 896) :
    (spread stages x).testBit (2 * i.val + 1) = false := by
  rw [testBit_spread, (routes_correct i).2]
  rfl

private theorem encode_even (a : Packed.Row) (i : Fin 896) :
    (encode a).testBit (2 * i.val) = a.1.testBit i.val := by
  rw [encode, Nat.testBit_or, spread_even, Nat.testBit_shiftLeft]
  by_cases hi : i.val = 0
  · simp [hi]
  · have hj : 2 * i.val - 1 = 2 * (i.val - 1) + 1 := by omega
    rw [hj, spread_odd _ ⟨i.val - 1, by omega⟩]
    simp

private theorem encode_odd (a : Packed.Row) (i : Fin 896) :
    (encode a).testBit (2 * i.val + 1) = a.2.testBit i.val := by
  rw [encode, Nat.testBit_or, spread_odd, Nat.testBit_shiftLeft]
  simp [spread_even _ i]

private theorem entry_encode (a : Packed.Row) (i : Fin 896) :
    entry (encode a) i.val = Packed.decode a i.val := by
  unfold entry Packed.decode Packed.Base.entry
  unfold Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit
  rw [encode_even, encode_odd]
  cases a.1.testBit i.val <;> cases a.2.testBit i.val <;> decide +kernel

private theorem encode_zero : encode (0, 0) = 0 := by decide +kernel

private theorem eval_eq_of_encode (a : Packed.Mat) (b : Array ℕ)
    (h : a.map encode = b.toList) :
    Packed.eval 896 a = fun i j : Fin 896 => entry (b.getD i.val 0) j.val := by
  funext i j
  change Packed.decode (a.getD i.val (0, 0)) j.val = _
  rw [← entry_encode _ j]
  have hi := congrArg (fun l : List ℕ => l.getD i.val 0) h
  rw [← encode_zero, List.getD_map] at hi
  have hi' : encode (a.getD i.val (0, 0)) = b.getD i.val 0 := by
    simpa only [encode_zero, List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getD_eq_getD_getElem?] using hi
  rw [hi']

private theorem join_block (a : Packed.Mat) (b : List ℕ) (k n : ℕ)
    (h : ((a.drop n).take k).map encode = (b.drop n).take k)
    (t : (a.drop (n + k)).map encode = b.drop (n + k)) :
    (a.drop n).map encode = b.drop n := by
  conv_lhs => rw [← List.take_append_drop k (a.drop n)]
  rw [List.map_append, h]
  have ht : ((a.drop n).drop k).map encode = (b.drop n).drop k := by
    simpa only [List.drop_drop, Nat.add_comm] using t
  rw [ht, List.take_append_drop]

set_option maxRecDepth 4096 in
private theorem rowsA_block0 : ((generatorRowsA.drop 0).take 128).map encode =
    (rowsA.toList.drop 0).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block1 : ((generatorRowsA.drop 128).take 128).map encode =
    (rowsA.toList.drop 128).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block2 : ((generatorRowsA.drop 256).take 128).map encode =
    (rowsA.toList.drop 256).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block3 : ((generatorRowsA.drop 384).take 128).map encode =
    (rowsA.toList.drop 384).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block4 : ((generatorRowsA.drop 512).take 128).map encode =
    (rowsA.toList.drop 512).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block5 : ((generatorRowsA.drop 640).take 128).map encode =
    (rowsA.toList.drop 640).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsA_block6 : ((generatorRowsA.drop 768).take 128).map encode =
    (rowsA.toList.drop 768).take 128 := by decide +kernel

private theorem rowsA_encode : generatorRowsA.map encode = rowsA.toList := by
  have h7 : (generatorRowsA.drop 896).map encode = rowsA.toList.drop 896 := by
    decide +kernel
  have h6 := join_block generatorRowsA rowsA.toList 128 768 rowsA_block6 h7
  have h5 := join_block generatorRowsA rowsA.toList 128 640 rowsA_block5 h6
  have h4 := join_block generatorRowsA rowsA.toList 128 512 rowsA_block4 h5
  have h3 := join_block generatorRowsA rowsA.toList 128 384 rowsA_block3 h4
  have h2 := join_block generatorRowsA rowsA.toList 128 256 rowsA_block2 h3
  have h1 := join_block generatorRowsA rowsA.toList 128 128 rowsA_block1 h2
  have h0 := join_block generatorRowsA rowsA.toList 128 0 rowsA_block0 h1
  simpa only [List.drop_zero] using h0

set_option maxRecDepth 4096 in
private theorem rowsB_block0 : ((generatorRowsB.drop 0).take 128).map encode =
    (rowsB.toList.drop 0).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block1 : ((generatorRowsB.drop 128).take 128).map encode =
    (rowsB.toList.drop 128).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block2 : ((generatorRowsB.drop 256).take 128).map encode =
    (rowsB.toList.drop 256).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block3 : ((generatorRowsB.drop 384).take 128).map encode =
    (rowsB.toList.drop 384).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block4 : ((generatorRowsB.drop 512).take 128).map encode =
    (rowsB.toList.drop 512).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block5 : ((generatorRowsB.drop 640).take 128).map encode =
    (rowsB.toList.drop 640).take 128 := by decide +kernel

set_option maxRecDepth 4096 in
private theorem rowsB_block6 : ((generatorRowsB.drop 768).take 128).map encode =
    (rowsB.toList.drop 768).take 128 := by decide +kernel

private theorem rowsB_encode : generatorRowsB.map encode = rowsB.toList := by
  have h7 : (generatorRowsB.drop 896).map encode = rowsB.toList.drop 896 := by
    decide +kernel
  have h6 := join_block generatorRowsB rowsB.toList 128 768 rowsB_block6 h7
  have h5 := join_block generatorRowsB rowsB.toList 128 640 rowsB_block5 h6
  have h4 := join_block generatorRowsB rowsB.toList 128 512 rowsB_block4 h5
  have h3 := join_block generatorRowsB rowsB.toList 128 384 rowsB_block3 h4
  have h2 := join_block generatorRowsB rowsB.toList 128 256 rowsB_block2 h3
  have h1 := join_block generatorRowsB rowsB.toList 128 128 rowsB_block1 h2
  have h0 := join_block generatorRowsB rowsB.toList 128 0 rowsB_block0 h1
  simpa only [List.drop_zero] using h0

end Reencoding

/-- The shared two-plane rows decode to the literal ATLAS generator a. -/
theorem generatorRowsA_eval : Packed.eval 896 generatorRowsA = matrixA :=
  Reencoding.eval_eq_of_encode generatorRowsA rowsA Reencoding.rowsA_encode

/-- The shared two-plane rows decode to the literal ATLAS generator b. -/
theorem generatorRowsB_eval : Packed.eval 896 generatorRowsB = matrixB :=
  Reencoding.eval_eq_of_encode generatorRowsB rowsB Reencoding.rowsB_encode

end Representation.HigmanSims.LargeModels.TracePair.Certificates
