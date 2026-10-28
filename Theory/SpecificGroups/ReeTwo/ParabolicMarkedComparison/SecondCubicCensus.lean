module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCoordinates
public import Theory.SpecificGroups.ReeTwo.CollectedBitVectors

/-!
# Census of images under cubic-centralizing automorphisms

The three-element cubic orbit generates the native second core. Its first
point has order four, its product with the next point has order eight, and
two length-five word identities hold. Every commuting automorphism preserves
these conditions. A bit-parallel kernel certificate checks all 2,048 core
elements and finds exactly 48 possible images. Evaluation of the packed
arithmetic is proved equal to the actual native cubic and group operations.

Source: the finite second-endpoint calculation for the binary Ree branch of
Aschbacher–Smith F.1.12, as used in J.4.5. This module establishes the upper
bound, not yet the full extension classification.
-/

@[expose] public section
namespace ReeTwo.SylowModel.CollectedBitVectors
variable {n:ℕ}

def product (x y:PackedElement n):PackedElement n :=
  ⟨productCore x y,x.t₀^^^y.t₀,x.t₁^^^y.t₁^^^(x.t₀&&&y.t₀)⟩

theorem read_product (x y:PackedElement n) (k:Fin n) :
    read (product x y) k=read x k*read y k := by
  apply SemidirectProduct.ext
  · exact (get_productCore x y k).trans
      (congrArg SemidirectProduct.left (collectedMul_eq ..))
  · change Multiplicative.ofAdd
      (((x.t₀^^^y.t₀).getLsbD k.val).toNat+
        2*(((x.t₁^^^y.t₁)^^^(x.t₀&&&y.t₀)).getLsbD k.val).toNat:ZMod 4)=_
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and]
    exact (by decide +kernel : ∀a b c d:Bool,
      (Multiplicative.ofAdd ((a^^c).toNat+2*((b^^d)^^(a&&c)).toNat:ZMod 4))=
        Multiplicative.ofAdd (a.toNat+2*b.toNat:ZMod 4)*
        Multiplicative.ofAdd (c.toNat+2*d.toNat:ZMod 4)) _ _ _ _

def choose (b:BitVec n) (x y:PackedElement n):PackedElement n :=
  ⟨select b x.core y.core,x.t₀^^^(b&&&(x.t₀^^^y.t₀)),
    x.t₁^^^(b&&&(x.t₁^^^y.t₁))⟩

theorem read_choose (b:BitVec n) (x y:PackedElement n) (k:Fin n) :
    read (choose b x y) k=if b.getLsbD k.val then read y k else read x k := by
  simp only [choose,read,get_select,BitVec.getLsbD_xor,BitVec.getLsbD_and,bool_select]
  cases b.getLsbD k.val <;> rfl

def equal (x y:PackedElement n):BitVec n :=
  eqMask x.core y.core &&& ~~~(x.t₀^^^y.t₀) &&& ~~~(x.t₁^^^y.t₁)

theorem equal_spec (x y:PackedElement n) (k:Fin n) :
    (equal x y).getLsbD k.val=true ↔ read x k=read y k := by
  have hr : ∀a b c d:Bool,
      (Multiplicative.ofAdd (a.toNat+2*b.toNat:ZMod 4)=
        Multiplicative.ofAdd (c.toNat+2*d.toNat:ZMod 4)) ↔ a=c ∧ b=d := by decide +kernel
  simp only [equal,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,k.isLt,
    decide_true,Bool.true_and,Bool.and_eq_true,Bool.not_eq_true',
    eqMask_spec]
  change (get x.core k=get y.core k ∧ _ ) ∧ _ ↔ _
  rw [SemidirectProduct.ext_iff]
  simp only [read,hr,and_assoc,show ∀a b:Bool,(a^^b)=false↔a=b from by decide]

open CubicAction
private theorem eval_replicate {H:Type*} [Group H] {m:ℕ}
    (f:Fin m→H) (k:ℕ) (i:Fin m) : Theory.GroupTheory.evalWord f (List.replicate k i)=f i^k := by
  induction k with
  | zero => simp [Theory.GroupTheory.evalWord]
  | succ k ih => simp only [List.replicate_succ,Theory.GroupTheory.evalWord,ih,pow_succ']
private theorem eval_append {H:Type*} [Group H] {m:ℕ}
    (f:Fin m→H) (u v:List (Fin m)) :
    Theory.GroupTheory.evalWord f (u++v)=Theory.GroupTheory.evalWord f u*Theory.GroupTheory.evalWord f v := by
  induction u with
  | nil => simp [Theory.GroupTheory.evalWord]
  | cons i u ih => simp only [List.cons_append,Theory.GroupTheory.evalWord,ih,mul_assoc]

private theorem cubic_formula (a:A) : (cubic a:SylowModel)=
    (cubicImage 1:SylowModel)^a.val.left.b1.val *
    (cubicImage 2:SylowModel)^a.val.left.b2.val *
    (cubicImage 3:SylowModel)^a.val.left.b3.val *
    (cubicImage 4:SylowModel)^a.val.left.b4.val *
    (cubicImage 5:SylowModel)^a.val.left.b5.val *
    (cubicImage 6:SylowModel)^a.val.left.b6.val *
    (cubicImage 7:SylowModel)^a.val.left.b7.val *
    (cubicImage 8:SylowModel)^a.val.left.b8.val *
    (cubicImage 9:SylowModel)^a.val.left.b9.val *
    (cubicImage 0:SylowModel)^a.val.right⁻¹.toAdd.val := by
  rw [←cubicEval_eq,cubicEval,Collected.collectedEval_eq,normalWord]
  simp only [eval_append,eval_replicate]

def rootImage (i:Fin 10):SylowModel:=cubicImage i
def chosenImage (b:BitVec n) (i:Fin 10):PackedElement n:=
  choose b (pack 1) (pack (rootImage i))
def chosenInverse (b:BitVec n) (k:ℕ):PackedElement n:=
  choose b (pack 1) (pack ((rootImage 0)⁻¹^k))

def cubicPacked (x:PackedElement n):PackedElement n :=
  product (product (product (product (product (product (product (product (product (product
    (chosenImage x.core.b1 1) (chosenImage x.core.b2 2))
    (chosenImage x.core.b3 3)) (chosenImage x.core.b4 4))
    (chosenImage x.core.b5 5)) (chosenImage x.core.b6 6))
    (chosenImage x.core.b7 7)) (chosenImage x.core.b8 8))
    (chosenImage x.core.b9 9)) (chosenInverse x.t₀ 1)) (chosenInverse x.t₁ 2)

private theorem read_chosen (b:BitVec n) (i:Fin 10) (k:Fin n) :
    read (chosenImage b i) k=rootImage i^(zbit (b.getLsbD k.val)).val := by
  simp only [chosenImage,read_choose,read_pack]
  cases b.getLsbD k.val <;> norm_num [zbit]
  change rootImage i=rootImage i^1
  rw [pow_one]

private theorem read_inverse (x:PackedElement n) (k:Fin n) :
    read (chosenInverse x.t₀ 1) k * read (chosenInverse x.t₁ 2) k=
      rootImage 0^(read x k).right⁻¹.toAdd.val := by
  simp only [chosenInverse,read_choose,read_pack]
  change (if x.t₀.getLsbD k.val then (rootImage 0)⁻¹^1 else 1)*
    (if x.t₁.getLsbD k.val then (rootImage 0)⁻¹^2 else 1)=
    rootImage 0^(Multiplicative.ofAdd ((x.t₀.getLsbD k.val).toNat+
      2*(x.t₁.getLsbD k.val).toNat:ZMod 4))⁻¹.toAdd.val
  have hfour:rootImage 0^4=1:=by decide +kernel
  have hinv:(rootImage 0)⁻¹=rootImage 0^3:=by
    apply inv_eq_of_mul_eq_one_left
    simpa only [←pow_succ] using hfour
  cases x.t₀.getLsbD k.val <;> cases x.t₁.getLsbD k.val
  all_goals simp only [Bool.false_eq_true,if_false,if_true,one_mul,mul_one,pow_one]
  · rfl
  · change (rootImage 0)⁻¹^2=rootImage 0^2
    rw [hinv,←pow_mul]
    calc
      _ = rootImage 0^4*rootImage 0^2 := by rw [←pow_add]
      _ = _ := by rw [hfour,one_mul]
  · exact hinv
  · change (rootImage 0)⁻¹*(rootImage 0)⁻¹^2=rootImage 0
    rw [←pow_succ',hinv,←pow_mul]
    calc
      _ = (rootImage 0^4)^2*rootImage 0 := by rw [←pow_mul,←pow_succ]
      _ = _ := by rw [hfour,one_pow,one_mul]

theorem read_cubicPacked (x:PackedElement n) (k:Fin n) (a:A)
    (ha:read x k=(a:SylowModel)) : read (cubicPacked x) k=(cubic a:SylowModel) := by
  rw [cubic_formula]
  simp only [cubicPacked,read_product,read_chosen]
  rw [mul_assoc,read_inverse]
  have hc:=congrArg SemidirectProduct.left ha
  have ht:=congrArg SemidirectProduct.right ha
  change get x.core k=a.val.left at hc
  rw [←hc,←ht]
  rfl

def power (x:PackedElement n):ℕ→PackedElement n
  | 0=>pack 1
  | m+1=>product x (power x m)
theorem read_power (x:PackedElement n) (m:ℕ) (k:Fin n):
    read (power x m) k=read x k^m := by
  induction m with
  | zero => simp [power,read_pack]
  | succ m ih => rw [power,read_product,ih,pow_succ']

def word (x y z:PackedElement n):List (Fin 3)→PackedElement n
  | []=>pack 1
  | i::is=>product (![x,y,z] i) (word x y z is)
private theorem read_word (x y z:PackedElement n) (w:List (Fin 3)) (k:Fin n):
    read (word x y z w) k=Theory.GroupTheory.evalWord
      (![read x k,read y k,read z k]) w := by
  induction w with
  | nil => exact read_pack 1 k
  | cons i w ih =>
    rw [word,read_product,ih]
    fin_cases i <;> rfl

/-- Necessary order and word identities for a cubic-centralizing image. -/
def profileMask (x:PackedElement n):BitVec n :=
  let y:=cubicPacked x
  let z:=cubicPacked y
  equal (power x 4) (pack 1) &&& ~~~(equal (power x 2) (pack 1)) &&&
  equal (power (product x y) 8) (pack 1) &&& ~~~(equal (power (product x y) 4) (pack 1)) &&&
  equal (word x y z [1,0,2,0,1]) (word x y z [0,0,1,1,2]) &&&
  equal (word x y z [1,1,0,0,2]) (word x y z [0,1,2,1,0])

def Profile (a:A):Prop :=
  a^4=1 ∧ a^2≠1 ∧ (a*cubic a)^8=1 ∧ (a*cubic a)^4≠1 ∧
  Theory.GroupTheory.evalWord (![a,cubic a,cubic (cubic a)]) [1,0,2,0,1]=
    Theory.GroupTheory.evalWord (![a,cubic a,cubic (cubic a)]) [0,0,1,1,2] ∧
  Theory.GroupTheory.evalWord (![a,cubic a,cubic (cubic a)]) [1,1,0,0,2]=
    Theory.GroupTheory.evalWord (![a,cubic a,cubic (cubic a)]) [0,1,2,1,0]

theorem profileMask_spec (x:PackedElement n) (k:Fin n) (a:A)
    (ha:read x k=(a:SylowModel)) : (profileMask x).getLsbD k.val=true ↔ Profile a := by
  have hy:=read_cubicPacked x k a ha
  have hz:=read_cubicPacked (cubicPacked x) k (cubic a) hy
  simp only [profileMask,BitVec.getLsbD_and,BitVec.getLsbD_not,k.isLt,decide_true,
    Bool.true_and,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equal_spec,read_power,read_pack,read_product,
    read_word,ha,hy,hz]
  simp only [Profile,Theory.GroupTheory.evalWord,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Fin.isValue,Matrix.tail_cons,Matrix.head_cons,mul_one]
  have hcoe (b:A) : (b:SylowModel)=1 ↔ b=1 :=
    ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  simp only [←Subgroup.coe_pow,←Subgroup.coe_mul,hcoe,Subtype.coe_inj,and_assoc]

def coreEnumeration : PackedElement 2048 :=
  ⟨⟨0,
    21544670714207338200476584459113301306962735113143656021420230285016436759245260595464800941015275642459145307281265346329413039433660614063392101590965522080420584911533997394500131833593101404530705092256045045517861479095079837441225396225650780313721097234690870028591717261027377205738368266082620257014609555593112228280456649857709712996570784023550881372051870439554017461805640209433505728576118077817295735812307904905065567434867763936269131742155524820818083789807213473150104734484620882313119028387104465290030664845568665758810350110926291557029068090288819736430212319069968098795703902407373064153770,
    25853604857048805840571901350935961568355282135772387225704276342019724111094312714557761129218330770950974368737518415595295647320392736876070521909158626496504701893840796873400158200311721685436846110707254054621433774914095804929470475470780936376465316681629044034310060713232852646886041919299144308417531466711734673936547979829251655595884940828261057646462244527464820954166768251320206874291341693380754882974769485886078680921841316723522958090586629784981700547768656167780125681381545058775742834064525358348036797814682398910572420133111549868434881708346583683716254782883961718554844682888847676984524,
    30416005714175065694790472177571719492182684865614573206710913343552616601287426723009130740256859730530558080867668724229759585082814984560082966951951325290005531639812702204000186118013790218160995424361475358378157382251877417564082912318565807501723901978387110628600071427332767819865931669763699186373566431425570204631232917446178418348099930386189479584073228855840965828431492060376713969754519639271476332911493512807151389319813313792379950694807799747037294762080771962094265507507700069147932745958265127468278585664332234012438141333072411609923390245113627863195593862216425551240993744575114914099440,
    32191258965975166805381355767702364598730312386953945183756297390841679827043502212678924363229049987176310498038933435760679405223835314398220105100897900696036982902836789881276461572372571748403855079479849406532524544640119290184554677628987936344236970187242389459063110615698493568107133907298545442387587818473755236029943009904126575061024050836745285785478281123691605857328271752616599999117623898372924367906327764527413143560269343780262048984388021522156203016676925967663969720008149489526216758368280601834131421403495593974253597052901540692214638702999637271553313348338006809095526453402456251498240,
    32316512960456508147453349385365121560029673505996215291052295923497502161845157660200677353335759292556934560431168784130592175847026458411091401113848279332188918918220823044523566226246795557791574734716850819454473882554323944334074207708109530615683335254269363676864674514061298027570754749667911282871724029983449112545310443072040154819642253271451940772360453967833714276902233168258408946731567076945106428632575740174062980318251379617483264824158211574922576695198259201131389838088044481970625035728915228891636395882917773452463381865274549723395723172372127735020455495580422417626880638757562929315840,
    32317006063786617977917430647786889867906369439928774745874403061933612682200576450810216481426203250827948543126557362463291876111646222960360790085163651852238641429717120847798370265322261673906889097924268663692940257295126353200399956021066277899174676540581348497257723324380162489733907944315511759482739072698058393384635692285896212301876001058488500506831120565403102471120452564365415396618005887063102909747528554645081362840155633503159179847489820241277356288078525972093195870585301724764277428214574822136154041715694457110709920357539707654728889907475699213364849177130473778351627777064507057111040,
    32317006071311007298962968279132820423318564169544585575840362784271006144270719271112334871465990491032121249854708136351097131222229533897039842809000575024469795858601452903608286950487291036173656424642694699111215656720330692156806652878176294560992911131049744850351554674082581482982160517647675979048835286736621524221873911053756802868040397366267058518789526418606983189736261563041441886139662520217871559010598356884184331324030205339382405674779699808810844071987274263786247133048684130104820097246644482379610721840409187043258179179795737779347699068638486420172878212978512006155262375419323025981440,
    32317006071311007300714876688669951960349131524534694890724875563828770168877477517674144147156520330032050859708107053367541780354298485118594865664828671846811824087147165337278333530998363043786544832224103197459486604404605511324149101655290064231896878300552753692653117794267740933710191915457110569482353408144600202632326067708533016730171645788373932339760925266412651919717201339056200596183833289262707915216292923080049316321410249206727677420171938451885976792643871821700059247191423513203065085185628574928209860250798213758159017512799345696238071622024309939738578610163879497403419196726710621962240,
    32317006071311007300714876688669951960444102669715484032130345427524655138867611798085573559146505641014799895848992131558773898897874931575600122725169680536153603186965708812344954253910382450831936435667181350651846563501034918154134916228896586215374039929970959986026631115266885080258995661844475996688216120407152368914262326688954297921116905358475567711539686747169438627081137712541397537050050280114428159335126130122919957080213913170378129944336867880090300295888143939010064438356220959263775585323618856951444769654532129484978655322733173025761463008789789037153537230130181217227468995996591943843840⟩,
    32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448280710318450446268407511633591722075539194702809692695116208601753153385228164358637425253452063124531982403270024154882788029124087013649227429510942494747442647489815192386233134523565554286718296887677415327531178143142900963914851815895844970678619654931422375297655621241901859303687650732732577258002390973227976426601145541195422760363881209530177954039354611088039227582300249931078656601680784145297277963248059010428202344946224651318834406502274474967040,
    32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521734564076182110829912044267485667021494378337432091400804375578173293516902959351017550115541769580704823489838590463999939561383487229281910850182593813106849357791285954724448854882125685229350225459628571692166207846586010535756741612055848610098380251624748643306405371232666472431888720497281435372093440⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem profile_count_check : (profileMask coreEnumeration).cpopNatRec 2048 0=48 := by
  decide +kernel

theorem coreEnumeration_mem (k:Fin 2048):read coreEnumeration k∈firstParabolicCore := by
  rw [mem_firstParabolicCore_iff]
  change zbit ((0:BitVec 2048).getLsbD k.val)=0
  simp [zbit]
def coreElement (k:Fin 2048):A:=⟨read coreEnumeration k,coreEnumeration_mem k⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem coreElement_code : ∀k:Fin 2048,Collected.code (coreElement k)=2*k.val := by
  decide +kernel


noncomputable def coreEnumerationEquiv : Fin 2048 ≃ A :=
  Equiv.ofBijective coreElement ((Nat.bijective_iff_injective_and_card coreElement).mpr ⟨by
    intro i j h
    have hh:=congrArg (fun a:A=>Collected.code (a:SylowModel)) h
    rw [coreElement_code,coreElement_code] at hh
    exact Fin.ext (by omega),by rw [Nat.card_fin,firstParabolicCore_card]⟩)

/-- Exactly forty-eight elements satisfy the necessary image profile. -/
theorem profile_card : Nat.card {a:A // Profile a}=48 := by
  let e : {k:Fin 2048 // (profileMask coreEnumeration).getLsbD k.val=true} ≃ {a:A // Profile a} :=
    Equiv.subtypeEquiv coreEnumerationEquiv (fun k=>profileMask_spec coreEnumeration k (coreElement k) rfl)
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype,pop_card,profile_count_check]

private theorem seed_profile : Profile (orbit 0) := by
  have h1:cubic (orbit 0)=orbit 1 := by
    change cubic ((generator 0)⁻¹)=(generator 1)⁻¹
    rw [map_inv,cubic_generator_zero]
  have h2:cubic (orbit 1)=orbit 2 := by
    change cubic ((generator 1)⁻¹)=(cubicImage 1)⁻¹
    rw [map_inv,cubic_generator]
  rw [Profile,h1,h2]
  decide +kernel

private theorem profile_of_commuting (α:MulAut A) (hc:Commute α cubic) : Profile (α (orbit 0)) := by
  have h:=seed_profile
  have hcomm (a:A):α (cubic a)=cubic (α a):=DFunLike.congr_fun hc.eq a
  have hword (w:List (Fin 3)) :
      α (Theory.GroupTheory.evalWord (![orbit 0,cubic (orbit 0),cubic (cubic (orbit 0))]) w)=
      Theory.GroupTheory.evalWord (![α (orbit 0),cubic (α (orbit 0)),cubic (cubic (α (orbit 0)))]) w := by
    induction w with
    | nil => exact map_one α
    | cons i w ih =>
      simp only [Theory.GroupTheory.evalWord,map_mul,ih]
      congr 1
      fin_cases i
      · rfl
      · exact hcomm _
      · exact (hcomm _).trans (congrArg cubic (hcomm _))
  rcases h with ⟨h4,h2,h8,hq,hA,hB⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [map_pow,map_one] using congrArg α h4
  · intro hh
    exact h2 (α.injective (by simpa only [map_pow,map_one] using hh))
  · simpa only [map_pow,map_mul,map_one,hcomm] using congrArg α h8
  · intro hh
    apply hq
    apply α.injective
    simpa only [map_pow,map_mul,map_one,hcomm] using hh
  · simpa only [hword] using congrArg α hA
  · simpa only [hword] using congrArg α hB

/-- Cubic-centralizing automorphisms have at most forty-eight possibilities. -/
theorem cubic_commuting_aut_card_le : Nat.card {α:MulAut A // Commute α cubic}≤48 := by
  let f : {α:MulAut A // Commute α cubic}→{a:A // Profile a} :=
    fun α=>⟨α.val (orbit 0),profile_of_commuting α.val α.property⟩
  have hf:Function.Injective f := by
    intro α β h
    apply Subtype.ext
    exact commuting_aut_ext α.val β.val α.property β.property (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective f hf).trans_eq profile_card

end ReeTwo.SylowModel.CollectedBitVectors

noncomputable section
namespace ReeTwo.SylowModel.CubicAction


theorem cubic_centralizer_card_le (γ:MulAut A) (hγ:orderOf γ=3) :
    Nat.card {α:MulAut A // Commute α γ}≤48 := by
  obtain ⟨c,hc⟩:=firstParabolic_cubic_conjugacy γ cubic hγ cubic_order
  have hcomm (α:MulAut A) (hα:Commute α γ) : Commute (MulAut.conj c α) cubic := by
    have hh:=hα.map (MulAut.conj c).toMonoidHom
    change Commute (MulAut.conj c α) (c*γ*c⁻¹) at hh
    rcases hc with hc|hc
    · rwa [hc] at hh
    · rw [hc] at hh
      simpa only [inv_inv] using hh.inv_right
  let f : {α:MulAut A // Commute α γ}→{α:MulAut A // Commute α cubic} :=
    fun α=>⟨MulAut.conj c α.val,hcomm α.val α.property⟩
  have hf:Function.Injective f := by
    intro α β h
    exact Subtype.ext ((MulAut.conj c).injective (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans CollectedBitVectors.cubic_commuting_aut_card_le


end ReeTwo.SylowModel.CubicAction

namespace ReeTwo.SylowModel.CollectedBitVectors
open CubicAction

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem fixed_count_check :
    (equal (cubicPacked coreEnumeration) coreEnumeration).cpopNatRec 2048 0=8 := by decide +kernel

/-- The literal native cubic fixes exactly eight elements of the core. -/
theorem cubic_fixed_card : Nat.card {a:A // cubic a=a}=8 := by
  let e : {k:Fin 2048 // (equal (cubicPacked coreEnumeration) coreEnumeration).getLsbD k.val=true} ≃
      {a:A // cubic a=a} := Equiv.subtypeEquiv coreEnumerationEquiv (fun k=>by
        rw [equal_spec,read_cubicPacked coreEnumeration k (coreElement k) rfl]
        change (cubic (coreElement k):SylowModel)=(coreElement k:SylowModel) ↔
          cubic (coreElement k)=coreElement k
        exact Subtype.ext_iff.symm)
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype,pop_card,fixed_count_check]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem fixed_seed_commuting_count_check :
    ((equal (cubicPacked coreEnumeration) coreEnumeration) &&&
      equal (product coreEnumeration (pack (orbit 0))) (product (pack (orbit 0)) coreEnumeration)).cpopNatRec 2048 0=1 :=
  by decide +kernel

private theorem fixed_seed_commuting_card :
    Nat.card {a:A // cubic a=a ∧ a*orbit 0=orbit 0*a}=1 := by
  let mask := (equal (cubicPacked coreEnumeration) coreEnumeration) &&&
    equal (product coreEnumeration (pack (orbit 0))) (product (pack (orbit 0)) coreEnumeration)
  let e : {k:Fin 2048 // mask.getLsbD k.val=true} ≃
      {a:A // cubic a=a ∧ a*orbit 0=orbit 0*a} := Equiv.subtypeEquiv coreEnumerationEquiv (fun k=>by
        simp only [mask,BitVec.getLsbD_and,Bool.and_eq_true,equal_spec,read_product,read_pack]
        rw [read_cubicPacked coreEnumeration k (coreElement k) rfl]
        change (↑(cubic (coreElement k)):SylowModel)=↑(coreElement k) ∧
          (coreElement k:SylowModel)*(orbit 0:SylowModel)=(orbit 0:SylowModel)*(coreElement k:SylowModel) ↔ _
        simp only [←Subgroup.coe_mul,Subtype.coe_inj]
        rfl)
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype,pop_card]
  exact fixed_seed_commuting_count_check

/-- A cubic-fixed element centralizing the orbit generator is trivial. -/
theorem cubic_fixed_eq_one_of_commute (a:A) (ha:cubic a=a) (hc:Commute a (orbit 0)) : a=1 := by
  let T:Type:={a:A // cubic a=a ∧ a*orbit 0=orbit 0*a}
  have hsub:Subsingleton T:=(Nat.card_eq_one_iff_unique.mp fixed_seed_commuting_card).1
  let h1:T:=⟨1,by simp⟩
  exact congrArg Subtype.val (hsub.elim (⟨a,ha,hc.eq⟩:T) h1)

end ReeTwo.SylowModel.CollectedBitVectors

namespace ReeTwo.SylowModel.CollectedBitVectors
/-- The packed coordinates enumerate the actual second core without repetition. -/
theorem read_coreEnumeration (k:Fin 2048) :
    read coreEnumeration k=(coreEnumerationEquiv k:SylowModel) := rfl
end ReeTwo.SylowModel.CollectedBitVectors
