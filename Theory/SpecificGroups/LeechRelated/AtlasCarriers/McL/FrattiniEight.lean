module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elements
public import Theory.GroupTheory.BinaryCollection.Subsequence
public import Theory.GroupTheory.SylowFrattiniBounds
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Source

/-!
# Three Frattini generators for the actual McL Sylow subgroup

Three words in the original degree-275 ATLAS generators give a subgroup of
order 128. Seven binary generators, their squares and triangular conjugation
relations give its normal forms. Evaluation at two letters separates all 128
forms. Four square words have sixteen distinct binary products, separated at
one letter. In a Sylow subgroup containing the word subgroup these products
lie in the Frattini subgroup. The proved McL order bounds that Sylow subgroup
by 128, so its Frattini quotient has order at most eight.

GAP discovers the words and relations; Lean's kernel checks every identity
and separation. The tables preserve the inverse-permutation convention of
ATLAS McLG1-p275B0, documented in the imported carrier module. No external
computation is a proof premise. The order uses the existing proved comparison
with the Leech model. The application excludes the original GL₄(2) outer
section in Aschbacher–Smith 4.4.10–11 and 12.1.9, printed pp.621 and 793.
-/

public section
namespace Sporadic.LeechRelated.McL.FrattiniEight
open Sporadic.LeechRelated.McL.ThreeRank
open Subgroup Theory.GroupTheory
private def packed (n : Nat) (i : Fin 275) : Fin 275 :=
  ⟨(n >>> (9 * i.val)) % 512 % 275, Nat.mod_lt _ (by decide)⟩

private def x0Word : Carrier := evalWord ![a,b,a⁻¹,b⁻¹] [2,1,2,3,3,2,3,2,3,3,2,3,2,3,2,1,2,3,2,1,2,1,2,1,1,2,1,2,1,1,2,3,2,3,3,2,1,1,2,1,1,2,1,1,2,3,2,1,1,0,3,2,1,2,3,3,2,1,1,2,3,2,1,0,1,1,0,1]
private def x0Table : Equiv.Perm (Fin 275) :=
  tablePerm (packed 4508225353106087227415463755772568487390731112269136472455485315084934189516375116140538616678223539186825543039534103864546323105992055939732555106674750429209325154587180137784820661292546771737469053262679454822124156210559342111670022764907633589931016398640874508500383928165619485224377777351505007088405184300371602288776353654196136486852445853357516973538518892600589859027044456766004950439025851088944670010542441067078661223603016709722891468398451881374377936271622910020034916276305491767482630110025011457442820237197729341453503909173972749439609833595900781824737867958454367902435874602337417817317744861517931660878338937440534155760401800548178806314284798301370594354300151273771304554386721994576222232682095206197406990848)
    (packed 1362771207013809777636779922107951547880250934082628835798898312482504089725080533307463054816070238001260316801714493554193496103181388069095009317977638687156078904028282408010887899985794015809766557214111681854963336557854396804468858437482036070883811973799669423725625311511264890738060760776969780952236977417568116989267418046895862391301447166848744027781217805955553484318569419724052244003366286592750569949319605704356115296611449119800543330173833975195561104320366063764999444973708097569047286113322295862913442103050619745036179819488936839021017594891998173343986315118157067648998499861475020070935385325492708733947294765663675254875084282880384514854208380670545151235990558209059979318587197272899957802324789309733496685056)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem x0Table_eq_word : x0Table = x0Word.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def x0 : Carrier := ⟨x0Table,x0Table_eq_word.symm ▸ x0Word.property⟩

private def x1Word : Carrier := evalWord ![a,b,a⁻¹,b⁻¹] [3,2,3,3,2,3,3,2,1,1,2,3,3,2,1,1,2,3,3,2,3,2,1,2,3,2,2,1,2,1,2,1,1,2,3,3,2,3,3,2,1,2,3,3,2,3,2,1,2,3,2,1,2,1,1,0,3,0,0,3,3,0,1,0,1,1,0,1,0,1,0,3,0,3,3,2,3,3,2,1,1,2,1,1,2,3,3,2,1,2,3,3,2,1,2,3,3,2,1,1,2,3,3,2,3,2,1,1,2,3,2,1,1,2,3]
private def x1Table : Equiv.Perm (Fin 275) :=
  tablePerm (packed 4989170036413348035933770037778319373798884554604341776839198538000996827108345452058123272572146046288180796607600508064321483292240654018550133609957820901566626783818197682991267452516915403948216761902093965320500878447845502202575109550156943287461397623673451650516764572770159922796216009067722454258703709058367250959478579887560730763209800544347670057706341721137942412197177031126508690002835981746131206244441659044172523327771155945471366512848971102311020037172056712995036761972029342115234522179084481144641341084565966334451236888957579099594366907573089934163865970543787084783470607840514466338082318187113901241980097552950197487482352914783940718587209544381820631066335633928340592489294505169489682744578807733045293744640)
    (packed 4989170036413348035933770037778319373798884554604341776839198538000996827108345452058123272572146046288180796607600508064321483292240654018550133609957820901566626783818197682991267452516915403948216761902093965320500878447845502202575109550156943287461397623673451650516764572770159922796216009067722454258703709058367250959478579887560730763209800544347670057706341721137942412197177031126508690002835981746131206244441659044172523327771155945471366512848971102311020037172056712995036761972029342115234522179084481144641341084565966334451236888957579099594366907573089934163865970543787084783470607840514466338082318187113901241980097552950197487482352914783940718587209544381820631066335633928340592489294505169489682744578807733045293744640)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem x1Table_eq_word : x1Table = x1Word.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def x1 : Carrier := ⟨x1Table,x1Table_eq_word.symm ▸ x1Word.property⟩

private def x2Word : Carrier := evalWord ![a,b,a⁻¹,b⁻¹] [2,3,3,2,1,2,1,2,3,2,3,2,3,3,2,3,3,2,1,2,1,0,1,0,1,1,0,1,0,1,1,0,1,1,2,1,0,1,0,3,0,3,3,2,1,2,3,0,3,0,1,0,3,0,3,0,1,1,0,1,0,3,3,3,2,1,2,1,1,2,1,2,1,1,2,1,1,2,3,2,1,2,3,2,3]
private def x2Table : Equiv.Perm (Fin 275) :=
  tablePerm (packed 1670544561050541372070540934091783395576980730888434054172534258589472055729678405887780566371735586488436845790924743127268819651912658380886933246804137332094678960942400261671029521933982110779563427658934421732011643483037632336070164731481069182214201354521777898698161386788053468716158016502476599093948918423232745561941374016296381834378598305767687278117858561565212783093263723478475457680182107811838509382090892785582835679671456759760881576746034099255742145370823549603168199200117994048529619220659513678786363383955886560048344343601447827128141735507406861958901452001450533420759724154224122368264041583227241417509899424304815700379700473170198758281782859780128198740590951145283324933674505611491267027859777378127096713728)
    (packed 5276037829221940610745470958205386987268909240500836115108270572332661582121610600119893176021434975171462187553828969391104443992937672058795094433626195542552147522020213504536391232523685096690543377855793785942818405659023817211209669703463762979360313598707175710413174407672279358341541970951534345168672433745736579657254466341207001958224744226091054056672418656768457137953492151965058589283678223577091528811209260403915131196352420339021773538846250926537138359225349042043411860398094083915646224929768546321111827004370481158686347419881081515431442845655172615585085817725402165736884661439361348327429406421148459322982578184360055028360336152357104836120281099274168376761979537941001982590457669239949499825220914063791132362752)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem x2Table_eq_word : x2Table = x2Word.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def x2 : Carrier := ⟨x2Table,x2Table_eq_word.symm ▸ x2Word.property⟩

private def gen : Fin 7 → Carrier := ![x0,x1,x2,x0 * x0 * x0 * x2 * x0 * x2,x2 * x0 * x0 * x2,x0 * x0,x0 * x0 * x1 * x2 * x1 * x2]
private def sqRel : Fin 7 → List (Fin 7) := ![[5],[],[4,6],[4,6],[],[],[]]
private def conjRel : Fin 7 → Fin 7 → List (Fin 7) := ![![[],[1,5],[2,3],[3,4,5],[6],[5],[4]],![[],[],[2,4,5],[3,5,6],[4],[5],[6]],![[],[],[],[3,4,6],[4,5,6],[6],[5]],![[],[],[],[],[6],[4,5,6],[4]],![[],[],[],[],[],[5],[6]],![[],[],[],[],[],[],[6]],![[],[],[],[],[],[],[]]]

private theorem sqRel_eq (i : Fin 7) : gen i * gen i = ((sqRel i).map gen).prod := by
  have h : ∀ i : Fin 7, ∀ t : Fin 275,
      (gen i * gen i).val t = (((sqRel i).map gen).prod).val t := by
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))
private theorem conjRel_eq (i j : Fin 7) (hij : i < j) :
    (gen i)⁻¹ * gen j * gen i = ((conjRel i j).map gen).prod := by
  have h : ∀ i j : Fin 7, i < j → ∀ t : Fin 275,
      ((gen i)⁻¹ * gen j * gen i).val t = (((conjRel i j).map gen).prod).val t := by
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j hij))
private theorem gen_triangular : BinaryCollection.triangular ([0,1,2,3,4,5,6].map gen) := by
  have step (a : Fin 7) (l : List (Fin 7))
      (hl : ∀ b ∈ l, a < b)
      (hs : ∀ i ∈ sqRel a, i ∈ l)
      (hc : ∀ b ∈ l, ∀ i ∈ conjRel a b, i ∈ l)
      (ht : BinaryCollection.triangular (l.map gen)) :
      BinaryCollection.triangular ((a :: l).map gen) :=
    BinaryCollection.triangular_cons_of_words gen a l (sqRel a) (conjRel a)
      (sqRel_eq a) (fun b hb => conjRel_eq a b (hl b hb)) hs hc ht
  apply step 0 [1,2,3,4,5,6] (by decide) (by decide) (by decide)
  apply step 1 [2,3,4,5,6] (by decide) (by decide) (by decide)
  apply step 2 [3,4,5,6] (by decide) (by decide) (by decide)
  apply step 3 [4,5,6] (by decide) (by decide) (by decide)
  apply step 4 [5,6] (by decide) (by decide) (by decide)
  apply step 5 [6] (by decide) (by decide) (by decide)
  apply step 6 [] (by decide) (by decide) (by decide)
  trivial

private def candidate : Subgroup Carrier := closure {g | g ∈ [0,1,2,3,4,5,6].map gen}
private theorem candidate_card : Nat.card candidate = 128 := by
  apply BinaryCollection.card_closure_of_injective _ gen_triangular
  have h : Function.Injective (fun i : Fin 128 =>
      ((BinaryCollection.product ([0,1,2,3,4,5,6].map gen) i.val).val 1,
       (BinaryCollection.product ([0,1,2,3,4,5,6].map gen) i.val).val 2)) := by
    decide +kernel
  intro i j he
  exact h (congrArg (fun g : Carrier => (g.val 1,g.val 2)) he)
private theorem candidate_gen_mem (i : Fin 7) : gen i ∈ candidate := by
  apply Subgroup.subset_closure
  exact List.mem_map.mpr ⟨i, by fin_cases i <;> simp, rfl⟩

private def squareWord (i : Fin 16) : Carrier :=
  (x0^2)^(i.val%2) * (x2^2)^((i.val/2)%2) *
    ((x0*x2)^2)^((i.val/4)%2) * ((x1*x2)^2)^((i.val/8)%2)
private theorem squareWord_injective : Function.Injective squareWord := by
  have h : Function.Injective (fun i : Fin 16 => (squareWord i).val 14) := by
    decide +kernel
  exact fun _ _ he => h (congrArg (fun g : Carrier => g.val 14) he)

/-- Sixteen square words in the certified order-128 subgroup give the bound
for every actual McL Sylow subgroup. -/
theorem sylow_frattini_card_le_eight (P : Sylow 2 Carrier) :
    Nat.card (P ⧸ frattini P) ≤ 8 := by
  have htwo : IsPGroup 2 candidate := IsPGroup.of_card (n := 7) candidate_card
  obtain ⟨Q,hQ⟩ := htwo.exists_le_sylow
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv Q)]
  let a : Q := ⟨x0,hQ (candidate_gen_mem 0)⟩
  let b : Q := ⟨x1,hQ (candidate_gen_mem 1)⟩
  let c : Q := ⟨x2,hQ (candidate_gen_mem 2)⟩
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  have hs (z : Q) : z^2 ∈ frattini Q := pth_power_mem_frattini_of_isPGroup (p := 2) z
  let w (i : Fin 16) : Q :=
    (a^2)^(i.val%2) * (c^2)^((i.val/2)%2) *
      ((a*c)^2)^((i.val/4)%2) * ((b*c)^2)^((i.val/8)%2)
  have hw (i : Fin 16) : w i ∈ frattini Q :=
    mul_mem (mul_mem (mul_mem (pow_mem (hs a) _) (pow_mem (hs c) _))
      (pow_mem (hs (a*c)) _)) (pow_mem (hs (b*c)) _)
  let f : Fin 16 → frattini Q := fun i => ⟨w i,hw i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply squareWord_injective
    exact congrArg (fun z : frattini Q => (z.val : Carrier)) he
  have h16 : 16 ≤ Nat.card (frattini Q) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hcard : Nat.card Q ≤ 128 := by
    obtain ⟨k,hk⟩ := Q.isPGroup'.exists_card_eq
    have hd := (Q : Subgroup Carrier).card_subgroup_dvd_card
    rw [hk, Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
      Atlas.Sporadic.McLaughlin.card] at hd
    have hk7 : k ≤ 7 := by
      by_contra! h
      have hd' := (pow_dvd_pow 2 (by omega : 8 ≤ k)).trans hd
      norm_num [Atlas.Sporadic.McLaughlin.order] at hd'
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk7
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini Q)
  nlinarith

/-- Transport through an actual McL marking preserves the literal Sylow subgroup. -/
theorem sylow_frattini_card_le_eight_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* Carrier) (P : Sylow 2 G) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup G))]
  exact sylow_frattini_card_le_eight Q
end Sporadic.LeechRelated.McL.FrattiniEight
