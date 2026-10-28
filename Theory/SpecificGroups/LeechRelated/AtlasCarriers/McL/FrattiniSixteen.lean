module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elements

public import Theory.GroupTheory.BinaryCollection.Subsequence
public import Theory.GroupTheory.SylowFrattiniBounds
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Source

/-!
# Four Frattini generators for the actual McL Sylow subgroup

Two words in the sourced degree-275 ATLAS generators generate a two-group
of order 32. Fifteen square and conjugation identities give binary normal
forms, separated by evaluation at one letter. The three words x², y²,
(xy)² have eight distinct products. In a Sylow subgroup containing this
two-group these products lie in the Frattini subgroup. The actual McL order
bounds the Sylow subgroup by 128, hence its Frattini quotient by sixteen.
Sylow conjugacy transports the bound to every marking.

GAP discovered the words; every identity and separation is kernel checked.
The packed tables follow the unchanged right-to-left action conversion in
`AtlasCarriers.McL`; no computational oracle is a premise. The group order
uses the proved comparison with the Leech model.
Source: ATLAS McLG1-p275B0 (see the carrier module); Aschbacher--Smith
4.4.10--11, printed p.621. The exterior odd-normalizer consumer uses the
absence of the prime 31 from GL₄(2) to exclude a PSL₅(2) outer section.
-/

public section
namespace Sporadic.LeechRelated.McL.FrattiniSixteen
open Sporadic.LeechRelated.McL.ThreeRank
open Subgroup
open Theory.GroupTheory

private def packed (n : Nat) (i : Fin 275) : Fin 275 :=
  ⟨(n >>> (9 * i.val)) % 512 % 275, Nat.mod_lt _ (by decide)⟩

private def xWord : Carrier :=
  evalWord ![a,b,a⁻¹,b⁻¹] [3, 2, 3, 3, 2, 3, 0, 1, 0, 3, 3, 0, 1, 1, 0, 3, 0, 1, 2, 3, 3, 0, 1, 0, 3, 3, 0, 3, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0]
private def xTable : Equiv.Perm (Fin 275) :=
  tablePerm (packed 1362771207013809777636779922107951547880250934082628835798898312482504089725080533307463054816070238001260316801714493554193496103181388069095009317977638687156078904028282408010887899985794015809766557214111681854963336557854396804468858437482036070883811973799669423725625311511264890738060760776969780952236977417568116989267418046895862391301447166848744027781217805955553484318569419724052244003366286592750569949319605704356115296611449119800543330173833975195561104320366063764999444973708097569047286113322295862913442103050619745036179819488936839021017594891998173343986315118157067648998499861475020070935385325492708733947294765663675254875084282880384514854208380670545151235990558209059979318587197272899957802324789309733496685056) (packed 4508225353106087227415463755772568487390731112269136472455485315084934189516375116140538616678223539186825543039534103864546323105992055939732555106674750429209325154587180137784820661292546771737469053262679454822124156210559342111670022764907633589931016398640874508500383928165619485224377777351505007088405184300371602288776353654196136486852445853357516973538518892600589859027044456766004950439025851088944670010542441067078661223603016709722891468398451881374377936271622910020034916276305491767482630110025011457442820237197729341453503909173972749439609833595900781824737867958454367902435874602337417817317744861517931660878338937440534155760401800548178806314284798301370594354300151273771304554386721994576222232682095206197406990848)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem xTable_eq_word : xTable = xWord.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def x : Carrier := ⟨xTable, xTable_eq_word.symm ▸ xWord.property⟩

private def yWord : Carrier :=
  evalWord ![a,b,a⁻¹,b⁻¹] [3, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 0, 1, 1, 0, 1, 2, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 3, 3, 2, 3, 2, 1, 1, 2, 1, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3]
private def yTable : Equiv.Perm (Fin 275) :=
  tablePerm (packed 1357740211967100013143633897166475657456981273795488637555957630645759340062095921366405133126580431882292289933323526571975739732102790895722136325021947408922098512197708643180136070409318859670681693539143981750780067421974876628857085580169508459106238731288243667287552764189614359221775765489756349748440524756504915156756893920678866903040711284053069124041972950174805215231749014168569069954767574632596179144085398071431081364931857933910021824959906807827063315796286062986266477368310922405059496519984934715097946638727065492494627340209526034481989861771655639373981268734039933086301533408937493095732467428232770535518254790474236187470942770075854809085289407246153947946328564697817816131357237879197291990731415078441836392960) (packed 4444829712445316289728718247935427318505747295480171108746313391132829753215601311433651347231072123376853473670383662256120084868485909797992410425317187078766115953319946340326189626441968703321710047303043556396500697101079555699823477555810986018979250114822281225643815244605037959718869440611630319329447099943160740306302186176972274816071490399375334545004688386788046146357462505839082885859451494118276609967980788300800643078618103871472166240991813512287242835152359934845018200275653085580932346355354535054819844629194566565020514618378447218634889652320383584108078877842004276146196916110066234159767411686866102286052747223322666945597898955165631736260711706911397242625529077227948919423320097763096790776297495918634825158144)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)
private theorem yTable_eq_word : yTable = yWord.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def y : Carrier := ⟨yTable, yTable_eq_word.symm ▸ yWord.property⟩

private def square (i : Fin 3) : Carrier := ![x^2,y^2,(x*y)^2] i
private def squareWord (i : Fin 8) : Carrier :=
  square 0 ^ (i.val % 2) * square 1 ^ ((i.val / 2) % 2) *
    square 2 ^ ((i.val / 4) % 2)

private theorem squareWord_injective : Function.Injective squareWord := by
  have h : Function.Injective (fun i : Fin 8 => (squareWord i).val 2) := by
    decide +kernel
  exact fun _ _ he => h (congrArg (fun g : Carrier => g.val 2) he)


private def gen : Fin 5 → Carrier := ![x,y,square 0,square 1,square 2]
private def sqRel : Fin 5 → List (Fin 5) := ![[2],[3],[],[],[]]
private def conjRel : Fin 5 → Fin 5 → List (Fin 5) :=
  ![![[],[1,2,3],[2],[3,4],[4]], ![[],[],[2,4],[3],[4]],
    ![[],[],[],[3],[4]], ![[],[],[],[],[4]], ![[],[],[],[],[]]]

private theorem sqRel_eq (i : Fin 5) : gen i * gen i = ((sqRel i).map gen).prod := by
  have h : ∀ i : Fin 5, ∀ t : Fin 275,
      (gen i * gen i).val t = (((sqRel i).map gen).prod).val t := by
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

private theorem conjRel_eq (i j : Fin 5) (hij : i < j) :
    (gen i)⁻¹ * gen j * gen i = ((conjRel i j).map gen).prod := by
  have h : ∀ i j : Fin 5, i < j → ∀ t : Fin 275,
      ((gen i)⁻¹ * gen j * gen i).val t = (((conjRel i j).map gen).prod).val t := by
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j hij))

private theorem gen_triangular : BinaryCollection.triangular ([0,1,2,3,4].map gen) := by
  have step (a : Fin 5) (l : List (Fin 5))
      (hl : ∀ b ∈ l, a < b)
      (hs : ∀ i ∈ sqRel a, i ∈ l)
      (hc : ∀ b ∈ l, ∀ i ∈ conjRel a b, i ∈ l)
      (ht : BinaryCollection.triangular (l.map gen)) :
      BinaryCollection.triangular ((a :: l).map gen) :=
    BinaryCollection.triangular_cons_of_words gen a l (sqRel a) (conjRel a)
      (sqRel_eq a) (fun b hb => conjRel_eq a b (hl b hb)) hs hc ht
  apply step 0 [1,2,3,4] (by decide) (by decide) (by decide)
  apply step 1 [2,3,4] (by decide) (by decide) (by decide)
  apply step 2 [3,4] (by decide) (by decide) (by decide)
  apply step 3 [4] (by decide) (by decide) (by decide)
  apply step 4 [] (by decide) (by decide) (by decide)
  trivial

private def candidate : Subgroup Carrier := closure {g | g ∈ [0,1,2,3,4].map gen}
private theorem candidate_card : Nat.card candidate = 32 := by
  apply BinaryCollection.card_closure_of_injective _ gen_triangular
  have h : Function.Injective (fun i : Fin 32 =>
      (BinaryCollection.product ([0,1,2,3,4].map gen) i.val).val 12) := by
    decide +kernel
  intro i j he
  exact h (congrArg (fun g : Carrier => g.val 12) he)

private theorem candidate_gen_mem (i : Fin 5) : gen i ∈ candidate := by
  apply Subgroup.subset_closure
  exact List.mem_map.mpr ⟨i, by fin_cases i <;> simp, rfl⟩

/-- The certified square words force at least eight elements into the Frattini
subgroup of a Sylow two-subgroup of the actual permutation carrier. -/
theorem sylow_frattini_card_le_sixteen (P : Sylow 2 Carrier) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  have htwo : IsPGroup 2 candidate := IsPGroup.of_card (n := 5) candidate_card
  obtain ⟨Q,hQ⟩ := htwo.exists_le_sylow
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv Q)]
  let a : Q := ⟨x,hQ (candidate_gen_mem 0)⟩
  let b : Q := ⟨y,hQ (candidate_gen_mem 1)⟩
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  have hs (z : Q) : z^2 ∈ frattini Q := pth_power_mem_frattini_of_isPGroup (p := 2) z
  let w (i : Fin 8) : Q :=
    (a^2)^(i.val%2) * (b^2)^((i.val/2)%2) * ((a*b)^2)^((i.val/4)%2)
  have hw (i : Fin 8) : w i ∈ frattini Q :=
    mul_mem (mul_mem (pow_mem (hs a) _) (pow_mem (hs b) _)) (pow_mem (hs (a*b)) _)
  let f : Fin 8 → frattini Q := fun i => ⟨w i,hw i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply squareWord_injective
    exact congrArg (fun z : frattini Q => (z.val : Carrier)) he
  have h8 : 8 ≤ Nat.card (frattini Q) := by
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

/-- Transport through an actual McL marking, retaining its literal carrier. -/
theorem sylow_frattini_card_le_sixteen_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* Carrier) (P : Sylow 2 G) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup G))]
  exact sylow_frattini_card_le_sixteen Q

end Sporadic.LeechRelated.McL.FrattiniSixteen
