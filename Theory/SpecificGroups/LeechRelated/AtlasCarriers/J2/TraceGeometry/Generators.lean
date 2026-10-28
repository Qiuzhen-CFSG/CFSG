module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.TableSupport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms

/-!
# Literal generators for the degree-six Hall--Janko trace calculation

The order-five pair and its order-six normalizer give a rotation on the
25 weights of C₅ × C₅. A commuting cubic and a fifth-order element satisfy
the (3,5,2) triangle relations. The same cubic is a central commutator.
These identities are the local group input to the weight calculation; no
completeness of conjugacy classes or modular representations is asserted.

Every witness is a word in the original degree-100 ATLAS generators. Lookup
tables are compared with those words and all identities are kernel checked.
The outer normalizer uses the literal `ExceptionalParabolics.involutionAut`.

Source application: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle,
corrected Table 2, degree-six characteristic-two J₂ entry. Original permutation
attribution: R. A. Wilson et al., ATLAS `J2G1-p100B0`, retained in
`AtlasCarriers/source/`. The adjacent `source/` files are untrusted discovery
witnesses, not proof inputs.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.TraceGeometry
open GeneratorPair GeneratorPair.SecondOrbitCertificate Theory.GroupTheory

private def fastA : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547) (packedMap 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)

private theorem tableA_fast : tableA = fastA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def fastB : Equiv.Perm (Fin 100) :=
  tablePerm (packedMap 3234967701574023288017704270913789399548845676982065206373928870228913752386975839948414443758577378205229365791802719998856417312117905715024748407215049785228781853510609863692219811450715825262485969147626773) (packedMap 3377862216939204608209019933455681426219024363596881756892669536352030827785925351345362563460844105849526589246761354822075856259740605599629990671129056314103711580268098197814694108667979975332570640941909071)
    (by apply allFin; decide +kernel) (by apply allFin; decide +kernel)

private theorem tableB_fast : tableB = fastB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

def xWord : List (Fin 3) := [1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
def x : Carrier := evalWord ![a,b,b⁻¹] xWord
private def xValues : Fin 100 → Fin 100 := packedMap 1042058804344934845579501611901232844008111895875387836113508841706960846987920546582575237848027267843773102907395034074675133568352947047780070582427809271087494164156963770202675011418213982828899143239619969
private def xInvValues : Fin 100 → Fin 100 := packedMap 917722495981082827959090453177340052377684742151359816293467578119905095695854083217551063171219494289627941059317071293383295635155698553210970861427923041857440929463403866261064572541639651547701251788767321
private def xTable : Equiv.Perm (Fin 100) where
  toFun := xValues
  invFun := xInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem x_table : inclusion x = xTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] xWord = xTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def yWord : List (Fin 3) := [1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0]
def y : Carrier := evalWord ![a,b,b⁻¹] yWord
private def yValues : Fin 100 → Fin 100 := packedMap 1563595342825505915862544955397953110058020694029274272068822888421673842125284470540536010610750232993975513789129078931421473703908978532481542753671747312980707482396663678031818484693321422338529329998337821
private def yInvValues : Fin 100 → Fin 100 := packedMap 1369528141881730338593462182314241188847611195378088311428555784637465587736983097923249957472030533027828610724470329133197851185159095506292640838646098718920542020336826265902999098612280977042084826692095507
private def yTable : Equiv.Perm (Fin 100) where
  toFun := yValues
  invFun := yInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem y_table : inclusion y = yTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] yWord = yTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def rWord : List (Fin 3) := [0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0]
def r : Carrier := evalWord ![a,b,b⁻¹] rWord
private def rValues : Fin 100 → Fin 100 := packedMap 1489600402409391142960736118223968116096138644936491718021286510225593595147542076297624448017331916299855194590362743548198030786088949707978391615393915161404988055559835486151542145542478926780972983647312899
private def rInvValues : Fin 100 → Fin 100 := packedMap 3391503884570694329201147455471285022638921560577471957458910449006208986865001031178767896153214138212733514646355571430920843249772949042085197591482850117465696880815803572472656972013892227796575371916057282
private def rTable : Equiv.Perm (Fin 100) where
  toFun := rValues
  invFun := rInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem r_table : inclusion r = rTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] rWord = rTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def cWord : List (Fin 3) := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2]
def c : Carrier := evalWord ![a,b,b⁻¹] cWord
private def cValues : Fin 100 → Fin 100 := packedMap 3196116099995604126017953045598116569692579267865646233786817825087909962608389298554413710478224521938534455826874431921265222115019539072309426131814250988557340611751732383336442813446034874687554331094435716
private def cInvValues : Fin 100 → Fin 100 := packedMap 4052154807866520748406845727395293046472658654910734743681180584249651907510478793414322885369310705840389355005368858755658204380171775548029264415987769406280397757565978901839840943306457917242484035026964932
private def cTable : Equiv.Perm (Fin 100) where
  toFun := cValues
  invFun := cInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem c_table : inclusion c = cTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] cWord = cTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def dWord : List (Fin 3) := [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2]
def d : Carrier := evalWord ![a,b,b⁻¹] dWord
private def dValues : Fin 100 → Fin 100 := packedMap 1211713903127677943257173989187889493239464202989507055088900734324524217092209724351192660232027416041539610007916750479347835827934507487161716836741837498580050619476102912718301150085857333831017304208838405
private def dInvValues : Fin 100 → Fin 100 := packedMap 1954056360531099681314197604972337585500870719975028070940118924310032712994336649761150154866343320968933275625849369056163432064481465079503730859244610681564793594851368426303282842139235129970640071213421473
private def dTable : Equiv.Perm (Fin 100) where
  toFun := dValues
  invFun := dInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem d_table : inclusion d = dTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] dWord = dTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def uWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0]
def u : Carrier := evalWord ![a,b,b⁻¹] uWord
private def uValues : Fin 100 → Fin 100 := packedMap 4052033214399507800498542578374166606829917687194912245790401988151458113040791423411425275322236418066885460872557918910991004766727996274124718085240746865475148520904662684370145463903696283002574730723116928
private def uInvValues : Fin 100 → Fin 100 := packedMap 3196163350828321115196744034280590183168643131041091758859642633711736696868662135423747731691871304982555128118279674073500960295899363309063442856195218774426773740945237829892220538884587052083448424111313280
private def uTable : Equiv.Perm (Fin 100) where
  toFun := uValues
  invFun := uInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem u_table : inclusion u = uTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] uWord = uTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def vWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]
def v : Carrier := evalWord ![a,b,b⁻¹] vWord
private def vValues : Fin 100 → Fin 100 := packedMap 1443174578957592503484999574280811219340517647009304895533683968425236312716283125859975099699253296517000978133792885033231991092537738349681284621251820358375003822084660165675638170983834137477749422415085645
private def vInvValues : Fin 100 → Fin 100 := packedMap 2795948963863521780669102744798601657226657702733485393198864339985418193522341851567875972408123314339224677710537049597506077272401167921847994694962297081924587420830398626077658729133159849704509695037859457
private def vTable : Equiv.Perm (Fin 100) where
  toFun := vValues
  invFun := vInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem v_table : inclusion v = vTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] vWord = vTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

def kWord : List (Fin 3) := [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1]
def k : Carrier := evalWord ![a,b,b⁻¹] kWord
private def kValues : Fin 100 → Fin 100 := packedMap 434174712462663421307175315876765182016183888851001367310275130590302308557450049657565155613490520005441016697760516715761982275493138698326891536340666221874994943115043759214489909543004564469002563027595266
private def kInvValues : Fin 100 → Fin 100 := packedMap 2318365432058052049816914009350357506877856894006547462919250405127243889598949793018164761451992235613727389344200866564879571910420792661908062953217047621708482753339510924989771244677217965522901964387523145
private def kTable : Equiv.Perm (Fin 100) where
  toFun := kValues
  invFun := kInvValues
  left_inv := by
    apply allFin
    decide +kernel
  right_inv := by
    apply allFin
    decide +kernel

set_option maxRecDepth 20000 in
private theorem k_table : inclusion k = kTable := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] kWord = kTable
  rw [generatorA_eq_table, generatorB_eq_table, tableA_fast, tableB_fast]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem x_pow_five : x ^ 5 = 1 := by
  apply inclusion_injective
  simp only [map_pow, map_one, x_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem y_pow_five : y ^ 5 = 1 := by
  apply inclusion_injective
  simp only [map_pow, map_one, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem x_y_commute : x * y = y * x := by
  apply inclusion_injective
  simp only [map_mul, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem r_pow_six : r ^ 6 = 1 := by
  apply inclusion_injective
  simp only [map_pow, map_one, r_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem r_conj_x : r * x * r⁻¹ = y := by
  apply inclusion_injective
  simp only [map_mul, map_inv, x_table, y_table, r_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem r_conj_y : r * y * r⁻¹ = x⁻¹ * y := by
  apply inclusion_injective
  simp only [map_mul, map_inv, x_table, y_table, r_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem d_eq : d = x * y⁻¹ ^ 2 := by
  apply inclusion_injective
  simp only [map_mul, map_pow, map_inv, x_table, y_table, d_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem c_pow_three : c ^ 3 = 1 := by
  apply inclusion_injective
  simp only [map_pow, map_one, c_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem d_pow_five : d ^ 5 = 1 := by
  apply inclusion_injective
  simp only [map_pow, map_one, d_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem cd_pow_two : (c * d) ^ 2 = 1 := by
  apply inclusion_injective
  simp only [map_mul, map_pow, map_one, c_table, d_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem c_x_commute : c * x = x * c := by
  apply inclusion_injective
  simp only [map_mul, x_table, c_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem central_commutator : v * u * v⁻¹ * u⁻¹ = c := by
  apply inclusion_injective
  simp only [map_mul, map_inv, c_table, u_table, v_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem c_u_commute : c * u = u * c := by
  apply inclusion_injective
  simp only [map_mul, c_table, u_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A checked identity on the literal ATLAS carrier. -/
theorem c_v_commute : c * v = v * c := by
  apply inclusion_injective
  simp only [map_mul, c_table, v_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- The marking of the nontrivial field twist, up to inner conjugacy. -/
def outerTwist : MulAut Carrier := MulAut.conj k * ExceptionalParabolics.involutionAut

theorem outerTwist_x : outerTwist x = x ^ 3 * y ^ 2 := by
  apply inclusion_injective
  change inclusion k * (ExceptionalParabolics.involution * inclusion x *
    ExceptionalParabolics.involution⁻¹) * (inclusion k)⁻¹ = inclusion (x ^ 3 * y ^ 2)
  simp only [map_mul, map_pow, k_table, x_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem outerTwist_y : outerTwist y = y ^ 2 := by
  apply inclusion_injective
  change inclusion k * (ExceptionalParabolics.involution * inclusion y *
    ExceptionalParabolics.involution⁻¹) * (inclusion k)⁻¹ = inclusion (y ^ 2)
  simp only [map_pow, k_table, y_table]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- The twenty-five normal forms are distinct; in particular the action
of this elementary abelian group cannot be trivial in a faithful module. -/
theorem five_pair_injective : Function.Injective
    (fun ij : Fin 5 × Fin 5 => x ^ ij.1.val * y ^ ij.2.val) := by
  intro ij kl h
  have hh := congrArg inclusion h
  simp only [map_mul, map_pow, x_table, y_table] at hh
  have hp := congrArg (fun q : Equiv.Perm (Fin 100) => q 0) hh
  exact (by decide +kernel : Function.Injective
    (fun ij : Fin 5 × Fin 5 => (xTable ^ ij.1.val * yTable ^ ij.2.val) 0)) hp

theorem x_ne_one : x ≠ 1 := by
  intro h
  have hh := congrArg inclusion h
  rw [x_table, map_one] at hh
  exact (by decide +kernel : xTable ≠ 1) hh

theorem c_ne_one : c ≠ 1 := by
  intro h
  have hh := congrArg inclusion h
  rw [c_table, map_one] at hh
  exact (by decide +kernel : cTable ≠ 1) hh

theorem d_ne_one : d ≠ 1 := by
  intro h
  have hh := congrArg inclusion h
  rw [d_table, map_one] at hh
  exact (by decide +kernel : dTable ≠ 1) hh

end Sporadic.LeechRelated.J2.TraceGeometry
