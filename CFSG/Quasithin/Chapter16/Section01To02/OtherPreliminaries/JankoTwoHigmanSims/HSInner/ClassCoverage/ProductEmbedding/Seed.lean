module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
import Mathlib.Tactic.FinCases

/-!
# Fixed words for the product-class centralizer in HS

The first two words generate the candidate automorphism factor `H`; the next
two generate `D`, to be identified with the actual alternating group on six
letters. The last two give a candidate index-six subgroup of `D`. Every word
belongs to the exact ATLAS carrier, and all six commute with the marked `t`.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
class 2B; ATLAS HSG1-p100B0. Candidate words come from the retained
`ClassCoverage/source/product_discovery.txt`. Tables encode the inverse of
the ATLAS right-action permutations, preserving word order. The accompanying
script supplies data only; Lean checks all identities in the kernel.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
open Sporadic.LeechRelated.HS Theory.GroupTheory Subgroup
open OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Seed

private def wordGen (i : Fin 3) : Equiv.Perm (Fin 100) :=
  match i.val with
  | 0 => p0
  | 1 => p1
  | _ => p1⁻¹

private theorem wordGen_mem (i : Fin 3) : wordGen i ∈ generated := by
  have ha : p0 ∈ generated := a_eq_generator.symm ▸ subset_closure (by simp)
  have hb : p1 ∈ generated := b_eq_generator.symm ▸ subset_closure (by simp)
  fin_cases i
  · exact ha
  · exact hb
  · exact generated.inv_mem hb

private theorem word_mem (w : List (Fin 3)) : evalWord wordGen w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (wordGen_mem i) ih

/-- Words in the alphabet `[a, b, b⁻¹]`, in Lean multiplication order. -/
def word : Fin 6 → List (Fin 3) :=
  ![[2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0],
    [2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 2],
    [1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0],
    [1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [2, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0]]

def codes : List ℕ :=
  [770688756380566560187664479781067929355407677554446954421212003075054781142829180088553230857092631804227612770091691174106158357009207146981709970780609500229924682685096990245949388877628609603772175623282484,
   4052037090028419442640705952738558399835871524547172546980751679248376193679639510186022195945553219093013300394344781930155105987471607137963021294260682358053753427334912530441738357559212197468048649536130831,
   3008923414126975661165282592019593260377165990885505056847078927111590166571661306226469464054063645534316784275529505310657870326905258299190012330173073493925380160437360676538833271092055704292390703580586453,
   1303627481187934755557311436521888720965161342890626410385963713835903024646672517184280584537585760380646457107253893970740224765622675922813131290643543237820228330339564597743451780278643407120247992268914872,
   110651608595713660716261283789572001060805426946616920950997821599396532120066662798303766544426846223101579452097445480704432638170410369245695490331479915255380926486171049448628635771439152841934475049224128,
   1280485000909101444469489404129366827470786264696504006893156666545475058095785671810847933251615814501792451602667934667012557032629654538662085650098799510735806278641871065593664634258335598710862793472919611]

def inverseCodes : List ℕ :=
  [1567458974972842456695327808271330226965005087166192222941087861518280351897728479474657393202342179052698218080931047002526888497802254643822938847390412473295205245123839362194335983344537735626828046696694924,
   2004513604838391585873410841136818373986619227561600431145507183314306763975787484930237238127752645255862775094510798878401739379694721981265224447115838003528017068750279931908887028546478644680476263841959055,
   1161060704664307038627865781732344219711736252443833664794783140076258595654600697393502178510926134305775324909906272187711508331175585391166302489938900676096087337437899884307049183207966508944714269098755003,
   1303627481187934755557311436521888720965161342890626410385963713835903024646672517184280584537585760380646457107253893970740224765622675922813131290643543237820228330339564597743451780278643407120247992268914872,
   1083918580533821471725037715873577371731744061485536225530135268960382452959928265542126413819928793985609764207521170329551888796544089561769363506862596905869933238344526919191389273243283404153569324744360354,
   2804872447655380517612581169287596753419650163650610693994933360909790688414156826463447669215156487703671236603902106583763807026794755143863006194641530426410954575005963935132180241472049061957111925773066713]

/-- Forward action, with letters numbered from zero. -/
def pointMap (i : Fin 6) (x : Fin 100) : Fin 100 :=
  ⟨(codes[i.val]! >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

/-- Inverse action, with letters numbered from zero. -/
def inversePointMap (i : Fin 6) (x : Fin 100) : Fin 100 :=
  ⟨(inverseCodes[i.val]! >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem tables_left : ∀ i x, inversePointMap i (pointMap i x) = x := by
  apply Certificate.allFin
  decide +kernel

/-- Six actual permutations, subsequently certified to be carrier words. -/
def permutation (i : Fin 6) : Equiv.Perm (Fin 100) :=
  tablePerm (pointMap i) (inversePointMap i) (tables_left i)
    (rightInverse_of_leftInverse_fin (tables_left i))

private theorem permutation_word (i : Fin 6) : evalWord wordGen (word i) = permutation i := by
  have h : ∀ i : Fin 6, ∀ x : Fin 100,
      evalWord wordGen (word i) x = permutation i x := by
    apply Certificate.allFin
    decide +kernel
  exact Equiv.ext (h i)

theorem permutation_mem (i : Fin 6) : permutation i ∈ generated :=
  permutation_word i ▸ word_mem (word i)

/-- The certified words as elements of the exact HS carrier. -/
def generator (i : Fin 6) : Carrier := ⟨permutation i, permutation_mem i⟩

theorem generator_commutes (i : Fin 6) : generator i * t = t * generator i := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 6, ∀ x : Fin 100,
      inclusion (generator i * t) x = inclusion (t * generator i) x := by
    apply Certificate.allFin
    decide +kernel
  exact h i

end Seed

/-- Candidate automorphism factor, specified by two checked ATLAS words. -/
def H : Subgroup Carrier := closure {Seed.generator 0, Seed.generator 1}

/-- Candidate alternating subgroup, specified independently by two checked words. -/
def D : Subgroup Carrier := closure {Seed.generator 2, Seed.generator 3}

/-- Candidate index-six subgroup used for the faithful six-letter action. -/
def A : Subgroup Carrier := closure {Seed.generator 4, Seed.generator 5}

theorem H_le_centralizer : H ≤ centralizer ({t} : Set Carrier) := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact mem_centralizer_singleton_iff.mpr (Seed.generator_commutes _)
  · rw [Set.mem_singleton_iff.mp hx]
    exact mem_centralizer_singleton_iff.mpr (Seed.generator_commutes _)

theorem D_le_centralizer : D ≤ centralizer ({t} : Set Carrier) := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact mem_centralizer_singleton_iff.mpr (Seed.generator_commutes _)
  · rw [Set.mem_singleton_iff.mp hx]
    exact mem_centralizer_singleton_iff.mpr (Seed.generator_commutes _)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
