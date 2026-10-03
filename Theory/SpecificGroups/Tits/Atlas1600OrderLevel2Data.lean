module

public import Theory.SpecificGroups.Tits.Atlas1600OrderData

/-!
# Level 2 witnesses for the Atlas degree-1600 order certificate

Representatives are words in the level-2 generators. The tables record their
images of base point 2 and candidate transition factorizations through level 3.
The accompanying certificate checks these witnesses before using the generic
word-subgroup cardinality theorem. Source: Atlas degree-1600 generators in
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

@[expose] public def L2RepWordBlock0 (x : Fin 32) : List (Fin 6) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else [0]) else (if x.val < 3 then [1] else [2])) else (if x.val < 6 then (if x.val < 5 then [3] else [5]) else (if x.val < 7 then [0, 0] else [1, 0]))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [2, 0] else [5, 0]) else (if x.val < 11 then [0, 1] else [2, 1])) else (if x.val < 14 then (if x.val < 13 then [3, 1] else [5, 1]) else (if x.val < 15 then [0, 2] else [2, 2])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [1, 3] else [2, 3]) else (if x.val < 19 then [5, 5] else [1, 0, 0])) else (if x.val < 22 then (if x.val < 21 then [2, 0, 0] else [5, 0, 0]) else (if x.val < 23 then [0, 1, 0] else [2, 1, 0]))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [3, 1, 0] else [5, 1, 0]) else (if x.val < 27 then [2, 2, 0] else [5, 5, 0])) else (if x.val < 30 then (if x.val < 29 then [2, 0, 1] else [0, 2, 1]) else (if x.val < 31 then [2, 1, 0, 0] else [5, 1, 0, 0])))))

@[expose] public def L2RepWord (x : Fin 32) : List (Fin 6) :=
  L2RepWordBlock0 x

@[expose] public def L2Rep (r : Fin 32) : Equiv.Perm (Fin 1600) :=
  evalWord L2Gen (L2RepWord r)

public theorem L2Rep_mem (r : Fin 32) : L2Rep r ∈ H2 :=
  evalWord_mem_wordSubgroup L2Gen L2Inv L2Inv_spec _

@[expose] public def L2PointPacked : Nat := 5230370862117445220803604097888068223524668933543152984333811386265798663757616802897339051525772871628802

@[expose] public def L2Point (x : Fin 32) : Fin 1600 :=
  ⟨(L2PointPacked >>> (11 * x.val)) % 2048 % 1600, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2PointInvPacked : Nat := 3841876846159369404259972825364729100166858119950835280036496151750430120518956323476651627666972014059013646041204439419597026051274167002575503318420121045794333184307423575509107874734461744589661364286994779821247402921412489415958031425084982677415570199058229727489658536543978533837632681656964249936526718853401715280106748818769573656519553920171731864543187443399834539228143629955928133328918626247115467472698608153831549578139203024123442413790437345319792001407112027233892827111848393427082319083951985577969094321551063676105315838661967089568944154446170255178433751288248015999356188759084931326140772571755245280297224346562045962030946823925266761551279615327653893644636022979509174671323674661644766009628721283002167152131514152704626834689815396388706194451814137666403190569842867727765338705185853575897326476019477994297696720262329356572890877291490457119803355195111201850215462816054484859814341705014065425678580271781974462671347564390491596305286505596080133296576649977747512881068769635333620728990184382410928654770073165539108811488057275087771289196929245299716723126415750274827739958333354128814644834931555410555397464137808541393744170958412555358574139785917497845951079328160758091758733432858363852540078752189837125895730852154412712308655072193392081258432220640627493436719667874306430069347028420962395902341175781061836086607353754113340473054918043511290253148710965035165924699095775608053102291016433142955393410252930739275983176946364984643298806862525248652794028384560962673726672729594516714082664715759995597819210409778998595111284781209110452531605473683021686346444635693838005433778021070026190724221314139341612319608709401597917854721481072310153060075472825484436597939556133622827260945898908056117983829293815710245273603041741479904460460576932680894560350711591420579271627773938125876997368628762646511934160070444856289679410735708207259609691252906383659761664

@[expose] public def L2PointInv (x : Fin 1600) : Fin 32 :=
  ⟨(L2PointInvPacked >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Act0Packed : Nat := 1312997599420054970846810168908792677552334776513

@[expose] public def L2Act0 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act0Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor0Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor0 (x : Fin 32) : List (Fin 0) :=
  L2Factor0Block0 x

@[expose] public def L2Act1Packed : Nat := 944059292545558092463187122761556095516119826658

@[expose] public def L2Act1 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act1Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor1Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor1 (x : Fin 32) : List (Fin 0) :=
  L2Factor1Block0 x

@[expose] public def L2Act2Packed : Nat := 899723976435202896179867544235993929953354165507

@[expose] public def L2Act2 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act2Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor2Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor2 (x : Fin 32) : List (Fin 0) :=
  L2Factor2Block0 x

@[expose] public def L2Act3Packed : Nat := 1183722839759387914421644382978603860374124277764

@[expose] public def L2Act3 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act3Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor3Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor3 (x : Fin 32) : List (Fin 0) :=
  L2Factor3Block0 x

@[expose] public def L2Act4Packed : Nat := 944059292545558092463187122761556095516119826658

@[expose] public def L2Act4 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act4Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor4Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor4 (x : Fin 32) : List (Fin 0) :=
  L2Factor4Block0 x

@[expose] public def L2Act5Packed : Nat := 1123972247840534035921725487229468453198744270117

@[expose] public def L2Act5 (x : Fin 32) : Fin 32 :=
  ⟨(L2Act5Packed >>> (5 * x.val)) % 32 % 32, Nat.mod_lt _ (by decide)⟩

@[expose] public def L2Factor5Block0 (x : Fin 32) : List (Fin 0) :=
  (if x.val < 16 then (if x.val < 8 then (if x.val < 4 then (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else [])) else (if x.val < 6 then (if x.val < 5 then [] else []) else (if x.val < 7 then [] else []))) else (if x.val < 12 then (if x.val < 10 then (if x.val < 9 then [] else []) else (if x.val < 11 then [] else [])) else (if x.val < 14 then (if x.val < 13 then [] else []) else (if x.val < 15 then [] else [])))) else (if x.val < 24 then (if x.val < 20 then (if x.val < 18 then (if x.val < 17 then [] else []) else (if x.val < 19 then [] else [])) else (if x.val < 22 then (if x.val < 21 then [] else []) else (if x.val < 23 then [] else []))) else (if x.val < 28 then (if x.val < 26 then (if x.val < 25 then [] else []) else (if x.val < 27 then [] else [])) else (if x.val < 30 then (if x.val < 29 then [] else []) else (if x.val < 31 then [] else [])))))

@[expose] public def L2Factor5 (x : Fin 32) : List (Fin 0) :=
  L2Factor5Block0 x

@[expose] public def L2Act : Fin 6 → Fin 32 → Fin 32
  | 0 => L2Act0
  | 1 => L2Act1
  | 2 => L2Act2
  | 3 => L2Act3
  | 4 => L2Act4
  | 5 => L2Act5

@[expose] public def L2Factor : Fin 6 → Fin 32 → List (Fin 0)
  | 0 => L2Factor0
  | 1 => L2Factor1
  | 2 => L2Factor2
  | 3 => L2Factor3
  | 4 => L2Factor4
  | 5 => L2Factor5

public theorem L2Rep_base : L2Rep 0 = 1 := rfl

public theorem L2Rep_point : ∀ r, L2Rep r 2 = L2Point r := by
  apply allFin
  decide +kernel

public theorem L2Point_injective : Function.Injective L2Point := by
  have h : ∀ r, L2PointInv (L2Point r) = r := by
    apply allFin
    decide +kernel
  exact Function.LeftInverse.injective h

end Tits.Atlas1600OrderCertificate
