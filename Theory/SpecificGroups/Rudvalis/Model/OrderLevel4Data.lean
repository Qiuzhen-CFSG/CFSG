module

public import Theory.SpecificGroups.Rudvalis.Model.OrderChainData
import Mathlib.Tactic.FinCases

/-!
# Level 4 witnesses for the Rudvalis order certificate

The witnesses derive from the ATLAS degree-4060 generators stored in
`RuG1-p4060B0.g1` and `RuG1-p4060B0.g2` beside `Model.Basic`.
The inverse point convention preserves the order of word multiplication.
GAP is an untrusted witness generator; all asserted equalities are checked
by Lean's kernel. See `OrderCertificate/GenerateChain.g`.
The 4 representatives are words in the level-4 generators.
Their distinct images of base point 4 are checked here. Transition words
are witness data only: their permutation identities are checked separately.
-/

namespace Rudvalis.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000
set_option Elab.async false

@[expose] public def L4RepWordBlock0 (x : Fin 4) : List (Fin 2) :=
  (if x.val < 2 then (if x.val < 1 then [] else unpackWord 1 0 1) else (if x.val < 3 then unpackWord 1 1 1 else unpackWord 1 0 2))

@[expose] public def L4RepWord (x : Fin 4) : List (Fin 2) :=
  L4RepWordBlock0 x

@[expose] public def L4Rep (r : Fin 4) : Equiv.Perm (Fin 4060) :=
  evalWord L4Gen (L4RepWord r)

public theorem L4Rep_mem (r : Fin 4) : L4Rep r ∈ H4 :=
  evalWord_mem_wordSubgroup L4Gen L4Inv L4Inv_spec _

@[expose] public def L4PointPacked : Nat := 126895800205316

@[expose] public def L4Point (x : Fin 4) : Fin 4060 :=
  ⟨(L4PointPacked >>> (12 * x.val)) % 4096 % 4060, Nat.mod_lt _ (by decide)⟩

@[expose] public def L4PointInvPacked : Nat := 9306566900688236568287269402993949084288466780185883180443080170400003506332308672001250527354586297476052622284258199332230716622167221412031717206243262877532360720686985489756448563932924354086580063675475894991117272737130483808671943102601638946258410940988270507785419843884400283238776471128598489123252263837626154415920332124164047353321175805624904548985482891007284328895938561615715520729333581110413656592343345825826213017235326001832874705959060885859369835178328729405047983674912043363738219067137085880684441759220396844104165954379214744418722554905199972147736895417415544703137263885065118175195790995099138988789380993846160037994823938377818202896293301065316766337185134796565222469360639121892646516521019256692878205777707378623420747273240619710039839383600224229297708099577985141425832189135100821088810564865281404904631054945468200131468234793738286515037204336982209329838202757192580070111784523995263775921569156748055530768612130937327326305627614681182942914375652325286550144058667244406722287737056262434259499400150398473909627723246821270731502121809676704187284203916470938966821383279026836574877016019872742668374275555376733284585809527095383877280661087107678353430609899035804527910183821221430833682010931487007310222999968821116104649238148783507261164756919707485180651652216520851906306072436765370063203395904999312000875189846565767077649813240931516043795234003512983552

@[expose] public def L4PointInv (x : Fin 4060) : Fin 4 :=
  ⟨(L4PointInvPacked >>> (2 * x.val)) % 4 % 4, Nat.mod_lt _ (by decide)⟩

@[expose] public def L4Act0Packed : Nat := 141

@[expose] public def L4Act0 (x : Fin 4) : Fin 4 :=
  ⟨(L4Act0Packed >>> (2 * x.val)) % 4 % 4, Nat.mod_lt _ (by decide)⟩

@[expose] public def L4Factor0Block0 (x : Fin 4) : List (Fin 0) :=
  (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else []))

@[expose] public def L4Factor0 (x : Fin 4) : List (Fin 0) :=
  L4Factor0Block0 x

@[expose] public def L4Act1Packed : Nat := 114

@[expose] public def L4Act1 (x : Fin 4) : Fin 4 :=
  ⟨(L4Act1Packed >>> (2 * x.val)) % 4 % 4, Nat.mod_lt _ (by decide)⟩

@[expose] public def L4Factor1Block0 (x : Fin 4) : List (Fin 0) :=
  (if x.val < 2 then (if x.val < 1 then [] else []) else (if x.val < 3 then [] else []))

@[expose] public def L4Factor1 (x : Fin 4) : List (Fin 0) :=
  L4Factor1Block0 x

@[expose] public def L4Act : Fin 2 → Fin 4 → Fin 4
  | 0 => L4Act0
  | 1 => L4Act1

@[expose] public def L4Factor : Fin 2 → Fin 4 → List (Fin 0)
  | 0 => L4Factor0
  | 1 => L4Factor1

public theorem L4Rep_base : L4Rep 0 = 1 := rfl

public theorem L4Rep_point : ∀ r, L4Rep r 4 = L4Point r := by
  apply allFin
  decide +kernel

public theorem L4Point_injective : Function.Injective L4Point := by
  have h : ∀ r, L4PointInv (L4Point r) = r := by
    apply allFin
    decide +kernel
  exact Function.LeftInverse.injective h

end Rudvalis.OrderCertificate
