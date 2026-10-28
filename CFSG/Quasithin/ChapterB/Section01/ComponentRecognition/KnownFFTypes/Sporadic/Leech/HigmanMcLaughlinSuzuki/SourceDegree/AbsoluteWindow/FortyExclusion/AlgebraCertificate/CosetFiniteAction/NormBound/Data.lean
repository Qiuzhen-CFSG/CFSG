module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Data.Points
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Data.Masks
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Data.Sources
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound.Data.Predecessors

/-! Literal sparse witness for the finite HS norm quotient.
The 39 selected coordinates, 78 coefficient masks, and 86586 norm rows
are candidate data; no dimension or action assertion is made here.
Source: the adjoining source/generate.py and original source manifest. -/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound

abbrev Row := Fin 86586

def selectedCode : ℕ := 131399091784387944677722242520743940016604708591815154605495384803356808898934158144138228869437460525762327705521231874165176238950517093744891695513321974991917714957212542738171092864387696951296
def selected (j : Fin 39) : Tables.Index :=
  ⟨((selectedCode >>> (17*j.val)) % 2^17) % 86625, Nat.mod_lt _ (by decide)⟩

def columnCodeA : ℕ := 58928759356809140465438878694420750198566904116344216562526743645332849286201600588503156879225551661878841331656105170326725570768747931823299561351893916851997632419192080639101248606242414685337272510933143535306346503063042895838086684147409776114711268749770751098338326844668022709132872650108781481047059688040584562969451356748229165247432005140381769144253648330319108935294492823774665851735542543496622881073669110525083330681943275642555870276859
def columnCodeB : ℕ := 7582350608078061713182184005271402619883130139873869396380662982894656187524486488373497478705524697202873043542383255326948925174916557192322779088390718233751977337305823428520952361330763934676374134183375345456205721691848910307264533259390232217951519897708971438736753353024995977062237087734930750163997369951804399950745369826173261947767569392538306211077663602917259199971086175736484964196055529707513357974888124414845443535061196424167749567542
def columnCode (s : Fin 2) (j : Fin 39) : ℕ :=
  ((if s = 0 then columnCodeA else columnCodeB) >>> (39*j.val)) % 2^39

def rowEntry (r : Row) (k : Fin 5) : Tables.Index :=
  ⟨((Data.points r.val >>> (17*k.val)) % 2^17) % 86625, Nat.mod_lt _ (by decide)⟩

def rowMask (r : Row) : ℕ := Data.masks r.val

def rowStep (r : Row) : Fin 6 :=
  ⟨(Data.sources r.val % 8) % 6, Nat.mod_lt _ (by decide)⟩

def rowStart (r : Row) : Tables.Index :=
  ⟨(Data.sources r.val >>> 3) % 86625, Nat.mod_lt _ (by decide)⟩

def predecessor (i : Tables.Index) : Tables.Index :=
  ⟨Data.predecessors i.val % 86625, Nat.mod_lt _ (by decide)⟩

def lastLetter (i : Tables.Index) : Fin 2 :=
  ⟨Tables.wordCode i % 2, Nat.mod_lt _ (by decide)⟩

def conjugator (i : Fin 6) : List (Fin 2) :=
  match i.val with
  | 0 => []
  | 1 => [1, 0]
  | 2 => [1, 1, 0, 1, 0]
  | 3 => [1, 1, 1, 0, 1, 1, 0, 1, 0]
  | 4 => [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0]
  | _ => [1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0]

theorem selected_zero : selected 0 = 0 := by decide +kernel

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.NormBound
