module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Data

/-!
# Permutation rows for three normalizer words

These additional tables shorten the pointwise neighbor checks. Every row is
checked against its explicit word in `NeighborChecks`; no GAP premise is used.
Source: ATLAS J2G1-p100B0 and Aschbacher, *Sporadic Groups*, 47.5.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction.Data

def normalizerPacked (i : Fin 3) : Nat :=
  (if i.val < 1 then 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547 else (if i.val < 2 then 380971579606859674284443682087138016092856435793447077091078324745589510555305738045242523170186460379900955336290623015611210410173529760953629588281897742960492860447299343315261857204290575656665297589951570 else 2389306170907242034664580294558720531627340129675818244101420377668938867727749415659418207217607936760506000709558451643712597540364942848802729024858307689401577404500830592044830039108646861445325882577158332))

def normalizerInvPacked (i : Fin 3) : Nat :=
  (if i.val < 1 then 470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547 else (if i.val < 2 then 380971579606859674284443682087138016092856435793447077091078324745589510555305738045242523170186460379900955336290623015611210410173529760953629588281897742960492860447299343315261857204290575656665297589951570 else 845456857777785325315359708756247474455796337828594246325419877063701333385585537235310170315178409166199241196818608227227892953927055105032856967336029368704341533451329656459240047916904138725112131090415836))

def normalizerValue (s : Fin 3) (p : Fin 100) : Fin 100 :=
  ⟨(normalizerPacked s >>> (7 * p.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def normalizerInvValue (s : Fin 3) (p : Fin 100) : Fin 100 :=
  ⟨(normalizerInvPacked s >>> (7 * p.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def neighborFlip (i : Fin 36) : Bool :=
  (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then false else false) else (if i.val < 3 then false else true)) else (if i.val < 6 then (if i.val < 5 then false else true) else (if i.val < 7 then false else (if i.val < 8 then true else false)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then false else false) else (if i.val < 12 then false else false)) else (if i.val < 15 then (if i.val < 14 then false else false) else (if i.val < 16 then false else (if i.val < 17 then false else false))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then false else false) else (if i.val < 21 then false else false)) else (if i.val < 24 then (if i.val < 23 then false else false) else (if i.val < 25 then false else (if i.val < 26 then false else false)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then false else false) else (if i.val < 30 then false else false)) else (if i.val < 33 then (if i.val < 32 then false else false) else (if i.val < 34 then false else (if i.val < 35 then false else false))))))

end Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction.Data
