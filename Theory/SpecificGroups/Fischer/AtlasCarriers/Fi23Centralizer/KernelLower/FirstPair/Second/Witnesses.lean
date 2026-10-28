module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Word

/-!
# Schreier witnesses for the second suffix point

The representatives and factors are explicit words. Each code stores its length
and its leftmost letter in the least significant hexadecimal digit. Positive
factor letters come first, followed by inverse letters. These numerical data
assert no group identities; the actual transitions must be proved in Lean.
Source: retained ATLAS F23G1-p31671B0; application GLS3 Table 5.3u.
Reproduce with `FirstPair/source/generate.py --discover`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.Second

def representativeCode (b : Nat) : Nat × Nat :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          if b < 1 then
            (0, 0)
          else
            if b < 2 then
              (1, 0)
            else
              (1, 1)
        else
          if b < 4 then
            (1, 3)
          else
            if b < 5 then
              (2, 0)
            else
              (2, 1)
      else
        if b < 9 then
          if b < 7 then
            (2, 3)
          else
            if b < 8 then
              (2, 16)
            else
              (2, 48)
        else
          if b < 10 then
            (2, 49)
          else
            if b < 11 then
              (2, 51)
            else
              (3, 1)
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            (3, 3)
          else
            if b < 14 then
              (3, 16)
            else
              (3, 19)
        else
          if b < 16 then
            (3, 48)
          else
            if b < 17 then
              (3, 49)
            else
              (3, 51)
      else
        if b < 21 then
          if b < 19 then
            (3, 256)
          else
            if b < 20 then
              (3, 259)
            else
              (3, 769)
        else
          if b < 22 then
            (3, 784)
          else
            if b < 23 then
              (3, 787)
            else
              (3, 817)
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            (4, 16)
          else
            if b < 26 then
              (4, 48)
            else
              (4, 49)
        else
          if b < 28 then
            (4, 51)
          else
            if b < 29 then
              (4, 259)
            else
              (4, 304)
      else
        if b < 33 then
          if b < 31 then
            (4, 305)
          else
            if b < 32 then
              (4, 784)
            else
              (4, 787)
        else
          if b < 34 then
            (4, 817)
          else
            if b < 35 then
              (4, 4147)
            else
              (4, 12304)
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            (4, 12307)
          else
            if b < 38 then
              (4, 12593)
            else
              (4, 13072)
        else
          if b < 40 then
            (5, 259)
          else
            if b < 41 then
              (5, 4883)
            else
              (5, 12544)
      else
        if b < 45 then
          if b < 43 then
            (5, 12595)
          else
            if b < 44 then
              (5, 13072)
            else
              (5, 196912)
        else
          if b < 46 then
            (5, 201488)
          else
            if b < 47 then
              (6, 4147)
            else
              (6, 201520)

def pointBlocks (_b : Nat) : Nat :=
  184320674339535299446550540516086575649612828875462415894399076670871338893945382616906605535339999310663785299030862591824414518050767523662973037181761962811972908934306655342337682758615997801878846664315307065390

def point (r : Fin 48) : Fin 31671 :=
  Fin.ofNat 31671 ((pointBlocks (r.val / 256) >>> (15 * (r.val % 256))) % 32768)

def forward0Blocks (_b : Nat) : Nat :=
  775075518329566955301203956112992236311119558794313469704426460373109676403988854078513875601695190907650935555073

def backward0Blocks (_b : Nat) : Nat :=
  6489129172071628446797868957465741727703111409128982010211096828462993850514532656634105832375701619905676599558148

def factorCode0 (b : Nat) : Nat × Nat :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          (0, 0)
        else
          if b < 4 then
            (0, 0)
          else
            if b < 5 then
              (7, 213795566)
            else
              (0, 0)
      else
        if b < 9 then
          if b < 7 then
            (0, 0)
          else
            if b < 8 then
              (0, 0)
            else
              (7, 218055406)
        else
          if b < 10 then
            (0, 0)
          else
            if b < 11 then
              (5, 981709)
            else
              (0, 0)
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            (0, 0)
          else
            if b < 14 then
              (5, 830841)
            else
              (0, 0)
        else
          if b < 16 then
            (7, 218055406)
          else
            if b < 17 then
              (0, 0)
            else
              (7, 267234249)
      else
        if b < 21 then
          if b < 19 then
            (7, 149837038)
          else
            if b < 20 then
              (8, 3903573737)
            else
              (0, 0)
        else
          if b < 22 then
            (7, 238960878)
          else
            if b < 23 then
              (5, 981709)
            else
              (0, 0)
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            (9, 67349923433)
          else
            if b < 26 then
              (4, 35801)
            else
              (7, 250588377)
        else
          if b < 28 then
            (7, 234104425)
          else
            if b < 29 then
              (5, 978754)
            else
              (4, 44134)
      else
        if b < 33 then
          if b < 31 then
            (5, 719868)
          else
            if b < 32 then
              (0, 0)
            else
              (6, 7291118)
        else
          if b < 34 then
            (0, 0)
          else
            if b < 35 then
              (7, 267041894)
            else
              (6, 6633065)
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            (0, 0)
          else
            if b < 38 then
              (0, 0)
            else
              (6, 13610201)
        else
          if b < 40 then
            (9, 59833058921)
          else
            if b < 41 then
              (7, 23497853)
            else
              (5, 984681)
      else
        if b < 45 then
          if b < 43 then
            (0, 0)
          else
            if b < 44 then
              (3, 2798)
            else
              (6, 11001577)
        else
          if b < 46 then
            (6, 15615525)
          else
            if b < 47 then
              (5, 822268)
            else
              (7, 264945390)

def treeEdge0 (b : Nat) : Bool :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          true
        else
          if b < 4 then
            true
          else
            if b < 5 then
              false
            else
              true
      else
        if b < 9 then
          if b < 7 then
            true
          else
            if b < 8 then
              true
            else
              false
        else
          if b < 10 then
            true
          else
            if b < 11 then
              false
            else
              true
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            true
          else
            if b < 14 then
              false
            else
              true
        else
          if b < 16 then
            false
          else
            if b < 17 then
              true
            else
              false
      else
        if b < 21 then
          if b < 19 then
            false
          else
            if b < 20 then
              false
            else
              true
        else
          if b < 22 then
            false
          else
            if b < 23 then
              false
            else
              true
  else
    if b < 36 then
      if b < 30 then
        false
      else
        if b < 33 then
          if b < 31 then
            false
          else
            if b < 32 then
              true
            else
              false
        else
          if b < 34 then
            true
          else
            false
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            true
          else
            if b < 38 then
              true
            else
              false
        else
          false
      else
        if b < 45 then
          if b < 43 then
            true
          else
            false
        else
          false

def forward1Blocks (_b : Nat) : Nat :=
  7261717556565542118334205224962980038510631554558321523603729543301924554265585332473722382101286074953778065310978

def backward1Blocks (_b : Nat) : Nat :=
  7261717556565542118334205224962980038510631554558321523603729543301924554265585332473722382101286074953778065310978

def factorCode1 (b : Nat) : Nat × Nat :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        (0, 0)
      else
        if b < 9 then
          if b < 7 then
            (0, 0)
          else
            if b < 8 then
              (9, 64033183337)
            else
              (0, 0)
        else
          (0, 0)
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            (0, 0)
          else
            if b < 14 then
              (2, 137)
            else
              (0, 0)
        else
          if b < 16 then
            (3, 3939)
          else
            (0, 0)
      else
        if b < 21 then
          if b < 19 then
            (3, 3047)
          else
            if b < 20 then
              (6, 9239654)
            else
              (0, 0)
        else
          if b < 22 then
            (6, 15599209)
          else
            (0, 0)
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            (6, 15248233)
          else
            if b < 26 then
              (8, 3739496169)
            else
              (0, 0)
        else
          if b < 28 then
            (6, 15155438)
          else
            if b < 29 then
              (7, 205457001)
            else
              (6, 6704873)
      else
        if b < 33 then
          if b < 31 then
            (0, 0)
          else
            if b < 32 then
              (5, 568537)
            else
              (8, 4210378345)
        else
          if b < 34 then
            (0, 0)
          else
            if b < 35 then
              (2, 201)
            else
              (6, 9239654)
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            (6, 15257582)
          else
            if b < 38 then
              (0, 0)
            else
              (6, 15615593)
        else
          if b < 40 then
            (5, 579566)
          else
            if b < 41 then
              (3, 3719)
            else
              (3, 3846)
      else
        if b < 45 then
          if b < 43 then
            (4, 14137)
          else
            if b < 44 then
              (4, 35513)
            else
              (2, 137)
        else
          if b < 46 then
            (4, 30313)
          else
            if b < 47 then
              (6, 12473070)
            else
              (7, 248184678)

def treeEdge1 (b : Nat) : Bool :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          if b < 1 then
            true
          else
            if b < 2 then
              true
            else
              false
        else
          if b < 4 then
            true
          else
            if b < 5 then
              true
            else
              false
      else
        if b < 9 then
          if b < 7 then
            true
          else
            if b < 8 then
              false
            else
              true
        else
          if b < 10 then
            false
          else
            if b < 11 then
              true
            else
              false
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            true
          else
            if b < 14 then
              false
            else
              true
        else
          if b < 16 then
            false
          else
            if b < 17 then
              false
            else
              true
      else
        if b < 21 then
          false
        else
          if b < 22 then
            false
          else
            if b < 23 then
              true
            else
              false
  else
    false

def forward2Blocks (_b : Nat) : Nat :=
  7261717556565542118334205224962980038510631554558321523603729543301924554265585332473722382101286074953778065310978

def backward2Blocks (_b : Nat) : Nat :=
  7261717556565542118334205224962980038510631554558321523603729543301924554265585332473722382101286074953778065310978

def factorCode2 (b : Nat) : Nat × Nat :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        (1, 9)
      else
        if b < 9 then
          if b < 7 then
            (1, 9)
          else
            if b < 8 then
              (8, 4002073958)
            else
              (1, 9)
        else
          (1, 9)
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            (1, 9)
          else
            if b < 14 then
              (1, 8)
            else
              (1, 9)
        else
          if b < 16 then
            (4, 63033)
          else
            (1, 9)
      else
        if b < 21 then
          if b < 19 then
            (4, 48761)
          else
            if b < 20 then
              (7, 147834473)
            else
              (1, 9)
        else
          if b < 22 then
            (5, 974950)
          else
            (1, 9)
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            (5, 953014)
          else
            if b < 26 then
              (7, 233718510)
            else
              (1, 9)
        else
          if b < 28 then
            (7, 242487017)
          else
            if b < 29 then
              (6, 12841062)
            else
              (5, 419054)
      else
        if b < 33 then
          if b < 31 then
            (1, 9)
          else
            if b < 32 then
              (4, 35533)
            else
              (7, 263148646)
        else
          if b < 34 then
            (1, 9)
          else
            if b < 35 then
              (1, 12)
            else
              (7, 147834473)
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            (7, 244121321)
          else
            if b < 38 then
              (1, 9)
            else
              (5, 975974)
        else
          if b < 40 then
            (6, 9273065)
          else
            if b < 41 then
              (4, 7815)
            else
              (4, 61545)
      else
        if b < 45 then
          if b < 43 then
            (3, 883)
          else
            if b < 44 then
              (3, 2219)
            else
              (1, 8)
        else
          if b < 46 then
            (3, 1894)
          else
            if b < 47 then
              (7, 199569129)
            else
              (8, 3970954857)

def treeEdge2 (_b : Nat) : Bool :=
  false

def forward3Blocks (_b : Nat) : Nat :=
  5863235629404286120673900458399802576495698680500637910349831479033821162237095446052708037153887127351029244495363

def backward3Blocks (_b : Nat) : Nat :=
  6795761956012259271018298321898863992213601388544460540912338205451914246366006382992358688899928198418067152310538

def factorCode3 (b : Nat) : Nat × Nat :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          if b < 1 then
            (0, 0)
          else
            if b < 2 then
              (0, 0)
            else
              (6, 1625461)
        else
          (0, 0)
      else
        if b < 9 then
          if b < 7 then
            (0, 0)
          else
            if b < 8 then
              (0, 0)
            else
              (5, 981709)
        else
          if b < 10 then
            (0, 0)
          else
            if b < 11 then
              (3, 4095)
            else
              (6, 16305902)
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            (0, 0)
          else
            if b < 14 then
              (0, 0)
            else
              (5, 841321)
        else
          if b < 16 then
            (6, 7291118)
          else
            if b < 17 then
              (0, 0)
            else
              (3, 4095)
      else
        if b < 21 then
          if b < 19 then
            (8, 3727573094)
          else
            (0, 0)
        else
          if b < 22 then
            (5, 981709)
          else
            if b < 23 then
              (6, 1625461)
            else
              (3, 1380)
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            (0, 0)
          else
            if b < 26 then
              (7, 234104425)
            else
              (7, 263189742)
        else
          if b < 28 then
            (3, 4095)
          else
            if b < 29 then
              (6, 15257337)
            else
              (5, 575081)
      else
        if b < 33 then
          if b < 31 then
            (0, 0)
          else
            if b < 32 then
              (3, 3286)
            else
              (0, 0)
        else
          if b < 34 then
            (5, 841321)
          else
            if b < 35 then
              (3, 4095)
            else
              (3, 3810)
    else
      if b < 42 then
        if b < 39 then
          if b < 37 then
            (5, 1005161)
          else
            if b < 38 then
              (6, 1625461)
            else
              (7, 218055406)
        else
          if b < 40 then
            (0, 0)
          else
            if b < 41 then
              (4, 14137)
            else
              (4, 24678)
      else
        if b < 45 then
          if b < 43 then
            (3, 4095)
          else
            if b < 44 then
              (6, 15257337)
            else
              (6, 7605993)
        else
          if b < 46 then
            (3, 2262)
          else
            if b < 47 then
              (3, 4095)
            else
              (4, 35529)

def treeEdge3 (b : Nat) : Bool :=
  if b < 24 then
    if b < 12 then
      if b < 6 then
        if b < 3 then
          if b < 1 then
            true
          else
            if b < 2 then
              true
            else
              false
        else
          true
      else
        if b < 9 then
          if b < 7 then
            true
          else
            if b < 8 then
              true
            else
              false
        else
          if b < 10 then
            true
          else
            false
    else
      if b < 18 then
        if b < 15 then
          if b < 13 then
            true
          else
            if b < 14 then
              true
            else
              false
        else
          if b < 16 then
            false
          else
            if b < 17 then
              true
            else
              false
      else
        if b < 21 then
          if b < 19 then
            false
          else
            true
        else
          false
  else
    if b < 36 then
      if b < 30 then
        if b < 27 then
          if b < 25 then
            true
          else
            false
        else
          false
      else
        if b < 33 then
          if b < 31 then
            true
          else
            if b < 32 then
              false
            else
              true
        else
          false
    else
      if b < 42 then
        if b < 39 then
          false
        else
          if b < 40 then
            true
          else
            false
      else
        false

def forwardBlocks : Fin 4 → Nat → Nat
  | 0 => forward0Blocks
  | 1 => forward1Blocks
  | 2 => forward2Blocks
  | 3 => forward3Blocks

def transitionForward (a : Fin 4) (r : Fin 48) : Fin 48 :=
  Fin.ofNat 48 (((forwardBlocks a) (r.val / 256) >>> (8 * (r.val % 256))) % 256)

def backwardBlocks : Fin 4 → Nat → Nat
  | 0 => backward0Blocks
  | 1 => backward1Blocks
  | 2 => backward2Blocks
  | 3 => backward3Blocks

def transitionBackward (a : Fin 4) (r : Fin 48) : Fin 48 :=
  Fin.ofNat 48 (((backwardBlocks a) (r.val / 256) >>> (8 * (r.val % 256))) % 256)

def factorCode : Fin 4 → Nat → Nat × Nat
  | 0 => factorCode0
  | 1 => factorCode1
  | 2 => factorCode2
  | 3 => factorCode3

def treeEdge : Fin 4 → Nat → Bool
  | 0 => treeEdge0
  | 1 => treeEdge1
  | 2 => treeEdge2
  | 3 => treeEdge3

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.Second
